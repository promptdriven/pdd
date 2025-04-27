import click
import logging
import os
import csv
from pathlib import Path
from typing import Optional, Tuple, Dict, Any, List

# Use relative imports for internal modules
from .construct_paths import construct_paths
from .change import change as change_func
from .process_csv_change import process_csv_change
from .get_extension import get_extension
from . import DEFAULT_STRENGTH  # Assuming DEFAULT_STRENGTH is defined in __init__.py

# Import Rich for pretty printing
from rich import print as rprint
from rich.panel import Panel

# Set up logging
logger = logging.getLogger(__name__)
# Ensure logger propagates messages to the root logger configured in the main CLI entry point
# If not configured elsewhere, uncomment the following lines:
# logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
# logger.setLevel(logging.DEBUG)


def change_main(
    ctx: click.Context,
    change_prompt_file: str,
    input_code: str,
    input_prompt_file: Optional[str],
    output: Optional[str],
    use_csv: bool,
) -> Tuple[str, float, str]:
    """
    Handles the core logic for the 'change' command.

    Modifies an input prompt file based on instructions in a change prompt,
    using the corresponding code file as context. Supports single file changes
    and batch changes via CSV.

    Args:
        ctx: The Click context object.
        change_prompt_file: Path to the change prompt file (or CSV in CSV mode).
        input_code: Path to the input code file (or directory in CSV mode).
        input_prompt_file: Path to the input prompt file (required in non-CSV mode).
        output: Optional output path (file or directory).
        use_csv: Flag indicating whether to use CSV mode.

    Returns:
        A tuple containing:
        - str: Modified prompt content (non-CSV), status message (CSV), or error message.
        - float: Total cost of the operation.
        - str: Name of the model used.
    """
    logger.debug(f"Starting change_main with use_csv={use_csv}")
    logger.debug(f"  change_prompt_file: {change_prompt_file}")
    logger.debug(f"  input_code: {input_code}")
    logger.debug(f"  input_prompt_file: {input_prompt_file}")
    logger.debug(f"  output: {output}")

    # Retrieve global options from context
    force: bool = ctx.obj.get("force", False)
    quiet: bool = ctx.obj.get("quiet", False)
    strength: float = ctx.obj.get("strength", DEFAULT_STRENGTH)
    temperature: float = ctx.obj.get("temperature", 0.0)
    # Default budget to 5.0 if not specified - needed for process_csv_change
    budget: float = ctx.obj.get("budget", 5.0) 
    # --- Get language and extension from context --- 
    # These are crucial for knowing the target code file types, especially in CSV mode
    target_language: str = ctx.obj.get("language", "") # Get from context
    target_extension: Optional[str] = ctx.obj.get("extension", None)

    result_message: str = "An unexpected error occurred."
    total_cost: float = 0.0
    model_name: str = ""
    success: bool = False
    modified_prompts_list: List[Dict[str, str]] = [] # For CSV mode

    try:
        # --- 1. Argument Validation ---
        if not change_prompt_file or not input_code:
            msg = "[bold red]Error:[/bold red] Both --change-prompt-file and --input-code arguments are required."
            if not quiet: rprint(msg)
            logger.error(msg)
            return msg, 0.0, ""

        if use_csv:
            if input_prompt_file:
                msg = "[bold red]Error:[/bold red] --input-prompt-file should not be provided when using --csv mode."
                if not quiet: rprint(msg)
                logger.error(msg)
                return msg, 0.0, ""
            if not os.path.isdir(input_code):
                msg = f"[bold red]Error:[/bold red] In CSV mode, --input-code ('{input_code}') must be a valid directory."
                if not quiet: rprint(msg)
                logger.error(msg)
                return msg, 0.0, ""
            if not change_prompt_file.lower().endswith(".csv"):
                 logger.warning(f"Input change file '{change_prompt_file}' does not end with .csv. Assuming it's a CSV.")
            # Further CSV validation happens within process_csv_change or just before calling it

        else: # Non-CSV mode
            if not input_prompt_file:
                msg = "[bold red]Error:[/bold red] --input-prompt-file is required when not using --csv mode."
                if not quiet: rprint(msg)
                logger.error(msg)
                return msg, 0.0, ""
            if os.path.isdir(input_code):
                 msg = f"[bold red]Error:[/bold red] In non-CSV mode, --input-code ('{input_code}') must be a file path, not a directory."
                 if not quiet: rprint(msg)
                 logger.error(msg)
                 return msg, 0.0, ""


        # --- 2. Construct Paths and Read Inputs (where applicable) ---
        input_file_paths: Dict[str, str] = {}
        command_options: Dict[str, Any] = {"output": output} if output else {}

        if use_csv:
            # Only the CSV file needs to be read by construct_paths initially
            input_file_paths["change_prompt_file"] = change_prompt_file
            # input_code is a directory, handled later
        else:
            # All inputs are files in non-CSV mode
            input_file_paths["change_prompt_file"] = change_prompt_file
            input_file_paths["input_code"] = input_code
            input_file_paths["input_prompt_file"] = input_prompt_file

        logger.debug(f"Calling construct_paths with inputs: {input_file_paths}")
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=force,
            quiet=quiet,
            command="change",
            command_options=command_options,
        )
        logger.debug(f"construct_paths returned:")
        logger.debug(f"  input_strings keys: {list(input_strings.keys())}")
        logger.debug(f"  output_file_paths: {output_file_paths}")
        logger.debug(f"  language: {language}") # Language might be inferred or needed for defaults

        # --- 3. Perform Prompt Modification ---
        if use_csv:
            logger.info("Running in CSV mode.")
            # Validate CSV header before calling process_csv_change
            try:
                with open(change_prompt_file, 'r', newline='', encoding='utf-8') as csvfile:
                    reader = csv.reader(csvfile)
                    header = next(reader)
                    if "prompt_name" not in header or "change_instructions" not in header:
                        msg = f"[bold red]Error:[/bold red] CSV file '{change_prompt_file}' must contain 'prompt_name' and 'change_instructions' columns."
                        if not quiet: rprint(msg)
                        logger.error(msg)
                        return msg, 0.0, ""
            except FileNotFoundError:
                msg = f"[bold red]Error:[/bold red] CSV file not found: {change_prompt_file}"
                if not quiet: rprint(msg)
                logger.error(msg)
                return msg, 0.0, ""
            except Exception as e:
                msg = f"[bold red]Error:[/bold red] Failed to read or validate CSV header: {e}"
                if not quiet: rprint(msg)
                logger.error(f"CSV header validation error: {e}", exc_info=True)
                return msg, 0.0, ""

            # Determine language and extension for process_csv_change
            # Use the target_language from the context if available, otherwise fallback (though fallback might be wrong)
            csv_target_language = target_language or language or "python" # Prioritize context language
            try:
                # If target_extension was provided in context, use it directly
                if target_extension:
                    extension = target_extension
                    logger.debug(f"Using extension '{extension}' from context for CSV processing.")
                else:
                    # Otherwise, derive from the determined language
                    extension = get_extension(csv_target_language)
                    logger.debug(f"Derived language '{csv_target_language}' and extension '{extension}' for CSV processing.")
            except ValueError as e:
                 msg = f"[bold red]Error:[/bold red] Could not determine file extension for language '{csv_target_language}': {e}"
                 if not quiet: rprint(msg)
                 logger.error(msg)
                 return msg, 0.0, ""


            success, modified_prompts_list, total_cost, model_name = process_csv_change(
                csv_file=change_prompt_file,
                strength=strength,
                temperature=temperature,
                code_directory=input_code, # Pass the directory path
                language=csv_target_language,
                extension=extension,
                budget=budget,
            )

            if success:
                result_message = f"Successfully processed {len(modified_prompts_list)} prompts from CSV."
                logger.info(result_message)
            else:
                result_message = f"[bold red]Error:[/bold red] Failed to process prompts from CSV. Check logs for details."
                if not quiet: rprint(result_message)
                logger.error("process_csv_change reported failure.")
                # Cost and model might still be partially accumulated
                return result_message, total_cost, model_name

        else: # Non-CSV mode
            logger.info("Running in single-file mode.")
            change_prompt_content = input_strings.get("change_prompt_file")
            input_code_content = input_strings.get("input_code")
            input_prompt_content = input_strings.get("input_prompt_file")

            if not all([change_prompt_content, input_code_content, input_prompt_content]):
                 missing = [k for k, v in {"change_prompt_file": change_prompt_content,
                                           "input_code": input_code_content,
                                           "input_prompt_file": input_prompt_content}.items() if not v]
                 msg = f"[bold red]Error:[/bold red] Failed to read content for required input files: {', '.join(missing)}"
                 if not quiet: rprint(msg)
                 logger.error(msg)
                 return msg, 0.0, ""

            modified_prompt, total_cost, model_name = change_func(
                input_prompt=input_prompt_content,
                input_code=input_code_content,
                change_prompt=change_prompt_content,
                strength=strength,
                temperature=temperature,
            )
            result_message = modified_prompt # Store the content for saving
            success = True # Assume success if no exception
            logger.info("Single prompt change successful.")


        # --- 4. Save Results ---
        if success:
            output_path_obj: Optional[Path] = None
            if output:
                output_path_obj = Path(output).resolve()
                logger.debug(f"User specified output path: {output_path_obj}")
            elif not use_csv and "output_prompt_file" in output_file_paths:
                 # Use default path from construct_paths for single file mode if no --output
                 output_path_obj = Path(output_file_paths["output_prompt_file"]).resolve()
                 logger.debug(f"Using default output path from construct_paths: {output_path_obj}")


            if use_csv:
                output_is_csv = output_path_obj and output_path_obj.suffix.lower() == ".csv"

                if output_is_csv:
                    # Save all results to a single CSV file
                    logger.info(f"Saving batch results to CSV: {output_path_obj}")
                    try:
                        output_path_obj.parent.mkdir(parents=True, exist_ok=True)
                        with open(output_path_obj, 'w', newline='', encoding='utf-8') as outfile:
                            fieldnames = ['prompt_name', 'modified_prompt']
                            writer = csv.DictWriter(outfile, fieldnames=fieldnames)
                            writer.writeheader()
                            # Map 'file_name' from process_csv_change output to 'prompt_name'
                            for item in modified_prompts_list:
                                writer.writerow({
                                    'prompt_name': item.get('file_name', 'unknown_prompt'),
                                    'modified_prompt': item.get('modified_prompt', '')
                                })
                        result_message += f" Results saved to {output_path_obj}"
                        if not quiet: rprint(f"[green]Results saved to:[/green] {output_path_obj}")
                    except IOError as e:
                        msg = f"[bold red]Error:[/bold red] Failed to write output CSV '{output_path_obj}': {e}"
                        if not quiet: rprint(msg)
                        logger.error(msg, exc_info=True)
                        return msg, total_cost, model_name # Return error after processing
                    except Exception as e:
                        msg = f"[bold red]Error:[/bold red] Unexpected error writing output CSV '{output_path_obj}': {e}"
                        if not quiet: rprint(msg)
                        logger.error(msg, exc_info=True)
                        return msg, total_cost, model_name

                else:
                    # Save each modified prompt to an individual file
                    output_dir = output_path_obj if output_path_obj and output_path_obj.is_dir() else Path.cwd()
                    if output_path_obj and not output_path_obj.is_dir():
                         # If user specified a non-csv file path, treat its parent as the dir
                         output_dir = output_path_obj.parent
                         logger.warning(f"Output path '{output_path_obj}' is not a directory or CSV. Saving individual files to parent directory: {output_dir}")

                    logger.info(f"Saving individual modified prompts to directory: {output_dir}")
                    output_dir.mkdir(parents=True, exist_ok=True)
                    saved_files_count = 0
                    for item in modified_prompts_list:
                        original_prompt_path = Path(item.get('file_name', ''))
                        modified_content = item.get('modified_prompt', '')
                        if not original_prompt_path or not modified_content:
                            logger.warning(f"Skipping save for item due to missing data: {item}")
                            continue

                        # Use original filename instead of adding a modified_ prefix
                        output_filename = os.path.basename(original_prompt_path)
                        individual_output_path = output_dir / output_filename

                        if not force and individual_output_path.exists():
                            logger.warning(f"Output file exists, skipping: {individual_output_path}. Use --force to overwrite.")
                            if not quiet: rprint(f"[yellow]Skipping existing file:[/yellow] {individual_output_path}")
                            continue

                        try:
                            individual_output_path.write_text(modified_content, encoding='utf-8')
                            logger.debug(f"Saved modified prompt to: {individual_output_path}")
                            saved_files_count += 1
                        except IOError as e:
                            msg = f"[bold red]Error:[/bold red] Failed to write output file '{individual_output_path}': {e}"
                            if not quiet: rprint(msg)
                            logger.error(msg, exc_info=True)
                            # Continue saving others, but report error at the end? Or stop? Let's continue for now.
                        except Exception as e:
                             msg = f"[bold red]Error:[/bold red] Unexpected error writing output file '{individual_output_path}': {e}"
                             if not quiet: rprint(msg)
                             logger.error(msg, exc_info=True)

                    result_message += f" {saved_files_count} modified prompts saved individually in {output_dir}"
                    if not quiet: rprint(f"[green]Saved {saved_files_count} modified prompts to:[/green] {output_dir}")


            else: # Non-CSV mode saving
                if not output_path_obj:
                     msg = "[bold red]Error:[/bold red] Could not determine output path for modified prompt."
                     if not quiet: rprint(msg)
                     logger.error(msg)
                     return msg, total_cost, model_name

                logger.info(f"Saving single modified prompt to: {output_path_obj}")
                try:
                    output_path_obj.parent.mkdir(parents=True, exist_ok=True)
                    output_path_obj.write_text(result_message, encoding='utf-8') # result_message holds the content here
                    if not quiet:
                        rprint(f"[green]Modified prompt saved to:[/green] {output_path_obj}")
                        rprint(Panel(result_message, title="Modified Prompt Content", expand=False))
                    # Update result_message for return value to be a status, not the full content
                    result_message = f"Modified prompt saved to {output_path_obj}"

                except IOError as e:
                    msg = f"[bold red]Error:[/bold red] Failed to write output file '{output_path_obj}': {e}"
                    if not quiet: rprint(msg)
                    logger.error(msg, exc_info=True)
                    return msg, total_cost, model_name # Return error after processing
                except Exception as e:
                    msg = f"[bold red]Error:[/bold red] Unexpected error writing output file '{output_path_obj}': {e}"
                    if not quiet: rprint(msg)
                    logger.error(msg, exc_info=True)
                    return msg, total_cost, model_name

        # --- 5. Final User Feedback ---
        if not quiet and success:
            rprint(f"[cyan]Model Used:[/cyan] {model_name}")
            rprint(f"[cyan]Total Cost:[/cyan] ${total_cost:.6f}")

    except FileNotFoundError as e:
        msg = f"[bold red]Error:[/bold red] Input file not found: {e}"
        if not quiet: rprint(msg)
        logger.error(msg, exc_info=True)
        return msg, 0.0, ""
    except NotADirectoryError as e:
         msg = f"[bold red]Error:[/bold red] Expected a directory but found a file, or vice versa: {e}"
         if not quiet: rprint(msg)
         logger.error(msg, exc_info=True)
         return msg, 0.0, ""
    except Exception as e:
        msg = f"[bold red]An unexpected error occurred during the 'change' operation:[/bold red] {e}"
        if not quiet: rprint(msg)
        logger.error("Unexpected error in change_main", exc_info=True)
        # Use the initialized default error message for return
        return result_message, total_cost, model_name # Return potentially partial cost/model

    logger.debug("change_main finished.")
    return result_message, total_cost, model_name
