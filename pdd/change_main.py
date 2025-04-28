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

    result_message: str = ""
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

            # Validate CSV header and columns early - before construct_paths
            try:
                with open(change_prompt_file, 'r', newline='', encoding='utf-8') as csvfile:
                    reader = csv.DictReader(csvfile)
                    if not reader.fieldnames or "prompt_name" not in reader.fieldnames or "change_instructions" not in reader.fieldnames:
                        msg = "CSV file must contain 'prompt_name' and 'change_instructions' columns."
                        if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                        logger.error(msg)
                        return msg, 0.0, ""
                    logger.debug(f"CSV validated. Columns: {reader.fieldnames}")
            except FileNotFoundError:
                msg = f"CSV file not found: {change_prompt_file}"
                if not quiet: rprint(f"[bold red]Error:[/bold red] {msg}")
                logger.error(msg)
                return msg, 0.0, ""
            except Exception as e:
                msg = f"Failed to read or validate CSV: {e}"
                if not quiet: rprint(f"[bold red]Error:[/bold red] {msg}")
                logger.error(f"CSV validation error: {e}", exc_info=True)
                return msg, 0.0, ""
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
        try:
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
        except Exception as e:
            msg = f"Error constructing paths: {str(e)}"
            if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
            logger.error(msg, exc_info=True)
            return msg, 0.0, ""

        # --- 3. Perform Prompt Modification --- 
        if use_csv:
            logger.info("Running in CSV mode.")
            # Process each row in the CSV
            try:
                with open(change_prompt_file, 'r', newline='', encoding='utf-8') as csvfile:
                    reader = csv.DictReader(csvfile)
                    # CSV already validated above
                    row_number = 0
                    for row in reader:
                        row_number += 1
                        logger.debug(f"Processing row {row_number}")
                        prompt_name = row["prompt_name"]
                        change_instructions = row["change_instructions"]
                        try:
                            prompt_path = Path(prompt_name)
                            if not prompt_path.is_file():
                                prompt_path = Path.cwd() / prompt_name
                                if not prompt_path.is_file():
                                    logger.warning(f"Prompt file not found: {prompt_name}. Skipping.")
                                    if not quiet: rprint(f"[yellow]Prompt file not found:[/yellow] {prompt_name}")
                                    continue
                            input_prompt = prompt_path.read_text(encoding='utf-8')
                            code_file_name = Path(prompt_name).stem
                            lang_suffix = None
                            if '_' in code_file_name:
                                code_file_name_split = code_file_name.rsplit('_', 1)
                                if len(code_file_name_split) == 2:
                                    code_file_name, lang_suffix = code_file_name_split
                            # Determine extension
                            if target_extension:
                                ext = target_extension
                            else:
                                try:
                                    ext = get_extension(target_language or language or 'python')
                                except ValueError:
                                    ext = '.txt' # Fallback
                            code_file_path = Path(input_code) / f"{code_file_name}{ext}"
                            if not code_file_path.is_file():
                                logger.warning(f"Code file not found: {code_file_path}. Skipping.")
                                if not quiet: rprint(f"[yellow]Code file not found:[/yellow] {code_file_path}")
                                continue
                            input_code_content = code_file_path.read_text(encoding='utf-8')
                            logger.debug(f"Calling change_func for row {row_number}")
                            try:
                                modified_prompt, cost, row_model_name = change_func(
                                    input_prompt=input_prompt,
                                    input_code=input_code_content,
                                    change_prompt=change_instructions,
                                    strength=strength,
                                    temperature=temperature,
                                    verbose=ctx.obj.get("verbose", False),
                                )
                                total_cost += cost
                                if not model_name and row_model_name: # Store first successful model name
                                    model_name = row_model_name
                                logger.debug(f"change_func completed. Cost: {cost}")
                                modified_prompts_list.append({
                                    'file_name': prompt_name,
                                    'modified_prompt': modified_prompt
                                })
                                logger.info(f"Row {row_number} processed successfully.")
                            except Exception as e:
                                logger.error(f"Error processing row {row_number}: {e}", exc_info=True)
                                if not quiet: rprint(f"[red]Error processing row {row_number} ('{prompt_name}'): {str(e)}. Skipping.[/red]")
                                continue
                        except Exception as e:
                            logger.error(f"Error preparing files for row {row_number}: {e}", exc_info=True)
                            if not quiet: rprint(f"[red]Error preparing files for row {row_number} ('{prompt_name}'): {str(e)}. Skipping.[/red]")
                            continue
                    success = True # CSV processing completed, even if no rows were successful or list is empty
                    # Set result message for CSV mode regardless of success of individual rows
                    result_message = "Multiple prompts have been updated."
            except FileNotFoundError: # Should not happen due to earlier check, but keep for safety
                msg = f"CSV file not found: {change_prompt_file}"
                if not quiet: rprint(f"[bold red]Error:[/bold red] {msg}")
                logger.error(msg)
                return msg, 0.0, ""
            except Exception as e:
                msg = f"Failed to read or process CSV content: {e}"
                if not quiet: rprint(f"[bold red]Error:[/bold red] {msg}")
                logger.error(f"CSV processing error: {e}", exc_info=True)
                return msg, 0.0, ""
        else:
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
            try:
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
            except Exception as e:
                msg = f"Error during prompt modification: {str(e)}"
                if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                logger.error(msg, exc_info=True)
                return msg, 0.0, ""

        # --- 4. Save Results --- 
        if success:
            output_path_obj: Optional[Path] = None
            if output:
                output_path_obj = Path(output).resolve()
                logger.debug(f"User specified output path: {output_path_obj}")
            elif not use_csv and "output_prompt_file" in output_file_paths:
                 output_path_obj = Path(output_file_paths["output_prompt_file"]).resolve()
                 logger.debug(f"Using default output path from construct_paths: {output_path_obj}")

            if use_csv:
                # Handle potential directory paths ending with a separator
                if output_path_obj and str(output_path_obj).endswith((os.sep, "/", "\\")):
                    logger.debug(f"Output path has trailing separator: {output_path_obj}")
                    output_path_obj = Path(os.path.normpath(str(output_path_obj)))
                    logger.debug(f"Normalized output path: {output_path_obj}")
                
                output_is_csv = output_path_obj and output_path_obj.suffix.lower() == ".csv"
                if output_is_csv:
                    logger.info(f"Saving batch results to CSV: {output_path_obj}")
                    try:
                        output_path_obj.parent.mkdir(parents=True, exist_ok=True)
                        with open(output_path_obj, 'w', newline='', encoding='utf-8') as outfile:
                            fieldnames = ['file_name', 'modified_prompt']
                            writer = csv.DictWriter(outfile, fieldnames=fieldnames)
                            writer.writeheader()
                            for item in modified_prompts_list:
                                writer.writerow({
                                    'file_name': item.get('file_name', 'unknown_prompt'),
                                    'modified_prompt': item.get('modified_prompt', '')
                                })
                        logger.info("Results saved to CSV successfully")
                        if not quiet: rprint(f"[bold]Results saved to CSV:[/bold] {output_path_obj}")
                    except IOError as e:
                        msg = f"Failed to write output CSV '{output_path_obj}': {e}"
                        if not quiet: rprint(f"[bold red]Error:[/bold red] {msg}")
                        logger.error(msg, exc_info=True)
                        # Still return the main CSV message, but with cost/model from successful rows if any
                        return result_message, total_cost, model_name 
                    except Exception as e:
                        msg = f"Unexpected error writing output CSV '{output_path_obj}': {e}"
                        if not quiet: rprint(f"[bold red]Error:[/bold red] {msg}")
                        logger.error(msg, exc_info=True)
                        return result_message, total_cost, model_name
                else:
                    # Save each modified prompt to an individual file
                    output_dir = None
                    if output_path_obj:
                        # Check if the normalized path IS a directory (even if it needs creation)
                        # Using suffix check is fragile, rely on os.path.isdir or expected behavior
                        # If it *looks* like a directory (no common file suffix or ends in / before norm), treat as dir.
                        # Safest: Assume dir if it doesn't end with a typical file extension or if explicitly created as one.
                        # Let's refine the logic: if output path exists AND is a file, error unless force? No, spec is save *in* dir.
                        # If output path is specified, treat it as the target directory.
                        output_dir = output_path_obj
                        logger.debug(f"Output target is directory: {output_dir}")
                    else:
                        output_dir = Path.cwd()
                        logger.debug(f"Using current working directory as output: {output_dir}")
                    
                    # Ensure the directory exists
                    try:
                        if not output_dir.exists():
                            logger.debug(f"Creating output directory: {output_dir}")
                        os.makedirs(output_dir, exist_ok=True) # exist_ok=True handles pre-existing dirs
                    except OSError as e:
                         msg = f"Failed to create output directory '{output_dir}': {e}"
                         if not quiet: rprint(f"[bold red]Error:[/bold red] {msg}")
                         logger.error(msg, exc_info=True)
                         return result_message, total_cost, model_name

                    logger.info(f"Saving individual files to directory: {output_dir}")
                    saved_files_count = 0
                    for item in modified_prompts_list:
                        original_prompt_path = item.get('file_name', '')
                        modified_content = item.get('modified_prompt', '')
                        if not original_prompt_path or not modified_content:
                            logger.warning(f"Skipping save for item due to missing data: {item}")
                            continue
                        # Use os.path.basename to handle potential subdirs in prompt_name
                        output_filename = os.path.basename(original_prompt_path)
                        individual_output_path = output_dir / output_filename
                        logger.debug(f"Attempting to save file to: {individual_output_path}")
                        if not force and individual_output_path.exists():
                            logger.warning(f"Output file exists, skipping: {individual_output_path}. Use --force to overwrite.")
                            if not quiet: rprint(f"[yellow]Skipping existing file:[/yellow] {individual_output_path}")
                            continue
                        try:
                            with open(individual_output_path, 'w', encoding='utf-8') as f:
                                f.write(modified_content)
                            logger.debug(f"Saved modified prompt to: {individual_output_path}")
                            saved_files_count += 1
                        except IOError as e:
                            msg = f"Failed to write output file '{individual_output_path}': {e}"
                            if not quiet: rprint(f"[bold red]Error:[/bold red] {msg}")
                            logger.error(msg, exc_info=True)
                            # Continue to next file, don't abort the whole batch
                        except Exception as e:
                             msg = f"Unexpected error writing output file '{individual_output_path}': {e}"
                             if not quiet: rprint(f"[bold red]Error:[/bold red] {msg}")
                             logger.error(msg, exc_info=True)
                    logger.info("Results saved as individual files in directory successfully")
                    if not quiet: rprint(f"[bold]Saved {saved_files_count} modified prompts to:[/bold] {output_dir}")
                # result_message already set to "Multiple prompts have been updated."
            else: # Non-CSV mode saving
                if not output_path_obj:
                     msg = "[bold red]Error:[/bold red] Could not determine output path for modified prompt."
                     if not quiet: rprint(msg)
                     logger.error(msg)
                     return msg, total_cost, model_name
                logger.info(f"Saving single modified prompt to: {output_path_obj}")
                try:
                    output_path_obj.parent.mkdir(parents=True, exist_ok=True)
                    with open(output_path_obj, 'w', encoding='utf-8') as f:
                        f.write(result_message) # result_message contains modified content here
                    if not quiet:
                        rprint(f"[bold]Modified prompt saved to:[/bold] {output_path_obj}")
                        rprint(Panel(result_message, title="Modified Prompt Content", expand=False))
                    result_message = f"Modified prompt saved to {output_path_obj}" # Update msg for return
                except IOError as e:
                    msg = f"Failed to write output file '{output_path_obj}': {e}"
                    if not quiet: rprint(f"[bold red]Error:[/bold red] {msg}")
                    logger.error(msg, exc_info=True)
                    return msg, total_cost, model_name
                except Exception as e:
                    msg = f"Unexpected error writing output file '{output_path_obj}': {e}"
                    if not quiet: rprint(f"[bold red]Error:[/bold red] {msg}")
                    logger.error(msg, exc_info=True)
                    return msg, total_cost, model_name
        # --- 5. Final User Feedback --- 
        # Only show success details if the operation was marked as successful 
        # AND cost > 0 or modified_prompts_list is not empty (in case of free model/cached result)
        # Success flag is now mainly for avoiding this print on early exit errors
        if not quiet and success and (total_cost > 0 or modified_prompts_list or (not use_csv and result_message)):
            rprint("[bold green]Prompt modification completed successfully.[/bold green]")
            if model_name:
                rprint(f"[bold]Model used:[/bold] {model_name}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")

    except FileNotFoundError as e:
        msg = f"Input file not found: {e}"
        if not quiet: rprint(f"[bold red]Error:[/bold red] {msg}")
        logger.error(msg, exc_info=True)
        return msg, 0.0, ""
    except NotADirectoryError as e:
         msg = f"Expected a directory but found a file, or vice versa: {e}"
         if not quiet: rprint(f"[bold red]Error:[/bold red] {msg}")
         logger.error(msg, exc_info=True)
         return msg, 0.0, ""
    except Exception as e:
        msg = f"An unexpected error occurred: {e}"
        if not quiet: rprint(f"[bold red]An unexpected error occurred during the 'change' operation:[/bold red] {e}")
        logger.error("Unexpected error in change_main", exc_info=True)
        return msg, 0.0, ""

    logger.debug("change_main finished.")
    return result_message, total_cost, model_name
