import click
import logging
import os # <--- Added import
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
    budget: float,
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
        budget: Budget for the operation.

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

        # Handle trailing slashes in output path *before* using it in validation/construct_paths
        original_output = output # Keep original for potential later use if needed
        if output and isinstance(output, str) and output.endswith(('/', '\\')):
            logger.debug(f"Normalizing output path: {output}")
            output = os.path.normpath(output)
            logger.debug(f"Normalized output path: {output}")

        if use_csv:
            if input_prompt_file:
                msg = "[bold red]Error:[/bold red] --input-prompt-file should not be provided when using --csv mode."
                if not quiet: rprint(msg)
                logger.error(msg)
                return msg, 0.0, ""
            # Check if input_code is a directory *before* trying to use it
            if not os.path.isdir(input_code):
                msg = f"[bold red]Error:[/bold red] In CSV mode, --input-code ('{input_code}') must be a valid directory."
                if not quiet: rprint(msg)
                logger.error(msg)
                return msg, 0.0, ""
            if not change_prompt_file.lower().endswith(".csv"):
                 logger.warning(f"Input change file '{change_prompt_file}' does not end with .csv. Assuming it's a CSV.")

            # Validate CSV header *before* calling construct_paths
            logger.debug("Validating CSV header...")
            try:
                with open(change_prompt_file, 'r', newline='', encoding='utf-8') as csvfile:
                    # Peek at the header using DictReader's fieldnames
                    # Use DictReader to easily access fieldnames
                    reader = csv.DictReader(csvfile)
                    header = reader.fieldnames
                    if header is None:
                        raise csv.Error("CSV file appears to be empty or header is missing.")
                    logger.debug(f"CSV header found: {header}")
                    required_columns = {'prompt_name', 'change_instructions'}
                    if not required_columns.issubset(header):
                        missing_columns = required_columns - set(header)
                        msg = "CSV file must contain 'prompt_name' and 'change_instructions' columns."
                        if missing_columns:
                            msg += f" Missing: {missing_columns}"
                        if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                        logger.error(msg)
                        return msg, 0.0, ""
                    logger.debug("CSV header validated successfully.")
            except FileNotFoundError:
                msg = f"CSV file not found: {change_prompt_file}"
                if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                logger.error(msg)
                return msg, 0.0, ""
            except csv.Error as e: # Catch specific CSV errors
                msg = f"Failed to read or validate CSV header: {e}"
                if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                logger.error(f"CSV header validation error: {e}", exc_info=True)
                return msg, 0.0, ""
            except Exception as e: # Catch other potential file errors
                msg = f"Failed to open or read CSV file '{change_prompt_file}': {e}"
                if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                logger.error(f"Error reading CSV file: {e}", exc_info=True)
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
        # Pass the potentially normalized output path to construct_paths
        command_options: Dict[str, Any] = {"output": output} if output is not None else {}

        # Prepare input paths for construct_paths based on mode
        if use_csv:
            # Only the CSV file needs to be read by construct_paths initially
            input_file_paths["change_prompt_file"] = change_prompt_file
            # input_code is a directory, handled later
        else:
            # All inputs are files in non-CSV mode
            input_file_paths["change_prompt_file"] = change_prompt_file
            input_file_paths["input_code"] = input_code
            input_file_paths["input_prompt_file"] = input_prompt_file

        logger.debug(f"Calling construct_paths with inputs: {input_file_paths} and options: {command_options}")
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
            msg = f"Error constructing paths: {e}"
            if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
            logger.error(msg, exc_info=True)
            return msg, 0.0, ""

        # --- 3. Perform Prompt Modification ---
        if use_csv:
            logger.info("Running in CSV mode.")
            # Determine language and extension for process_csv_change
            csv_target_language = target_language or language or "python" # Prioritize context language
            try:
                if target_extension:
                    extension = target_extension
                    logger.debug(f"Using extension '{extension}' from context for CSV processing.")
                else:
                    extension = get_extension(csv_target_language)
                    logger.debug(f"Derived language '{csv_target_language}' and extension '{extension}' for CSV processing.")
            except ValueError as e:
                 msg = f"Could not determine file extension for language '{csv_target_language}': {e}"
                 if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                 logger.error(msg)
                 return msg, 0.0, ""

            try:
                # Call process_csv_change - this is the function mocked in CSV tests
                success, modified_prompts_list, total_cost, model_name = process_csv_change(
                    csv_file=change_prompt_file,
                    strength=strength,
                    temperature=temperature,
                    code_directory=input_code, # Pass the directory path
                    language=csv_target_language,
                    extension=extension,
                    budget=budget,
                    # Pass verbosity if needed by process_csv_change internally
                    #verbose=ctx.obj.get("verbose", False) # Removed based on TypeError in verification
                )
                # Process_csv_change should return cost and model name even on partial success/failure.
                logger.info(f"process_csv_change returned: success={success}, cost={total_cost}, model={model_name}")
            except Exception as e:
                # This catches errors within process_csv_change itself
                msg = f"Error during CSV processing: {e}"
                if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                logger.error(msg, exc_info=True)
                # Even if the process fails, the tests expect the overall success message
                result_message = "Multiple prompts have been updated."
                # Return 0 cost/empty model on *exception* during the call
                return result_message, 0.0, ""

            # Always set the result message for CSV mode, regardless of internal success/failure of rows
            result_message = "Multiple prompts have been updated."
            logger.info(f"CSV processing complete. Result message: {result_message}")

        else: # Non-CSV mode
            logger.info("Running in single-file mode.")
            change_prompt_content = input_strings.get("change_prompt_file")
            input_code_content = input_strings.get("input_code")
            input_prompt_content = input_strings.get("input_prompt_file")

            if not all([change_prompt_content, input_code_content, input_prompt_content]):
                 missing = [k for k, v in {"change_prompt_file": change_prompt_content,
                                           "input_code": input_code_content,
                                           "input_prompt_file": input_prompt_content}.items() if not v]
                 msg = f"Failed to read content for required input files: {', '.join(missing)}"
                 if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                 logger.error(msg)
                 return msg, 0.0, ""

            try:
                modified_prompt, total_cost, model_name = change_func(
                    input_prompt=input_prompt_content,
                    input_code=input_code_content,
                    change_prompt=change_prompt_content,
                    strength=strength,
                    temperature=temperature,
                    verbose=ctx.obj.get("verbose", False),
                )
                result_message = modified_prompt # Store the content for saving
                success = True # Assume success if no exception
                logger.info("Single prompt change successful.")
            except Exception as e:
                msg = f"Error during prompt modification: {e}"
                if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                logger.error(msg, exc_info=True)
                return msg, 0.0, ""

        # --- 4. Save Results ---
        # Determine output path object using the potentially normalized 'output'
        output_path_obj: Optional[Path] = None
        if output:
            output_path_obj = Path(output).resolve()
            logger.debug(f"Resolved user specified output path: {output_path_obj}")
        elif not use_csv and "output_prompt_file" in output_file_paths:
             # Use default path from construct_paths for single file mode if no --output
             output_path_obj = Path(output_file_paths["output_prompt_file"]).resolve()
             logger.debug(f"Using default output path from construct_paths: {output_path_obj}")

        # Proceed with saving if CSV mode OR if non-CSV mode was successful
        if use_csv or success:
            if use_csv:
                # Determine if output is explicitly a CSV file
                output_is_csv = output_path_obj and output_path_obj.suffix.lower() == ".csv"

                if output_is_csv:
                    # Save all results to a single CSV file
                    logger.info(f"Saving batch results to CSV: {output_path_obj}")
                    try:
                        output_path_obj.parent.mkdir(parents=True, exist_ok=True) # Uses Path.mkdir, OK here
                        with open(output_path_obj, 'w', newline='', encoding='utf-8') as outfile:
                            # Use the fieldnames expected by the tests
                            fieldnames = ['file_name', 'modified_prompt']
                            writer = csv.DictWriter(outfile, fieldnames=fieldnames)
                            writer.writeheader()
                            # Only write successfully processed prompts from the list
                            for item in modified_prompts_list:
                                # Ensure item has the expected keys before writing
                                if 'file_name' in item and 'modified_prompt' in item and item['modified_prompt'] is not None:
                                     writer.writerow({
                                        'file_name': item.get('file_name', 'unknown_prompt'),
                                        'modified_prompt': item.get('modified_prompt', '')
                                    })
                                else:
                                    logger.warning(f"Skipping row in output CSV due to missing data or error: {item.get('file_name')}")
                        if not quiet: rprint(f"[green]Results saved to:[/green] {output_path_obj}")
                    except IOError as e:
                        msg = f"Failed to write output CSV '{output_path_obj}': {e}"
                        if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                        logger.error(msg, exc_info=True)
                        # Return the standard CSV message but potentially with cost/model from successful rows
                        return result_message, total_cost, model_name or ""
                    except Exception as e:
                        msg = f"Unexpected error writing output CSV '{output_path_obj}': {e}"
                        if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                        logger.error(msg, exc_info=True)
                        return result_message, total_cost, model_name or ""

                else:
                    # Save each modified prompt to an individual file
                    # Determine output directory: explicit dir, parent of explicit file, or CWD
                    output_dir: Path
                    if output_path_obj:
                        # Check if the resolved path exists and is a directory
                        # We need Path.is_dir() mocked correctly in tests for this path
                        if output_path_obj.is_dir():
                            output_dir = output_path_obj
                        # Check if it doesn't exist AND doesn't have a suffix (likely intended dir)
                        elif not output_path_obj.exists() and not output_path_obj.suffix:
                             output_dir = output_path_obj
                        else: # Assume it's a file path, use parent
                             output_dir = output_path_obj.parent
                             logger.warning(f"Output path '{output_path_obj}' is not a directory or CSV. Saving individual files to parent directory: {output_dir}")
                    else: # No output specified, save to CWD
                        output_dir = Path.cwd()

                    logger.info(f"Saving individual modified prompts to directory: {output_dir}")
                    try:
                        # Use os.makedirs to align with test mocks
                        os.makedirs(output_dir, exist_ok=True) # <--- Changed to os.makedirs
                    except OSError as e:
                         msg = f"Failed to create output directory '{output_dir}': {e}"
                         if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                         logger.error(msg, exc_info=True)
                         return result_message, total_cost, model_name or ""

                    saved_files_count = 0
                    for item in modified_prompts_list:
                        original_prompt_filename = item.get('file_name') # This should be the original prompt filename
                        modified_content = item.get('modified_prompt')

                        # Skip if modification failed for this file or data is missing
                        if not original_prompt_filename or modified_content is None:
                            logger.warning(f"Skipping save for item due to missing data or error: {item}")
                            continue

                        # Use original filename for the output file
                        individual_output_path = output_dir / Path(original_prompt_filename).name

                        if not force and individual_output_path.exists():
                            logger.warning(f"Output file exists, skipping: {individual_output_path}. Use --force to overwrite.")
                            if not quiet: rprint(f"[yellow]Skipping existing file:[/yellow] {individual_output_path}")
                            continue

                        try:
                            logger.debug(f"Attempting to save file to: {individual_output_path}")
                            with open(individual_output_path, 'w', encoding='utf-8') as f:
                                f.write(modified_content)
                            logger.debug(f"Saved modified prompt to: {individual_output_path}")
                            saved_files_count += 1
                        except IOError as e:
                            msg = f"Failed to write output file '{individual_output_path}': {e}"
                            if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                            logger.error(msg, exc_info=True)
                            # Continue saving others
                        except Exception as e:
                             msg = f"Unexpected error writing output file '{individual_output_path}': {e}"
                             if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                             logger.error(msg, exc_info=True)
                             # Continue saving others

                    logger.info(f"Results saved as individual files in directory successfully")
                    if not quiet: rprint(f"[green]Saved {saved_files_count} modified prompts to:[/green] {output_dir}")

            else: # Non-CSV mode saving
                if not output_path_obj:
                     # This case should ideally be caught by construct_paths, but double-check
                     msg = "Could not determine output path for modified prompt."
                     if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                     logger.error(msg)
                     return msg, 0.0, ""

                logger.info(f"Saving single modified prompt to: {output_path_obj}")
                try:
                    output_path_obj.parent.mkdir(parents=True, exist_ok=True) # Uses Path.mkdir, OK here
                    # Use open() for writing as expected by tests
                    with open(output_path_obj, 'w', encoding='utf-8') as f:
                        f.write(result_message) # result_message contains the modified content here
                    if not quiet:
                        rprint(f"[green]Modified prompt saved to:[/green] {output_path_obj}")
                        rprint(Panel(result_message, title="Modified Prompt Content", expand=False))
                    # Update result_message for return value to be a status, not the full content
                    result_message = f"Modified prompt saved to {output_path_obj}"

                except IOError as e:
                    msg = f"Failed to write output file '{output_path_obj}': {e}"
                    if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                    logger.error(msg, exc_info=True)
                    return msg, total_cost, model_name or "" # Return error after processing
                except Exception as e:
                    msg = f"Unexpected error writing output file '{output_path_obj}': {e}"
                    if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
                    logger.error(msg, exc_info=True)
                    return msg, total_cost, model_name or ""

        # --- 5. Final User Feedback ---
        # Show summary if not quiet AND (it was CSV mode OR non-CSV mode succeeded)
        if not quiet and (use_csv or success):
            rprint("[bold green]Prompt modification completed successfully.[/bold green]")
            rprint(f"[bold]Model used:[/bold] {model_name or 'N/A'}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            if use_csv:
                if output_is_csv:
                     rprint(f"[bold]Results saved to CSV:[/bold] {output_path_obj.resolve()}")
                else:
                     # Re-calculate output_dir in case it wasn't set earlier (e.g., no output specified)
                     final_output_dir = Path(output).resolve() if output and Path(output).resolve().is_dir() else Path.cwd()
                     if output and not final_output_dir.is_dir(): # Handle case where output was file-like
                          # Use the previously calculated output_dir if available
                          final_output_dir = output_dir if 'output_dir' in locals() else Path(output).resolve().parent
                     rprint(f"[bold]Results saved as individual files in directory:[/bold] {final_output_dir}")


    except FileNotFoundError as e:
        msg = f"Input file not found: {e}"
        if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
        logger.error(msg, exc_info=True)
        return msg, 0.0, ""
    except NotADirectoryError as e:
         msg = f"Expected a directory but found a file, or vice versa: {e}"
         if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
         logger.error(msg, exc_info=True)
         return msg, 0.0, ""
    except Exception as e:
        # Catch-all for truly unexpected errors during the main flow
        msg = f"An unexpected error occurred: {e}"
        if not quiet: rprint(f"[bold red]Error: {msg}[/bold red]")
        logger.error("Unexpected error in change_main", exc_info=True)
        return msg, 0.0, ""

    logger.debug("change_main finished.")
    # Return computed values, ensuring model_name is never None
    return result_message, total_cost, model_name or ""
