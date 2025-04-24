import csv
import os
from pathlib import Path # Added Path
from typing import Optional, Tuple, List, Dict
import click
from rich import print as rprint
import logging
import traceback

from .construct_paths import construct_paths
from .change import change as change_func
# Remove process_csv_change import as logic moves here
# from .process_csv_change import process_csv_change
from .get_extension import get_extension # Added get_extension

logger = logging.getLogger(__name__)
logger.setLevel(logging.DEBUG)

def change_main(
    ctx: click.Context,
    change_prompt_file: str,
    input_code: str,
    input_prompt_file: Optional[str],
    output: Optional[str],
    use_csv: bool
) -> Tuple[str, float, str]:
    """
    Main function to handle the 'change' command logic.

    :param ctx: Click context containing command-line parameters.
    :param change_prompt_file: Path to the change prompt file (or CSV).
    :param input_code: Path to the input code file or directory (when using '--csv').
    :param input_prompt_file: Path to the input prompt file. Optional and not used when '--csv' is specified.
    :param output: Optional path to save the modified prompt file(s).
    :param use_csv: Flag indicating whether to use CSV mode for batch changes.
    :return: A tuple containing the modified prompt or a message indicating multiple prompts were updated, total cost, and model name used.
    """
    logger.debug(f"Starting change_main with use_csv={use_csv}")
    total_cost: float = 0.0
    model_name: str = ""
    modified_prompts: List[Dict[str, str]] = [] # Initialize here for CSV mode
    quiet = ctx.obj.get('quiet', False)
    force = ctx.obj.get('force', False)
    strength = ctx.obj.get('strength', 0.9)
    temperature = ctx.obj.get('temperature', 0)
    budget = ctx.obj.get('budget', 10.0) # Get budget from context

    try:
        if use_csv:
            # 1. Validate CSV file and code directory paths
            csv_path = Path(change_prompt_file)
            code_dir_path = Path(input_code)

            if not csv_path.is_file():
                error_msg = f"CSV file not found: {change_prompt_file}"
                logger.error(error_msg)
                if not quiet: rprint(f"[bold red]Error: {error_msg}[/bold red]")
                return (error_msg, 0.0, "")

            if not code_dir_path.is_dir():
                error_msg = f"Input code directory not found or not a directory: {input_code}"
                logger.error(error_msg)
                if not quiet: rprint(f"[bold red]Error: {error_msg}[/bold red]")
                return (error_msg, 0.0, "")

            # 2. Determine base output path using construct_paths logic (simplified for CSV)
            # We need a basename for default output naming if 'output' is a dir or None
            # Let construct_paths figure out the basename from the CSV filename
            try:
                 # Only pass csv file path, other inputs aren't files in this mode
                 _, output_file_paths, _ = construct_paths(
                     input_file_paths={"change_prompt_file": change_prompt_file},
                     force=force,
                     quiet=True, # Suppress path logging from this call
                     command="change", # Still use 'change' command context
                     command_options={"output": output} # Pass output option
                 )
                 # Get the primary output path determined by construct_paths
                 base_output_path = output_file_paths.get('output', None)
                 logger.debug(f"Base output path from construct_paths: {base_output_path}")
            except Exception as e:
                 error_msg = f"Error determining output path: {e}"
                 logger.error(error_msg)
                 if not quiet: rprint(f"[bold red]{error_msg}[/bold red]")
                 return (error_msg, 0.0, "")

            # 3. Process the CSV
            logger.debug(f"Processing CSV file: {csv_path}")
            try:
                with open(csv_path, mode='r', newline='', encoding='utf-8') as csvfile:
                    reader = csv.DictReader(csvfile)
                    if 'prompt_name' not in reader.fieldnames or 'change_instructions' not in reader.fieldnames:
                        error_msg = "CSV file must contain 'prompt_name' and 'change_instructions' columns."
                        logger.error(error_msg)
                        if not quiet: rprint(f"[bold red]Error: {error_msg}[/bold red]")
                        return (error_msg, 0.0, "")
                    logger.debug(f"CSV validated. Columns: {reader.fieldnames}")

                    for row_number, row in enumerate(reader, start=1):
                        prompt_name = row.get('prompt_name', '').strip()
                        change_instructions = row.get('change_instructions', '').strip()
                        logger.debug(f"Processing row {row_number}: prompt_name='{prompt_name}'")

                        if not prompt_name or not change_instructions:
                            logger.warning(f"Skipping row {row_number} due to missing prompt_name or change_instructions.")
                            if not quiet: rprint(f"[yellow]Warning: Skipping row {row_number} due to missing data.[/yellow]")
                            continue

                        # --- Dynamic Extension Logic ---
                        try:
                            # Assume prompt_name is just the filename relative to code_dir_path
                            prompt_path = Path(prompt_name).resolve() # CORRECT: Resolve relative to CWD
                            prompt_path_obj = Path(prompt_name) # Use Path object for parsing
                            prompt_stem = prompt_path_obj.stem # e.g., "dummy_a_python"

                            language_suffix = ""
                            base_name = prompt_stem
                            if '_' in prompt_stem:
                                parts = prompt_stem.rsplit('_', 1)
                                base_name = parts[0]
                                potential_lang = parts[1]
                                # Check if the suffix is a known language
                                derived_extension = get_extension(potential_lang)
                                if derived_extension:
                                    language_suffix = potential_lang
                                    code_extension = derived_extension
                                    logger.debug(f"Row {row_number}: Detected language '{language_suffix}' -> extension '{code_extension}'")
                                else:
                                    # Suffix not a language, revert base_name and use default/fallback
                                    base_name = prompt_stem # Use full stem if suffix wasn't language
                                    code_extension = ".txt" # Or some other sensible default? Let's use .txt
                                    logger.warning(f"Row {row_number}: Suffix '_{potential_lang}' not a recognized language. Assuming extension '{code_extension}'.")
                            else:
                                # No underscore, assume no language suffix
                                code_extension = ".txt" # Default extension if no language found
                                logger.warning(f"Row {row_number}: No language suffix found in '{prompt_name}'. Assuming extension '{code_extension}'.")

                            # Construct code file path
                            input_code_name = f"{base_name}{code_extension}"
                            input_code_path = (code_dir_path / input_code_name).resolve()
                            logger.debug(f"Row {row_number}: Expecting prompt file: {prompt_path}")
                            logger.debug(f"Row {row_number}: Expecting code file: {input_code_path}")

                            # Check file existence
                            if not prompt_path.is_file():
                                logger.warning(f"Input prompt file not found for row {row_number}: {prompt_path}")
                                if not quiet: rprint(f"[yellow]Warning: Prompt file '{prompt_path}' not found. Skipping row {row_number}.[/yellow]")
                                continue
                            if not input_code_path.is_file():
                                logger.warning(f"Input code file not found for row {row_number}: {input_code_path}")
                                if not quiet: rprint(f"[yellow]Warning: Code file '{input_code_path}' not found. Skipping row {row_number}.[/yellow]")
                                continue

                            # Read file contents
                            input_prompt_content = prompt_path.read_text(encoding='utf-8')
                            input_code_content = input_code_path.read_text(encoding='utf-8')

                            # Call the core change function
                            logger.debug(f"Row {row_number}: Calling change_func")
                            modified_prompt, cost, current_model_name = change_func(
                                input_prompt=input_prompt_content,
                                input_code=input_code_content,
                                change_prompt=change_instructions,
                                strength=strength,
                                temperature=temperature,
                                verbose=ctx.obj.get('verbose', False), # Pass verbose flag
                            )
                            logger.debug(f"Row {row_number}: change_func completed. Cost: {cost}, Model: {current_model_name}")

                            total_cost += cost
                            if not model_name: # Capture model name from first successful call
                                model_name = current_model_name
                            elif model_name != current_model_name:
                                logger.warning(f"Model name changed from {model_name} to {current_model_name}")
                                # Decide how to handle model name changes if necessary

                            # Check budget
                            if total_cost > budget:
                                logger.warning(f"Budget exceeded (${total_cost:.6f} > ${budget:.2f}) after row {row_number}. Stopping.")
                                if not quiet: rprint(f"[bold red]Budget exceeded. Stopping processing.[/bold red]")
                                break # Stop processing more rows

                            # Store result
                            modified_prompts.append({
                                "file_name": prompt_name, # Store original relative prompt name
                                "modified_prompt": modified_prompt
                            })
                            logger.info(f"Row {row_number} processed successfully.")

                        except Exception as row_e:
                            logger.error(f"Error processing row {row_number} for prompt '{prompt_name}': {row_e}")
                            logger.error(traceback.format_exc())
                            if not quiet: rprint(f"[red]Error processing row {row_number}: {row_e}. Skipping.[/red]")
                            continue # Skip to next row on error

            except Exception as csv_e:
                error_msg = f"Error reading or processing CSV file: {csv_e}"
                logger.error(error_msg)
                logger.error(traceback.format_exc())
                if not quiet: rprint(f"[bold red]Error: {error_msg}[/bold red]")
                return (error_msg, total_cost, model_name) # Return accumulated cost so far

            # --- CSV Processing Done ---

            # Determine actual output path/mode (Directory, specific CSV file, or default individual files)
            output_target_is_dir = False
            output_target_is_csv = False
            final_output_path = base_output_path # Start with path from construct_paths

            if output: # If --output was provided
                output_path_obj = Path(output)
                # Check if it explicitly names an existing directory OR ends with / or \
                if output_path_obj.is_dir():
                     output_target_is_dir = True
                     final_output_path = output # Use the user-provided dir path
                     logger.debug(f"Output target is directory: {final_output_path}")
                elif output.endswith(('.csv', '.CSV')):
                     output_target_is_csv = True
                     final_output_path = output # Use the user-provided CSV path
                     logger.debug(f"Output target is CSV file: {final_output_path}")
                else:
                     # Assume it's a directory if it doesn't end with .csv and isn't an existing file
                     # Or maybe treat as CSV by default if not clearly a dir? Let's default to CSV.
                     output_target_is_csv = True
                     final_output_path = output
                     logger.debug(f"Output target assumed to be CSV file: {final_output_path}")

            else: # --output not provided, default to individual files in CWD or output_dir from context
                output_target_is_dir = True # Default mode is saving individual files
                final_output_path = "." # Default to current directory
                 # Use the directory suggested by construct_paths if it determined one
                if base_output_path and Path(base_output_path).parent != Path("."):
                    final_output_path = str(Path(base_output_path).parent)

                logger.debug(f"Output target is default directory: {final_output_path}")


            # Save results based on determined mode
            try:
                if output_target_is_dir:
                    logger.debug(f"Saving individual files to directory: {final_output_path}")
                    output_dir = Path(final_output_path)
                    output_dir.mkdir(parents=True, exist_ok=True)
                    for item in modified_prompts:
                        # Save file relative to the output directory
                        # Use the original prompt_name which might contain subdirs
                        individual_output_path = output_dir / item['file_name']
                        # Ensure parent directory for the file exists within the output dir
                        individual_output_path.parent.mkdir(parents=True, exist_ok=True)
                        individual_output_path.write_text(item['modified_prompt'], encoding='utf-8')
                        logger.debug(f"Saved: {individual_output_path}")

                    if not quiet:
                        rprint(f"[bold]Results saved as individual files in:[/bold] {output_dir.resolve()}")
                        for item in modified_prompts:
                           rprint(f"  - {(output_dir / item['file_name']).resolve()}")

                elif output_target_is_csv:
                    logger.debug(f"Saving results to CSV file: {final_output_path}")
                    output_csv_path = Path(final_output_path)
                    output_csv_path.parent.mkdir(parents=True, exist_ok=True) # Ensure parent dir exists
                    with open(output_csv_path, 'w', newline='', encoding='utf-8') as csvfile:
                        fieldnames = ['file_name', 'modified_prompt']
                        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
                        writer.writeheader()
                        writer.writerows(modified_prompts) # Write all rows
                    logger.debug("Results saved to CSV successfully")
                    if not quiet:
                         rprint(f"[bold]Results saved to CSV:[/bold] {output_csv_path.resolve()}")

            except Exception as e:
                error_msg = f"Error writing output: {str(e)}"
                logger.error(f"Error during output saving: {str(e)}")
                logger.error(f"Exception type: {type(e)}")
                logger.error(f"Traceback: {traceback.format_exc()}")
                if not quiet: rprint(f"[bold red]Error: {error_msg}[/bold red]")
                # Return accumulated cost even if saving failed
                return (error_msg, total_cost, model_name)

            # Provide summary feedback for CSV mode
            if not quiet:
                 rprint("[bold green]Batch change operation completed.[/bold green]")
                 rprint(f"[bold]Model used:[/bold] {model_name if model_name else 'N/A'}")
                 rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
                 # Saving location message printed within the saving block

            logger.debug("Returning success message for CSV mode")
            return ("Multiple prompts have been updated.", total_cost, model_name)

        else: # --- Non-CSV Mode ---
            logger.debug("Using non-CSV mode")
            if not input_prompt_file: # Should have been caught earlier, but double-check
                 error_msg = "Error: 'input_prompt_file' is required when not using '--csv' mode."
                 logger.error(error_msg)
                 if not quiet: rprint(f"[bold red]{error_msg}[/bold red]")
                 return (error_msg, 0.0, "")

            # Construct paths for single file mode
            input_file_paths = {
                "change_prompt_file": change_prompt_file,
                "input_code": input_code,
                "input_prompt_file": input_prompt_file,
            }
            command_options = {"output": output}
            try:
                 logger.debug(f"Constructing paths with input_file_paths={input_file_paths}")
                 input_strings, output_file_paths, _ = construct_paths(
                     input_file_paths=input_file_paths,
                     force=force,
                     quiet=quiet, # Pass quiet flag here
                     command="change",
                     command_options=command_options
                 )
            except FileNotFoundError as e:
                 error_msg = f"Input file not found: {e}"
                 logger.error(error_msg)
                 if not quiet: rprint(f"[bold red]Error: {error_msg}[/bold red]")
                 return (error_msg, 0.0, "")
            except Exception as e:
                 error_msg = f"Error constructing paths: {e}"
                 logger.error(error_msg)
                 if not quiet: rprint(f"[bold red]Error: {error_msg}[/bold red]")
                 return (error_msg, 0.0, "")


            change_prompt_content = input_strings["change_prompt_file"]
            input_code_content = input_strings["input_code"]
            input_prompt_content = input_strings["input_prompt_file"]
            logger.debug("Input files loaded for non-CSV mode")

            # Perform single change
            logger.debug("Calling change_func")
            try:
                modified_prompt, cost, current_model_name = change_func(
                    input_prompt=input_prompt_content,
                    input_code=input_code_content,
                    change_prompt=change_prompt_content,
                    strength=strength,
                    temperature=temperature,
                    verbose=ctx.obj.get('verbose', False),
                )
                total_cost = cost # Assign cost for single operation
                model_name = current_model_name
                logger.debug(f"change_func completed. Cost: {cost}, Model: {model_name}")
            except Exception as e:
                error_msg = f"Error during prompt modification: {str(e)}"
                logger.error(error_msg)
                logger.error(traceback.format_exc())
                if not quiet: rprint(f"[bold red]Error: {error_msg}[/bold red]")
                return (error_msg, 0.0, "")

            # Determine output path
            output_path = output_file_paths.get('output') # Get path determined by construct_paths
            if not output_path: # Should not happen if construct_paths worked
                 output_path = f"modified_{os.path.basename(input_prompt_file)}"
                 logger.warning(f"Could not determine output path from construct_paths, defaulting to {output_path}")

            logger.debug(f"Output path: {output_path}")

            # Save the modified prompt
            try:
                output_path_obj = Path(output_path)
                output_path_obj.parent.mkdir(parents=True, exist_ok=True) # Ensure parent dir exists
                output_path_obj.write_text(modified_prompt, encoding='utf-8')
                logger.debug("Results saved successfully")
            except Exception as e:
                error_msg = f"Error writing output file: {str(e)}"
                logger.error(error_msg)
                if not quiet: rprint(f"[bold red]Error: {error_msg}[/bold red]")
                return (error_msg, total_cost, model_name)

            # Provide user feedback
            if not quiet:
                rprint("[bold green]Prompt modification completed successfully.[/bold green]")
                rprint(f"[bold]Model used:[/bold] {model_name}")
                rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
                rprint(f"[bold]Modified prompt saved to:[/bold] {Path(output_path).resolve()}")

            logger.debug("Returning success message for non-CSV mode")
            return (modified_prompt, total_cost, model_name)

    except Exception as e:
        error_msg = f"An unexpected error occurred in change_main: {str(e)}"
        logger.error(error_msg)
        logger.error(traceback.format_exc())
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold red]Error: {error_msg}[/bold red]")
        # Return accumulated cost if available, otherwise 0.0
        return (error_msg, total_cost, model_name if model_name else "")
