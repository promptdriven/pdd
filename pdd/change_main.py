import csv
import os
from typing import Optional, Tuple, List, Dict
import click
from rich import print as rprint
import logging

from .construct_paths import construct_paths
from .change import change as change_func
from .process_csv_change import process_csv_change

logger = logging.getLogger(__name__)
logger.setLevel(logging.DEBUG)  # Changed from WARNING to DEBUG

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
    :param change_prompt_file: Path to the change prompt file.
    :param input_code: Path to the input code file or directory (when using '--csv').
    :param input_prompt_file: Path to the input prompt file. Optional and not used when '--csv' is specified.
    :param output: Optional path to save the modified prompt file. If not specified, it will be generated based on the input files.
    :param use_csv: Flag indicating whether to use CSV mode for batch changes.
    :return: A tuple containing the modified prompt or a message indicating multiple prompts were updated, total cost, and model name used.
    """
    logger.debug(f"Starting change_main with use_csv={use_csv}")
    try:
        # Validate arguments
        if not use_csv and not input_prompt_file:
            error_msg = "Error: 'input_prompt_file' is required when not using '--csv' mode."
            logger.error(error_msg)
            if not ctx.obj.get('quiet', False):
                rprint(f"[bold red]{error_msg}[/bold red]")
            return (error_msg, 0.0, "")

        # Check if input_code is a directory when using CSV mode
        if use_csv:
            try:
                if not os.path.isdir(input_code):
                    error_msg = f"In CSV mode, 'input_code' must be a directory. Got: {input_code}"
                    logger.error(error_msg)
                    if not ctx.obj.get('quiet', False):
                        rprint(f"[bold red]Error: {error_msg}[/bold red]")
                    return (error_msg, 0.0, "")
            except Exception as e:
                error_msg = f"Error checking input_code directory: {str(e)}"
                logger.error(error_msg)
                if not ctx.obj.get('quiet', False):
                    rprint(f"[bold red]Error: {error_msg}[/bold red]")
                return (error_msg, 0.0, "")

        # Construct file paths
        input_file_paths = {
            "change_prompt_file": change_prompt_file,
        }
        if not use_csv:
            input_file_paths["input_code"] = input_code
            input_file_paths["input_prompt_file"] = input_prompt_file

        command_options = {
            "output": output
        }

        logger.debug(f"Constructing paths with input_file_paths={input_file_paths}")
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=ctx.obj.get('quiet', False),
            command="change",
            command_options=command_options
        )

        # Load input files
        change_prompt_content = input_strings["change_prompt_file"]
        logger.debug("Change prompt content loaded")

        # Get strength and temperature from context
        strength = ctx.obj.get('strength', 0.9)
        temperature = ctx.obj.get('temperature', 0)
        logger.debug(f"Using strength={strength} and temperature={temperature}")

        if use_csv:
            logger.debug(f"Using CSV mode with input_code={input_code}")
            # Validate CSV file format
            try:
                with open(change_prompt_file, mode='r', newline='', encoding='utf-8') as csvfile:
                    reader = csv.DictReader(csvfile)
                    if 'prompt_name' not in reader.fieldnames or 'change_instructions' not in reader.fieldnames:
                        error_msg = "CSV file must contain 'prompt_name' and 'change_instructions' columns."
                        logger.error(error_msg)
                        if not ctx.obj.get('quiet', False):
                            rprint(f"[bold red]Error: {error_msg}[/bold red]")
                        return (error_msg, 0.0, "")
                    logger.debug(f"CSV file validated. Columns: {reader.fieldnames}")
            except Exception as e:
                error_msg = f"Error reading CSV file: {str(e)}"
                logger.error(error_msg)
                if not ctx.obj.get('quiet', False):
                    rprint(f"[bold red]Error: {error_msg}[/bold red]")
                return (error_msg, 0.0, "")

            # Perform batch changes using CSV
            try:
                logger.debug("Calling process_csv_change")
                success, modified_prompts, total_cost, model_name = process_csv_change(
                    csv_file=change_prompt_file,
                    strength=strength,
                    temperature=temperature,
                    code_directory=input_code,
                    language=ctx.obj.get('language', 'python'),
                    extension=ctx.obj.get('extension', '.py'),
                    budget=ctx.obj.get('budget', 10.0)
                )
                logger.debug(f"process_csv_change completed. Success: {success}")
            except Exception as e:
                error_msg = f"Error during CSV processing: {str(e)}"
                logger.error(error_msg)
                if not ctx.obj.get('quiet', False):
                    rprint(f"[bold red]Error: {error_msg}[/bold red]")
                return (error_msg, 0.0, "")

            # Determine output path
            output_path = output or output_file_paths.get('output', "batch_modified_prompts.csv")
            logger.debug(f"Output path: {output_path}")

            # Save results
            if success:
                try:
                    if output is None:
                        # Save individual files
                        logger.debug("Attempting to save individual prompt files.")
                        for i, item in enumerate(modified_prompts):
                            logger.debug(f"--- Processing item {i} ---")
                            try:
                                file_name = item['file_name']
                                modified_prompt = item['modified_prompt']
                                logger.debug(f"Item {i}: file_name = {repr(file_name)}")
                                logger.debug(f"Item {i}: output_path = {repr(output_path)}")

                                dirname_output = os.path.dirname(output_path)
                                logger.debug(f"Item {i}: os.path.dirname(output_path) = {repr(dirname_output)}")

                                individual_output_path = os.path.join(dirname_output, file_name)
                                logger.debug(f"Item {i}: Calculated individual_output_path = {repr(individual_output_path)}")

                                logger.debug(f"Item {i}: Attempting to open: {repr(individual_output_path)}")
                                with open(individual_output_path, 'w') as file:
                                    file.write(modified_prompt)
                                logger.debug(f"Item {i}: Successfully wrote to: {repr(individual_output_path)}")
                            except KeyError as ke:
                                logger.error(f"Item {i}: Missing key in modified_prompts item: {ke}. Item data: {item}")
                            except Exception as item_e:
                                logger.error(f"Item {i}: Error processing item: {item_e}. Item data: {item}")
                                raise

                        logger.debug("Finished saving individual files successfully")
                    else:
                        # Check if output_path is a directory
                        if os.path.isdir(output_path):
                            # Handle as a directory - save individual files inside it
                            logger.debug(f"Output path is a directory: {repr(output_path)}")
                            for i, item in enumerate(modified_prompts):
                                try:
                                    file_name = item['file_name']
                                    modified_prompt = item['modified_prompt']
                                    
                                    # Extract just the basename from the file_name path
                                    base_file_name = os.path.basename(file_name)
                                    
                                    individual_output_path = os.path.join(output_path, base_file_name)
                                    logger.debug(f"Saving file to: {repr(individual_output_path)}")
                                    with open(individual_output_path, 'w') as file:
                                        file.write(modified_prompt)
                                except KeyError as ke:
                                    logger.error(f"Item {i}: Missing key in modified_prompts item: {ke}. Item data: {item}")
                                except Exception as item_e:
                                    logger.error(f"Item {i}: Error processing item: {item_e}. Item data: {item}")
                                    raise
                            logger.debug("Results saved as individual files in directory successfully")
                        else:
                            # Handle as a CSV file
                            logger.debug(f"Attempting to save results to CSV: {repr(output_path)}")
                            with open(output_path, 'w', newline='') as csvfile:
                                fieldnames = ['file_name', 'modified_prompt']
                                writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
                                writer.writeheader()
                                for item in modified_prompts:
                                    writer.writerow(item)
                            logger.debug("Results saved to CSV successfully")
                except Exception as e:
                    error_msg = f"Error writing output: {str(e)}"
                    logger.error(error_msg)
                    if not ctx.obj.get('quiet', False):
                        rprint(f"[bold red]Error: {error_msg}[/bold red]")
                    return (error_msg, total_cost, model_name)

            # Provide user feedback
            if not ctx.obj.get('quiet', False):
                if use_csv and success:
                    rprint("[bold green]Batch change operation completed successfully.[/bold green]")
                    rprint(f"[bold]Model used:[/bold] {model_name}")
                    rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
                    if output is None:
                        output_dir = os.path.dirname(output_path)
                        rprint(f"[bold]Results saved as individual files in:[/bold] {output_dir}")
                        for item in modified_prompts:
                            file_name = item['file_name']
                            individual_output_path = os.path.join(output_dir, file_name)
                            rprint(f"  - {individual_output_path}")
                    elif os.path.isdir(output_path):
                        rprint(f"[bold]Results saved as individual files in directory:[/bold] {output_path}")
                        for item in modified_prompts:
                            file_name = item['file_name']
                            base_file_name = os.path.basename(file_name)
                            individual_output_path = os.path.join(output_path, base_file_name)
                            rprint(f"  - {individual_output_path}")
                    else:
                        rprint(f"[bold]Results saved to CSV:[/bold] {output_path}")

            logger.debug("Returning success message for CSV mode")
            return ("Multiple prompts have been updated.", total_cost, model_name)

        else:
            logger.debug("Using non-CSV mode")
            input_code_content = input_strings["input_code"]
            input_prompt_content = input_strings["input_prompt_file"]

            # Perform single change
            logger.debug("Calling change_func")
            try:
                modified_prompt, total_cost, model_name = change_func(
                    input_prompt=input_prompt_content,
                    input_code=input_code_content,
                    change_prompt=change_prompt_content,
                    strength=strength,
                    temperature=temperature,
                    verbose=ctx.obj.get('verbose', False),
                )
                logger.debug("change_func completed")
            except Exception as e:
                error_msg = f"An unexpected error occurred: {str(e)}"
                logger.error(error_msg)
                if not ctx.obj.get('quiet', False):
                    rprint(f"[bold red]Error: {error_msg}[/bold red]")
                return (error_msg, 0.0, "")

            # Determine output path
            output_path = output or output_file_paths.get('output', f"modified_{os.path.basename(input_prompt_file)}")
            logger.debug(f"Output path: {output_path}")

            # Save the modified prompt
            try:
                with open(output_path, 'w') as f:
                    f.write(modified_prompt)
                logger.debug("Results saved successfully")
            except Exception as e:
                error_msg = f"Error writing output file: {str(e)}"
                logger.error(error_msg)
                if not ctx.obj.get('quiet', False):
                    rprint(f"[bold red]Error: {error_msg}[/bold red]")
                return (error_msg, total_cost, model_name)

            # Provide user feedback
            if not ctx.obj.get('quiet', False):
                rprint("[bold green]Prompt modification completed successfully.[/bold green]")
                rprint(f"[bold]Model used:[/bold] {model_name}")
                rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
                rprint(f"[bold]Modified prompt saved to:[/bold] {output_path}")

            logger.debug("Returning success message for non-CSV mode")
            return (modified_prompt, total_cost, model_name)

    except Exception as e:
        error_msg = f"An unexpected error occurred: {str(e)}"
        logger.error(error_msg)
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold red]Error: {error_msg}[/bold red]")
        return (error_msg, 0.0, "")

    # This line should never be reached, but we'll log it just in case
    logger.warning("Reached end of change_main without returning")
    return ("An unknown error occurred", 0.0, "")