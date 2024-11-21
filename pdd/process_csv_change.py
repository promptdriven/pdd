# process_csv_change.py

from typing import List, Dict, Tuple
import os
import csv
from pathlib import Path
import logging

from rich.console import Console
from rich.pretty import Pretty
from rich.panel import Panel

from .change import change  # Relative import for the internal change function

console = Console()

# Set up logging
logging.basicConfig(level=logging.WARNING)
logger = logging.getLogger(__name__)

def process_csv_change(
    csv_file: str,
    strength: float,
    temperature: float,
    code_directory: str,
    language: str,
    extension: str,
    budget: float
) -> Tuple[bool, List[Dict[str, str]], float, str]:
    """
    Processes a CSV file to apply changes to code prompts using an LLM model.

    Args:
        csv_file (str): Path to the CSV file containing 'prompt_name' and 'change_instructions' columns.
        strength (float): Strength parameter for the LLM model (0.0 to 1.0).
        temperature (float): Temperature parameter for the LLM model.
        code_directory (str): Path to the directory where code files are stored.
        language (str): Programming language of the code files.
        extension (str): File extension of the code files.
        budget (float): Maximum allowed total cost for the change process.

    Returns:
        Tuple[bool, List[Dict[str, str]], float, str]:
            - success (bool): Indicates if changes were successfully made within the budget and without errors.
            - list_of_jsons (List[Dict[str, str]]): List of dictionaries with 'file_name' and 'modified_prompt'.
            - total_cost (float): Total accumulated cost of all change attempts.
            - model_name (str): Name of the LLM model used.
    """
    list_of_jsons: List[Dict[str, str]] = []
    total_cost: float = 0.0
    model_name: str = ""
    success: bool = False
    any_failures: bool = False  # Track if any failures occur

    # Validate inputs
    if not os.path.isfile(csv_file):
        console.print(f"[bold red]Error:[/bold red] CSV file '{csv_file}' does not exist.")
        return success, list_of_jsons, total_cost, model_name

    if not (0.0 <= strength <= 1.0):
        console.print(f"[bold red]Error:[/bold red] 'strength' must be between 0 and 1. Given: {strength}")
        return success, list_of_jsons, total_cost, model_name

    if not (0.0 <= temperature <= 1.0):
        console.print(f"[bold red]Error:[/bold red] 'temperature' must be between 0 and 1. Given: {temperature}")
        return success, list_of_jsons, total_cost, model_name

    code_dir_path = Path(code_directory)
    if not code_dir_path.is_dir():
        console.print(f"[bold red]Error:[/bold red] Code directory '{code_directory}' does not exist or is not a directory.")
        return success, list_of_jsons, total_cost, model_name

    try:
        with open(csv_file, mode='r', newline='', encoding='utf-8') as csvfile:
            reader = csv.DictReader(csvfile)
            if 'prompt_name' not in reader.fieldnames or 'change_instructions' not in reader.fieldnames:
                console.print("[bold red]Error:[/bold red] CSV file must contain 'prompt_name' and 'change_instructions' columns.")
                return success, list_of_jsons, total_cost, model_name

            for row_number, row in enumerate(reader, start=1):
                prompt_name = row.get('prompt_name', '').strip()
                change_instructions = row.get('change_instructions', '').strip()

                if not prompt_name:
                    console.print(f"[yellow]Warning:[/yellow] Missing 'prompt_name' in row {row_number}. Skipping.")
                    any_failures = True
                    continue

                if not change_instructions:
                    console.print(f"[yellow]Warning:[/yellow] Missing 'change_instructions' in row {row_number}. Skipping.")
                    any_failures = True
                    continue

                # Parse the prompt_name to get the input_code filename
                try:
                    prompt_path = Path(prompt_name)
                    base_name = prompt_path.stem  # Removes suffix
                    # Remove the '_<language>' part if present
                    if '_' in base_name:
                        base_name = base_name.rsplit('_', 1)[0]
                    input_code_name = f"{base_name}{extension}"
                    input_code_path = code_dir_path / input_code_name

                    if not input_code_path.is_file():
                        console.print(f"[yellow]Warning:[/yellow] Input code file '{input_code_path}' does not exist. Skipping row {row_number}.")
                        logger.warning(f"Input code file '{input_code_path}' does not exist for row {row_number}")
                        any_failures = True
                        continue

                    # Check if prompt file exists
                    if not prompt_path.is_file():
                        console.print(f"[yellow]Warning:[/yellow] Prompt file '{prompt_name}' does not exist. Skipping row {row_number}.")
                        logger.warning(f"Prompt file '{prompt_name}' does not exist for row {row_number}")
                        any_failures = True
                        continue

                    # Read the input_code from the file
                    with open(input_code_path, 'r', encoding='utf-8') as code_file:
                        input_code = code_file.read()

                    # Read the input_prompt from the prompt file
                    with open(prompt_path, 'r', encoding='utf-8') as prompt_file:
                        input_prompt = prompt_file.read()

                    # Call the change function
                    modified_prompt, cost, current_model_name = change(
                        input_prompt=input_prompt,
                        input_code=input_code,
                        change_prompt=change_instructions,
                        strength=strength,
                        temperature=temperature
                    )

                    # Accumulate the total cost
                    total_cost += cost

                    # Check if budget is exceeded
                    if total_cost > budget:
                        console.print(f"[bold red]Budget exceeded after row {row_number}. Stopping further processing.[/bold red]")
                        any_failures = True
                        break

                    # Set the model_name (assumes all calls use the same model)
                    if not model_name:
                        model_name = current_model_name
                    elif model_name != current_model_name:
                        console.print(f"[yellow]Warning:[/yellow] Model name changed from '{model_name}' to '{current_model_name}' in row {row_number}.")

                    # Add to the list_of_jsons
                    list_of_jsons.append({
                        "file_name": prompt_name,
                        "modified_prompt": modified_prompt
                    })

                    console.print(Panel(f"[green]Row {row_number} processed successfully.[/green]"))

                except Exception as e:
                    console.print(f"[red]Error:[/red] Failed to process 'prompt_name' in row {row_number}: {str(e)}")
                    logger.exception(f"Failed to process row {row_number}")
                    any_failures = True
                    continue

        # Determine success based on whether total_cost is within budget and no failures occurred
        success = (total_cost <= budget) and not any_failures

        # Pretty print the results
        console.print(Panel(f"[bold]Processing Complete[/bold]\n"
                           f"Success: {'Yes' if success else 'No'}\n"
                           f"Total Cost: ${total_cost:.6f}\n"
                           f"Model Used: {model_name if model_name else 'N/A'}"))

        # Optionally, pretty print the list of modified prompts
        if list_of_jsons:
            console.print(Panel("[bold]List of Modified Prompts[/bold]"))
            console.print(Pretty(list_of_jsons))

        return success, list_of_jsons, total_cost, model_name

    except Exception as e:
        console.print(f"[bold red]Unexpected Error:[/bold red] {str(e)}")
        logger.exception("Unexpected error occurred")
        return success, list_of_jsons, total_cost, model_name
