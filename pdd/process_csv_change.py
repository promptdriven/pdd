import csv
import os
from typing import List, Dict, Tuple
from rich.console import Console
from .change import change

console = Console()

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
    Process a CSV file and apply changes to code files based on instructions.

    Args:
        csv_file (str): Path to the CSV file.
        strength (float): Strength parameter for the LLM (0.0 to 1.0).
        temperature (float): Temperature parameter for the LLM (0.0 to 1.0).
        code_directory (str): Path to the directory containing code files.
        language (str): Programming language of the code files.
        extension (str): File extension of the code files.
        budget (float): Maximum allowed cost for the change process.

    Returns:
        Tuple[bool, List[Dict[str, str]], float, str]: 
            - Success status
            - List of dictionaries containing file names and modified prompts
            - Total cost of all fix attempts
            - Name of the LLM model used
    """
    success = True
    list_of_jsons = []
    total_cost = 0.0
    model_name = ""

    try:
        with open(csv_file, 'r') as file:
            csv_reader = csv.DictReader(file)
            
            for row in csv_reader:
                prompt_name = row.get('prompt_name')
                change_instructions = row.get('change_instructions')

                if not prompt_name or not change_instructions:
                    console.print(f"[yellow]Warning: Missing data in CSV row. Skipping.[/yellow]")
                    continue

                # Parse the prompt_name into an input_code name
                input_code_name = prompt_name.replace(f"_{language}.prompt", f"{extension}")
                input_code_path = os.path.join(code_directory, input_code_name)

                # Read the input prompt and code
                try:
                    with open(os.path.join(code_directory, prompt_name), 'r') as prompt_file:
                        input_prompt = prompt_file.read()

                    with open(input_code_path, 'r') as code_file:
                        input_code = code_file.read()
                except FileNotFoundError as e:
                    console.print(f"[red]Error: File not found - {e.filename}[/red]")
                    success = False
                    continue

                try:
                    modified_prompt, cost, model = change(
                        input_prompt, input_code, change_instructions, strength, temperature
                    )
                    total_cost += cost
                    model_name = model  # Update the model name

                    if total_cost > budget:
                        console.print(f"[yellow]Warning: Budget exceeded. Stopping process.[/yellow]")
                        break

                    list_of_jsons.append({input_code_name: modified_prompt})
                except Exception as e:
                    console.print(f"[red]Error during change process: {str(e)}[/red]")
                    success = False

    except FileNotFoundError:
        console.print(f"[red]Error: CSV file '{csv_file}' not found.[/red]")
        success = False
    except csv.Error as e:
        console.print(f"[red]Error reading CSV file: {str(e)}[/red]")
        success = False
    except Exception as e:
        console.print(f"[red]Unexpected error: {str(e)}[/red]")
        success = False

    return success, list_of_jsons, total_cost, model_name
