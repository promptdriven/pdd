from typing import Optional, Tuple
from datetime import datetime
from io import StringIO
import os
import glob
import csv

from pydantic import BaseModel, Field
from rich import print
from rich.progress import track

# Relative imports for internal modules
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke


# Define a Pydantic model for structured file summary
class FileSummary(BaseModel):
    file_summary: str = Field(description="The summary of the file")

def summarize_directory(
    directory_path: str,
    strength: float,
    temperature: float,
    verbose: bool,
    csv_file: Optional[str] = None
) -> Tuple[str, float, str]:
    """
    Summarize files in a directory and generate a CSV containing the summaries.

    Parameters:
        directory_path (str): Path to the directory to summarize with wildcard (e.g., /path/to/directory/*.py)
        strength (float): Between 0 and 1 that is the strength of the LLM model to use.
        temperature (float): Controls the randomness of the LLM's output.
        verbose (bool): Whether to print out the details of the function.
        csv_file (Optional[str]): Current CSV file contents if it already exists.

    Returns:
        Tuple[str, float, str]: A tuple containing:
            - csv_output (str): Updated CSV content with 'full_path', 'file_summary', and 'date'.
            - total_cost (float): Total cost of the LLM runs.
            - model_name (str): Name of the LLM model used.
    """
    try:
        # Input Validation
        if not isinstance(directory_path, str) or not directory_path:
            print("[red]Error: 'directory_path' must be a non-empty string.[/red]")
            raise ValueError("Invalid 'directory_path'.")

        if not (0.0 <= strength <= 1.0):
            print("[red]Error: 'strength' must be a float between 0 and 1.[/red]")
            raise ValueError("Invalid 'strength' value.")

        if not isinstance(temperature, (int, float)) or temperature < 0:
            print("[red]Error: 'temperature' must be a non-negative float.[/red]")
            raise ValueError("Invalid 'temperature' value.")

        if not isinstance(verbose, bool):
            print("[red]Error: 'verbose' must be a boolean.[/red]")
            raise ValueError("Invalid 'verbose' value.")

        # Load Prompt Template
        prompt_template = load_prompt_template("summarize_file_LLM")
        if not prompt_template:
            print("[red]Error: Failed to load the prompt template 'summarize_file_LLM.prompt'.[/red]")
            raise FileNotFoundError("Prompt template 'summarize_file_LLM.prompt' not found.")

        if verbose:
            print(f"[green]Loaded prompt template 'summarize_file_LLM.prompt'.[/green]")

        # Retrieve list of files
        files = glob.glob(directory_path, recursive=True)
        if not files:
            print("[yellow]Warning: No files found matching the provided 'directory_path'.[/yellow]")
            # Return empty CSV content with current timestamp
            current_time = datetime.utcnow().isoformat()
            csv_output = "full_path,file_summary,date\n"
            return csv_output, 0.0, "None"

        if verbose:
            print(f"[blue]Found {len(files)} file(s) to process.[/blue]")

        # Parse existing CSV content
        existing_data = {}
        if csv_file:
            try:
                csv_reader = csv.DictReader(StringIO(csv_file))
                for row in csv_reader:
                    existing_data[row['full_path']] = {
                        'file_summary': row['file_summary'],
                        'date': row['date']
                    }
                if verbose:
                    print(f"[green]Loaded existing CSV data with {len(existing_data)} entries.[/green]")
            except Exception as e:
                print(f"[red]Error parsing existing CSV file: {e}[/red]")
                raise ValueError("Invalid CSV file format.")

        # Initialize CSV output
        csv_output = "full_path,file_summary,date\n"
        total_cost = 0.0
        model_name = "None"

        # Iterate through files with progress bar
        for file_path in track(files, description="Processing files..."):
            try:
                relative_path = os.path.relpath(file_path)
                file_mod_time = os.path.getmtime(file_path)
                file_mod_datetime = datetime.fromtimestamp(file_mod_time).isoformat()

                # Check for existing summary
                if relative_path in existing_data:
                    existing_entry = existing_data[relative_path]
                    existing_date = existing_entry['date']
                    existing_datetime = datetime.fromisoformat(existing_date)
                    current_datetime = datetime.utcnow()

                    file_datetime = datetime.utcfromtimestamp(file_mod_time)

                    if file_datetime <= existing_datetime:
                        # Reuse existing summary
                        file_summary = existing_entry['file_summary']
                        date_generated = existing_entry['date']
                        if verbose:
                            print(f"[cyan]Reusing existing summary for '{relative_path}'.[/cyan]")
                    else:
                        # Need to re-summarize
                        if verbose:
                            print(f"[magenta]File '{relative_path}' has been modified. Generating new summary.[/magenta]")
                        with open(file_path, 'r', encoding='utf-8') as f:
                            file_contents = f.read()

                        input_params = {"file_contents": file_contents}
                        response = llm_invoke(
                            prompt=prompt_template,
                            input_json=input_params,
                            strength=strength,
                            temperature=temperature,
                            verbose=verbose,
                            output_pydantic=FileSummary
                        )

                        if response.get('error'):
                            print(f"[red]Error summarizing file '{relative_path}': {response['error']}[/red]")
                            file_summary = "Error in summarization."
                        else:
                            file_summary = response['result'].file_summary
                            total_cost += response.get('cost', 0.0)
                            model_name = response.get('model_name', model_name)
                            date_generated = datetime.utcnow().isoformat()
                            if verbose:
                                print(f"[green]Summary generated for '{relative_path}'.[/green]")

                        # Update existing data
                        existing_data[relative_path] = {
                            'file_summary': file_summary,
                            'date': date_generated
                        }
                else:
                    # New file, generate summary
                    if verbose:
                        print(f"[magenta]Generating summary for new file '{relative_path}'.[/magenta]")
                    with open(file_path, 'r', encoding='utf-8') as f:
                        file_contents = f.read()

                    input_params = {"file_contents": file_contents}
                    response = llm_invoke(
                        prompt=prompt_template,
                        input_json=input_params,
                        strength=strength,
                        temperature=temperature,
                        verbose=verbose,
                        output_pydantic=FileSummary
                    )

                    if response.get('error'):
                        print(f"[red]Error summarizing file '{relative_path}': {response['error']}[/red]")
                        file_summary = "Error in summarization."
                    else:
                        file_summary = response['result'].file_summary
                        total_cost += response.get('cost', 0.0)
                        model_name = response.get('model_name', model_name)
                        date_generated = datetime.utcnow().isoformat()
                        if verbose:
                            print(f"[green]Summary generated for '{relative_path}'.[/green]")

                    # Add to existing data
                    existing_data[relative_path] = {
                        'file_summary': file_summary,
                        'date': date_generated
                    }

                # Append to CSV output
                csv_output += f'"{relative_path}","{file_summary.replace(chr(34), "")}",{date_generated}\n'

            except Exception as e:
                print(f"[red]Unexpected error processing file '{file_path}': {e}[/red]")
                # Optionally, continue processing other files or raise the exception
                continue

        if verbose:
            print(f"[blue]Processing complete. Total cost: ${total_cost:.6f} using model '{model_name}'.[/blue]")

        return csv_output, total_cost, model_name

    except Exception as e:
        print(f"[red]An error occurred: {e}[/red]")
        raise