from typing import Optional, Tuple
from datetime import datetime, UTC
from io import StringIO
import os
import glob
import csv

from pydantic import BaseModel, Field
from rich import print
from rich.progress import track

from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke

class FileSummary(BaseModel):
    file_summary: str = Field(description="The summary of the file")

def validate_csv_format(csv_content: str) -> bool:
    """Validate CSV has required columns and proper format."""
    try:
        # Check if content is empty or just whitespace
        if not csv_content or csv_content.isspace():
            return False
            
        # Try parsing as CSV
        reader = csv.DictReader(StringIO(csv_content.lstrip()))
        
        # Check for required columns
        if not reader.fieldnames:
            return False
            
        required_columns = {'full_path', 'file_summary', 'date'}
        if not all(col in reader.fieldnames for col in required_columns):
            return False
            
        # Validate at least one row can be parsed
        try:
            first_row = next(reader, None)
            if not first_row:
                return True  # Empty CSV with valid headers is OK
            return all(key in first_row for key in required_columns)
        except csv.Error:
            return False
            
    except Exception:
        return False

def normalize_path(path: str) -> str:
    """Normalize path for consistent comparison."""
    return os.path.normpath(path.strip().strip('"').strip())

def parse_date(date_str: str) -> datetime:
    """Parse date string to datetime with proper error handling."""
    try:
        dt = datetime.fromisoformat(date_str.strip())
        return dt if dt.tzinfo else dt.replace(tzinfo=UTC)
    except Exception:
        return datetime.now(UTC)

def parse_existing_csv(csv_content: str, verbose: bool = False) -> dict:
    """Parse existing CSV file and return normalized data."""
    existing_data = {}
    try:
        # Handle different line endings and remove BOM
        cleaned_content = csv_content.lstrip('\ufeff').replace('\r\n', '\n')
        reader = csv.DictReader(StringIO(cleaned_content))
        
        for row in reader:
            try:
                normalized_path = normalize_path(row['full_path'])
                existing_data[normalized_path] = {
                    'file_summary': row['file_summary'].strip().strip('"'),
                    'date': row['date'].strip()
                }
                if verbose:
                    print(f"[green]Parsed existing entry for: {normalized_path}[/green]")
            except Exception as e:
                if verbose:
                    print(f"[yellow]Warning: Skipping invalid CSV row: {str(e)}[/yellow]")
    except Exception as e:
        if verbose:
            print(f"[yellow]Warning: Error parsing CSV: {str(e)}[/yellow]")
        raise ValueError("Invalid CSV file format.")
    return existing_data

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
            raise ValueError("Invalid 'directory_path'.")
        if not (0.0 <= strength <= 1.0):
            raise ValueError("Invalid 'strength' value.")
        if not isinstance(temperature, (int, float)) or temperature < 0:
            raise ValueError("Invalid 'temperature' value.")
        if not isinstance(verbose, bool):
            raise ValueError("Invalid 'verbose' value.")

        # Load Prompt Template
        prompt_template = load_prompt_template("summarize_file_LLM")
        if not prompt_template:
            raise FileNotFoundError("Prompt template 'summarize_file_LLM.prompt' not found.")

        # Initialize output
        csv_output = "full_path,file_summary,date\n"
        total_cost = 0.0
        model_name = "None"
        
        # Parse existing CSV if provided
        existing_data = {}
        if csv_file:
            if not validate_csv_format(csv_file):
                raise ValueError("Invalid CSV file format.")
            existing_data = parse_existing_csv(csv_file, verbose)

        # Get files
        files = glob.glob(directory_path, recursive=True)
        if not files:
            if verbose:
                print("[yellow]No files found.[/yellow]")
            return csv_output, total_cost, model_name

        # Process files
        for file_path in track(files, description="Processing files..."):
            try:
                relative_path = os.path.relpath(file_path)
                normalized_path = normalize_path(relative_path)
                file_mod_time = os.path.getmtime(file_path)
                date_generated = datetime.now(UTC).isoformat()

                needs_summary = True
                if normalized_path in existing_data:
                    try:
                        existing_entry = existing_data[normalized_path]
                        existing_date = parse_date(existing_entry['date'])
                        file_date = datetime.fromtimestamp(file_mod_time, UTC)
                        
                        if file_date <= existing_date:
                            needs_summary = False
                            file_summary = existing_entry['file_summary']
                            date_generated = existing_entry['date']
                            if verbose:
                                print(f"[green]Reusing existing summary for: {normalized_path}[/green]")
                        else:
                            if verbose:
                                print(f"[blue]File modified, generating new summary for: {normalized_path}[/blue]")
                    except Exception as e:
                        if verbose:
                            print(f"[yellow]Warning: Error comparing dates for {normalized_path}: {str(e)}[/yellow]")

                if needs_summary:
                    if verbose:
                        print(f"[blue]Generating new summary for: {normalized_path}[/blue]")
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
                        file_summary = "Error in summarization."
                        if verbose:
                            print(f"[red]Error summarizing file '{normalized_path}': {response['error']}[/red]")
                    else:
                        file_summary = response['result'].file_summary
                        total_cost += response.get('cost', 0.0)
                        model_name = response.get('model_name', model_name)

                csv_output += f'"{relative_path}","{file_summary.replace(chr(34), "")}",{date_generated}\n'

            except Exception as e:
                if verbose:
                    print(f"[red]Error processing file '{file_path}': {str(e)}[/red]")
                date_generated = datetime.now(UTC).isoformat()
                csv_output += f'"{relative_path}","Error processing file",{date_generated}\n'

        return csv_output, total_cost, model_name

    except Exception as e:
        print(f"[red]An error occurred: {str(e)}[/red]")
        raise