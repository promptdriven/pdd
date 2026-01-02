from typing import Callable, Optional, Tuple
from datetime import datetime
try:
    from datetime import UTC
except ImportError:
    # Python < 3.11 compatibility
    from datetime import timezone
    UTC = timezone.utc
from io import StringIO
import os
import glob
import csv

from pydantic import BaseModel, Field
from rich import print
from rich.progress import track

from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke
from . import DEFAULT_TIME

class FileSummary(BaseModel):
    file_summary: str = Field(description="The summary of the file")

def validate_csv_format(csv_content: str) -> bool:
    """Validate CSV has required columns and proper format."""
    try:
        if not csv_content or csv_content.isspace():
            return False
        reader = csv.DictReader(StringIO(csv_content.lstrip()))
        if not reader.fieldnames:
            return False
        required_columns = {'full_path', 'file_summary', 'date'}
        if not all(col in reader.fieldnames for col in required_columns):
            return False
        try:
            first_row = next(reader, None)
            if not first_row:
                return True
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
        # Clean the CSV content by removing leading/trailing whitespace from each line
        cleaned_lines = [line.strip() for line in csv_content.splitlines()]
        cleaned_content = '\n'.join(cleaned_lines)
        
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
    time: float = DEFAULT_TIME,
    csv_file: Optional[str] = None,
    progress_callback: Optional[Callable[[int, int], None]] = None
) -> Tuple[str, float, str]:
    """
    Summarize files in a directory and generate a CSV containing the summaries.

    Parameters:
        directory_path (str): Path to the directory to summarize with wildcard (e.g., /path/to/directory/*.py)
        strength (float): Between 0 and 1 that is the strength of the LLM model to use.
        temperature (float): Controls the randomness of the LLM's output.
        verbose (bool): Whether to print out the details of the function.
        time (float): Time budget for LLM calls.
        csv_file (Optional[str]): Current CSV file contents if it already exists.
        progress_callback (Optional[Callable[[int, int], None]]): Callback for progress updates.
            Called with (current, total) for each file processed. Used by TUI ProgressBar.

    Returns:
        Tuple[str, float, str]: A tuple containing:
            - csv_output (str): Updated CSV content with 'full_path', 'file_summary', and 'date'.
            - total_cost (float): Total cost of the LLM runs.
            - model_name (str): Name of the LLM model used.
    """
    try:
        if not isinstance(directory_path, str) or not directory_path:
            raise ValueError("Invalid 'directory_path'.")
        if not (0.0 <= strength <= 1.0):
            raise ValueError("Invalid 'strength' value.")
        if not isinstance(temperature, (int, float)) or temperature < 0:
            raise ValueError("Invalid 'temperature' value.")
        if not isinstance(verbose, bool):
            raise ValueError("Invalid 'verbose' value.")

        prompt_template = load_prompt_template("summarize_file_LLM")
        if not prompt_template:
            raise FileNotFoundError("Prompt template 'summarize_file_LLM.prompt' not found.")

        csv_output = "full_path,file_summary,date\n"
        total_cost = 0.0
        model_name = "None"

        existing_data = {}
        if csv_file:
            if not validate_csv_format(csv_file):
                raise ValueError("Invalid CSV file format.")
            existing_data = parse_existing_csv(csv_file, verbose)

        # Expand directory_path: support plain directories or glob patterns
        try:
            normalized_input = normalize_path(directory_path)
        except Exception:
            normalized_input = directory_path

        if os.path.isdir(normalized_input):
            # Recursively include all files under the directory
            search_pattern = os.path.join(normalized_input, "**", "*")
        else:
            # Treat as a glob pattern (may be a single file path too)
            search_pattern = directory_path

        # Get list of files first to ensure consistent order
        all_files = sorted(glob.glob(search_pattern, recursive=True))
        if not all_files:
            if verbose:
                print("[yellow]No files found.[/yellow]")
            return csv_output, total_cost, model_name

        # Pre-filter to get only processable files (for accurate progress count)
        files = [
            f for f in all_files
            if not os.path.isdir(f)
            and '__pycache__' not in f
            and not f.endswith(('.pyc', '.pyo'))
        ]

        if not files:
            if verbose:
                print("[yellow]No processable files found.[/yellow]")
            return csv_output, total_cost, model_name

        # Get all modification times at once to ensure consistent order
        file_mod_times = {f: os.path.getmtime(f) for f in files}

        # Determine iteration method: use callback if provided, else track()
        # Disable track() when in TUI context (COLUMNS env var set) or callback provided
        total_files = len(files)
        use_track = progress_callback is None and "COLUMNS" not in os.environ

        if use_track:
            file_iterator = track(files, description="Processing files...")
        else:
            file_iterator = files

        for idx, file_path in enumerate(file_iterator):
            # Report progress if callback provided
            if progress_callback is not None:
                progress_callback(idx + 1, total_files)

            try:
                relative_path = os.path.relpath(file_path)
                normalized_path = normalize_path(relative_path)
                file_mod_time = file_mod_times[file_path]
                date_generated = datetime.now(UTC).isoformat()

                if verbose:
                    print(f"\nProcessing file: {normalized_path}")
                    print(f"Modification time: {datetime.fromtimestamp(file_mod_time, UTC)}")

                needs_summary = True
                if normalized_path in existing_data:
                    try:
                        existing_entry = existing_data[normalized_path]
                        existing_date = parse_date(existing_entry['date'])
                        file_date = datetime.fromtimestamp(file_mod_time, UTC)
                        
                        if verbose:
                            print(f"Existing date: {existing_date}")
                            print(f"File date: {file_date}")
                        
                        # Explicitly check if file is newer
                        if file_date > existing_date:
                            if verbose:
                                print(f"[blue]File modified, generating new summary[/blue]")
                            needs_summary = True
                        else:
                            needs_summary = False
                            file_summary = existing_entry['file_summary']
                            date_generated = existing_entry['date']
                            if verbose:
                                print(f"[green]Reusing existing summary[/green]")
                    except Exception as e:
                        if verbose:
                            print(f"[yellow]Warning: Date comparison error: {str(e)}[/yellow]")
                        needs_summary = True
                elif verbose:
                    print("[blue]New file, generating summary[/blue]")

                if needs_summary:
                    if verbose:
                        print(f"[blue]Generating summary for: {normalized_path}[/blue]")
                    with open(file_path, 'r', encoding='utf-8') as f:
                        file_contents = f.read()

                    input_params = {"file_contents": file_contents}
                    response = llm_invoke(
                        prompt=prompt_template,
                        input_json=input_params,
                        strength=strength,
                        temperature=temperature,
                        time=time,
                        verbose=verbose,
                        output_pydantic=FileSummary
                    )

                    if response.get('error'):
                        file_summary = "Error in summarization."
                        if verbose:
                            print(f"[red]Error summarizing file: {response['error']}[/red]")
                    else:
                        file_summary = response['result'].file_summary
                        total_cost += response.get('cost', 0.0)
                        model_name = response.get('model_name', model_name)

                csv_output += f'"{relative_path}","{file_summary.replace(chr(34), "")}",{date_generated}\n'

            except Exception as e:
                if verbose:
                    print(f"[red]Error processing file: {str(e)}[/red]")
                date_generated = datetime.now(UTC).isoformat()
                csv_output += f'"{relative_path}","Error processing file",{date_generated}\n'

        return csv_output, total_cost, model_name

    except Exception as e:
        print(f"[red]An error occurred: {str(e)}[/red]")
        raise
