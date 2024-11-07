import os
import csv
import glob
from datetime import datetime
from typing import Tuple, Optional
from pathlib import Path
import io
from rich.console import Console
from rich.progress import Progress, SpinnerColumn, TextColumn
from pydantic import BaseModel, Field
from .llm_invoke import llm_invoke

console = Console()

class FileSummary(BaseModel):
    """Pydantic model for the file summary output."""
    summary: str = Field(description="A concise summary of the file contents")

def read_existing_csv(csv_file: str) -> dict:
    """Read existing CSV file into a dictionary with file paths as keys."""
    if not csv_file:
        return {}
    
    existing_data = {}
    reader = csv.DictReader(io.StringIO(csv_file))
    for row in reader:
        existing_data[row['full_path']] = {
            'file_summary': row['file_summary'],
            'date': datetime.fromisoformat(row['date'])
        }
    return existing_data

def create_csv_output(data: dict) -> str:
    """Create CSV string from the data dictionary."""
    output = io.StringIO()
    writer = csv.DictWriter(output, fieldnames=['full_path', 'file_summary', 'date'])
    writer.writeheader()
    
    for full_path, info in sorted(data.items()):
        writer.writerow({
            'full_path': full_path,
            'file_summary': info['file_summary'],
            'date': info['date'].isoformat()
        })
    
    return output.getvalue()

def summarize_directory(
    directory_path: str,
    strength: float,
    temperature: float,
    verbose: bool = False,
    csv_file: Optional[str] = None
) -> Tuple[str, float, str]:
    """
    Summarize files in a directory and output results to a CSV string.
    
    Args:
        directory_path (str): Path to directory with wildcard
        strength (float): Strength of the LLM model (0-1)
        temperature (float): Temperature for LLM output
        verbose (bool): Whether to print detailed information
        csv_file (Optional[str]): Existing CSV file contents
        
    Returns:
        Tuple[str, float, str]: CSV contents, total cost, and model name
    """
    try:
        # Step 1: Get PDD_PATH
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable not set")

        # Step 2: Create prompt template
        prompt_path = Path(pdd_path) / "prompts" / "summarize_file_LLM.prompt"
        if not prompt_path.exists():
            raise FileNotFoundError(f"Prompt file not found: {prompt_path}")

        with open(prompt_path, 'r') as f:
            prompt_template = f.read()

        # Initialize tracking variables
        total_cost = 0.0
        model_name = ""
        existing_data = read_existing_csv(csv_file)
        current_data = {}

        # Get list of files
        files = glob.glob(directory_path)
        if not files:
            console.print(f"[yellow]Warning: No files found matching pattern: {directory_path}[/yellow]")
            return create_csv_output({}), 0.0, ""

        # Step 3: Process files
        with Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}"),
            console=console
        ) as progress:
            task = progress.add_task("Processing files...", total=len(files))

            for file_path in files:
                full_path = str(Path(file_path).resolve())
                file_stat = os.stat(file_path)
                file_mtime = datetime.fromtimestamp(file_stat.st_mtime)

                # Step 3a: Check if file needs processing
                if full_path in existing_data:
                    if file_mtime <= existing_data[full_path]['date']:
                        current_data[full_path] = existing_data[full_path]
                        progress.advance(task)
                        continue

                # Step 3b: Read file contents
                try:
                    with open(file_path, 'r', encoding='utf-8') as f:
                        file_contents = f.read()
                except Exception as e:
                    console.print(f"[red]Error reading file {file_path}: {str(e)}[/red]")
                    progress.advance(task)
                    continue

                # Step 3c: Summarize file
                if verbose:
                    console.print(f"[blue]Summarizing: {file_path}[/blue]")

                try:
                    response = llm_invoke(
                        prompt=prompt_template,
                        input_json={'file_contents': file_contents},
                        strength=strength,
                        temperature=temperature,
                        verbose=verbose,
                        output_pydantic=FileSummary
                    )

                    total_cost += response['cost']
                    model_name = response['model_name']
                    
                    current_data[full_path] = {
                        'file_summary': response['result'].summary,
                        'date': datetime.now()
                    }

                except Exception as e:
                    console.print(f"[red]Error summarizing {file_path}: {str(e)}[/red]")
                    progress.advance(task)
                    continue

                progress.advance(task)

        # Step 4: Create final CSV output
        csv_output = create_csv_output(current_data)

        # Step 5: Return results
        return csv_output, total_cost, model_name

    except Exception as e:
        console.print(f"[red]Error in summarize_directory: {str(e)}[/red]")
        raise
