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
    file_summary: str = Field(description="A concise summary of the file contents")

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
    writer = csv.writer(output, lineterminator='\r\n')  # Use Windows-style line endings
    writer.writerow(['full_path', 'file_summary', 'date'])
    
    for full_path, info in sorted(data.items()):
        writer.writerow([
            full_path,
            info['file_summary'],
            info['date'].isoformat()
        ])
    
    return output.getvalue()

def create_empty_csv() -> str:
    """Create empty CSV with header."""
    return "full_path,file_summary,date\r\n"

def read_prompt_template(prompt_path: Path) -> str:
    """Read prompt template with specific error handling."""
    try:
        with open(prompt_path, 'r') as f:
            return f.read().strip()
    except Exception as e:
        console.print(f"[red]Error reading prompt file: {str(e)}[/red]")
        raise

def summarize_directory(
    directory_path: str,
    strength: float,
    temperature: float,
    verbose: bool = False,
    csv_file: Optional[str] = None
) -> Tuple[str, float, str]:
    """
    Summarize files in a directory and output results to a CSV string.
    """
    # Validate parameters
    if not 0 <= strength <= 1:
        raise ValueError("Strength must be between 0 and 1")
    if not 0 <= temperature <= 1:
        raise ValueError("Temperature must be between 0 and 1")

    # Step 1: Get PDD_PATH
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise ValueError("PDD_PATH environment variable not set")

    # Step 2: Create prompt template
    prompt_path = Path(pdd_path) / "prompts" / "summarize_file_LLM.prompt"
    if not prompt_path.exists():
        raise FileNotFoundError(f"Prompt file not found: {prompt_path}")

    try:
        prompt_template = read_prompt_template(prompt_path)
    except Exception as e:
        console.print(f"[red]Error reading prompt file: {str(e)}[/red]")
        return create_empty_csv(), 0.0, ""

    # Initialize tracking variables
    total_cost = 0.0
    model_name = ""
    existing_data = read_existing_csv(csv_file)
    current_data = {}

    # Get list of files
    files = glob.glob(directory_path)
    if not files:
        console.print(f"[yellow]Warning: No files found matching pattern: {directory_path}[/yellow]")
        return create_empty_csv(), 0.0, ""

    # Step 3: Process files
    with Progress(
        SpinnerColumn(),
        TextColumn("[progress.description]{task.description}"),
        console=console
    ) as progress:
        task = progress.add_task("Processing files...", total=len(files))

        for file_path in files:
            try:
                full_path = str(Path(file_path).resolve())
                file_stat = os.stat(file_path)
                file_mtime = datetime.fromtimestamp(file_stat.st_mtime)

                file_name = os.path.basename(full_path)
                matching_path = next((path for path in existing_data if os.path.basename(path) == file_name), None)

                if matching_path and file_mtime <= existing_data[matching_path]['date']:
                    current_data[full_path] = {
                        'file_summary': existing_data[matching_path]['file_summary'],
                        'date': existing_data[matching_path]['date']
                    }
                    progress.advance(task)
                    continue

                try:
                    with open(file_path, 'r', encoding='utf-8') as f:
                        file_contents = f.read()
                except Exception as e:
                    console.print(f"[red]Error reading file {file_path}: {str(e)}[/red]")
                    progress.advance(task)
                    continue

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

                    if not isinstance(response, dict):
                        raise ValueError(f"Invalid LLM response format: {response}")

                    result = response.get('result')
                    if not result or not hasattr(result, 'file_summary'):
                        raise ValueError(f"Invalid LLM result format: {result}")

                    total_cost += response.get('cost', 0.0)
                    model_name = response.get('model_name', '')
                    
                    current_data[full_path] = {
                        'file_summary': result.file_summary,
                        'date': datetime.now()
                    }

                except Exception as e:
                    console.print(f"[red]Error processing {file_path}: {str(e)}[/red]")
                    continue

            except Exception as e:
                console.print(f"[red]Error processing {file_path}: {str(e)}[/red]")
                continue

            finally:
                progress.advance(task)

    # Step 4: Create final CSV output
    if not current_data:
        return create_empty_csv(), total_cost, model_name
        
    return create_csv_output(current_data), total_cost, model_name
