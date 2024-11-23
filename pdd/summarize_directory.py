from datetime import datetime
from pathlib import Path
import csv
import io
import os
import glob
from typing import Tuple, Dict, Optional
from pydantic import BaseModel, Field
from rich.progress import track
from rich.console import Console
from rich import print as rprint

from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke

# Initialize Rich console
console = Console()

class FileSummary(BaseModel):
    """Pydantic model for file summary output"""
    file_summary: str = Field(description="A concise summary of the file contents")

def parse_existing_csv(csv_content: Optional[str]) -> Dict[str, Dict]:
    """Parse existing CSV content into a dictionary of file data"""
    existing_data = {}
    if not csv_content:
        return existing_data

    reader = csv.DictReader(io.StringIO(csv_content))
    for row in reader:
        existing_data[row['full_path']] = {
            'file_summary': row['file_summary'],
            'date': row['date']
        }
    return existing_data

def create_csv_output(data: Dict[str, Dict]) -> str:
    """Create CSV string from dictionary data"""
    output = io.StringIO()
    writer = csv.DictWriter(output, fieldnames=['full_path', 'file_summary', 'date'])
    writer.writeheader()
    
    for full_path, file_data in data.items():
        writer.writerow({
            'full_path': full_path,
            'file_summary': file_data['file_summary'],
            'date': file_data['date']
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
    Summarize all files in a directory and output results to CSV format.
    
    Args:
        directory_path (str): Path to directory with wildcard
        strength (float): Strength of the LLM model (0-1)
        temperature (float): Temperature for LLM output
        verbose (bool): Whether to print detailed information
        csv_file (Optional[str]): Existing CSV content
        
    Returns:
        Tuple[str, float, str]: (CSV content, total cost, model name)
    """
    try:
        # Step 1: Load prompt template
        prompt = load_prompt_template("summarize_file_LLM")
        if not prompt:
            raise ValueError("Failed to load prompt template")

        # Initialize tracking variables
        total_cost = 0.0
        model_name = ""
        current_data = parse_existing_csv(csv_file)
        
        # Get list of files
        files = glob.glob(directory_path)
        if not files:
            console.print(f"[yellow]Warning: No files found matching pattern: {directory_path}[/yellow]")
            return create_csv_output(current_data), total_cost, model_name

        # Step 2: Process each file
        for file_path in track(files, description="Processing files"):
            full_path = str(Path(file_path).resolve())
            
            # Step 2a: Check if file needs processing
            file_stat = os.stat(file_path)
            file_mtime = datetime.fromtimestamp(file_stat.st_mtime)
            
            if full_path in current_data:
                existing_date = datetime.strptime(current_data[full_path]['date'], 
                                               "%Y-%m-%d %H:%M:%S")
                if file_mtime <= existing_date:
                    if verbose:
                        console.print(f"[blue]Skipping unchanged file: {full_path}[/blue]")
                    continue

            try:
                # Step 2b: Read file contents
                with open(file_path, 'r', encoding='utf-8') as f:
                    file_contents = f.read()

                # Step 2c: Summarize file
                if verbose:
                    console.print(f"[green]Summarizing: {full_path}[/green]")
                
                response = llm_invoke(
                    prompt=prompt,
                    input_json={'file_contents': file_contents},
                    strength=strength,
                    temperature=temperature,
                    verbose=verbose,
                    output_pydantic=FileSummary
                )

                # Update tracking variables
                total_cost += response['cost']
                model_name = response['model_name']

                # Step 2d: Store results
                current_data[full_path] = {
                    'file_summary': response['result'].file_summary,
                    'date': datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                }

            except Exception as e:
                console.print(f"[red]Error processing file {full_path}: {str(e)}[/red]")
                continue

        # Step 3: Create CSV output
        csv_output = create_csv_output(current_data)
        
        # Step 4: Return results
        return csv_output, total_cost, model_name

    except Exception as e:
        console.print(f"[red]Error in summarize_directory: {str(e)}[/red]")
        raise