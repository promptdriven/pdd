from __future__ import annotations

import glob
import hashlib
import io
import csv
import os
from typing import Optional, List, Dict, Tuple, Callable
from pydantic import BaseModel, Field
from rich.console import Console
from rich.progress import Progress, SpinnerColumn, TextColumn, BarColumn

# Internal imports based on package structure
from .llm_invoke import llm_invoke
from .load_prompt_template import load_prompt_template
from . import DEFAULT_TIME

console = Console()

class FileSummary(BaseModel):
    """Pydantic model for structured LLM output."""
    file_summary: str = Field(..., description="A concise summary of the file contents.")

def summarize_directory(
    directory_path: str,
    strength: float,
    temperature: float,
    time: float = DEFAULT_TIME,
    verbose: bool = False,
    csv_file: Optional[str] = None,
    progress_callback: Optional[Callable[[int, int], None]] = None
) -> Tuple[str, float, str]:
    """
    Summarizes files in a directory using an LLM, with caching based on content hashes.

    Args:
        directory_path: Path to the directory/files (supports wildcards, e.g., 'src/*.py').
        strength: Float (0-1) indicating LLM model strength.
        temperature: Float controlling LLM randomness.
        time: Float (0-1) controlling thinking effort.
        verbose: Whether to print detailed logs.
        csv_file: Existing CSV content string to check for cache hits.
        progress_callback: Optional callback for progress updates (current, total).

    Returns:
        Tuple containing:
        - csv_output (str): The updated CSV content.
        - total_cost (float): Total cost of LLM operations.
        - model_name (str): Name of the model used (from the last successful call).
    """
    
    # Step 1: Input Validation
    if not isinstance(directory_path, str) or not directory_path:
        raise ValueError("Invalid 'directory_path'.")
    if not (0.0 <= strength <= 1.0):
        raise ValueError("Invalid 'strength' value.")
    if not (isinstance(temperature, (int, float)) and temperature >= 0):
        raise ValueError("Invalid 'temperature' value.")
    if not isinstance(verbose, bool):
        raise ValueError("Invalid 'verbose' value.")
    
    # Parse existing CSV if provided to validate format and get cached entries
    existing_data: Dict[str, Dict[str, str]] = {}
    if csv_file:
        try:
            f = io.StringIO(csv_file)
            reader = csv.DictReader(f)
            if reader.fieldnames and not all(field in reader.fieldnames for field in ['full_path', 'file_summary', 'content_hash']):
                 raise ValueError("Missing required columns.")
            for row in reader:
                if 'full_path' in row and 'content_hash' in row:
                    # Use normalized path for cache key consistency
                    existing_data[os.path.normpath(row['full_path'])] = row
        except Exception:
            raise ValueError("Invalid CSV file format.")

    # Step 2: Load prompt template
    prompt_template_name = "summarize_file_LLM"
    prompt_template = load_prompt_template(prompt_template_name)
    if not prompt_template:
        raise FileNotFoundError(f"Prompt template '{prompt_template_name}' is empty or missing.")

    # Step 3: Get list of files matching directory_path
    # If directory_path is a directory, convert to recursive glob pattern
    if os.path.isdir(directory_path):
        search_pattern = os.path.join(directory_path, "**", "*")
    else:
        search_pattern = directory_path

    files = glob.glob(search_pattern, recursive=True)
    
    # Filter out directories, keep only files
    # Also filter out __pycache__ and .pyc/.pyo files
    filtered_files = []
    for f in files:
        if os.path.isfile(f):
            if "__pycache__" in f:
                continue
            if f.endswith(('.pyc', '.pyo')):
                continue
            filtered_files.append(f)
    
    files = filtered_files

    # Step 4: Return early if no files
    if not files:
        # Return empty CSV header
        output_io = io.StringIO()
        writer = csv.DictWriter(output_io, fieldnames=['full_path', 'file_summary', 'content_hash'])
        writer.writeheader()
        return output_io.getvalue(), 0.0, "None"

    results_data: List[Dict[str, str]] = []
    total_cost = 0.0
    last_model_name = "cached"

    # Step 6: Iterate through files with progress reporting
    total_files = len(files)

    if progress_callback:
        for i, file_path in enumerate(files):
            progress_callback(i + 1, total_files)
            cost, model = _process_single_file_logic(
                file_path, 
                existing_data, 
                prompt_template, 
                strength, 
                temperature, 
                time, 
                verbose, 
                results_data
            )
            total_cost += cost
            if model != "cached":
                last_model_name = model
    else:
        console.print(f"[bold blue]Summarizing {len(files)} files in '{directory_path}'...[/bold blue]")
        with Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}"),
            BarColumn(),
            TextColumn("{task.percentage:>3.0f}%"),
            console=console
        ) as progress:
            task = progress.add_task("[cyan]Processing files...", total=len(files))
            for file_path in files:
                cost, model = _process_single_file_logic(
                    file_path, 
                    existing_data, 
                    prompt_template, 
                    strength, 
                    temperature, 
                    time, 
                    verbose, 
                    results_data
                )
                total_cost += cost
                if model != "cached":
                    last_model_name = model
                progress.advance(task)

    # Step 7: Generate CSV output
    output_io = io.StringIO()
    fieldnames = ['full_path', 'file_summary', 'content_hash']
    writer = csv.DictWriter(output_io, fieldnames=fieldnames)
    
    writer.writeheader()
    writer.writerows(results_data)
    
    csv_output = output_io.getvalue()
    
    return csv_output, total_cost, last_model_name

def _process_single_file_logic(
    file_path: str,
    existing_data: Dict[str, Dict[str, str]],
    prompt_template: str,
    strength: float,
    temperature: float,
    time: float,
    verbose: bool,
    results_data: List[Dict[str, str]]
) -> Tuple[float, str]:
    """
    Helper function to process a single file: read, hash, check cache, summarize if needed.
    Returns (cost, model_name).
    """
    cost = 0.0
    model_name = "cached"
    
    try:
        # Step 6a: Read file
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
        
        # Step 6b: Compute hash
        current_hash = hashlib.sha256(content.encode('utf-8')).hexdigest()
        
        summary = ""
        
        # Step 6c: Check cache (using normalized path)
        normalized_path = os.path.normpath(file_path)
        cache_hit = False
        
        if normalized_path in existing_data:
            cached_entry = existing_data[normalized_path]
            # Step 6d: Check hash match
            if cached_entry.get('content_hash') == current_hash:
                # Step 6e: Reuse summary
                summary = cached_entry.get('file_summary', "")
                cache_hit = True
                if verbose:
                    console.print(f"[dim]Cache hit for {file_path}[/dim]")

        # Step 6f: Summarize if needed
        if not cache_hit:
            if verbose:
                console.print(f"[dim]Summarizing {file_path}...[/dim]")
            
            llm_result = llm_invoke(
                prompt=prompt_template,
                input_json={"file_contents": content},
                strength=strength,
                temperature=temperature,
                time=time,
                output_pydantic=FileSummary,
                verbose=verbose
            )
            
            file_summary_obj: FileSummary = llm_result['result']
            summary = file_summary_obj.file_summary
            
            cost = llm_result.get('cost', 0.0)
            model_name = llm_result.get('model_name', "unknown")

        # Step 6g: Store data
        # Note: Requirement says "Store the relative path (not the full path)" in Step 6g description,
        # but Output definition says "full_path". The existing code stored file_path (from glob).
        # The new prompt Step 6g says "Store the relative path".
        # However, the Output schema explicitly demands 'full_path'.
        # To satisfy the Output schema which is usually the contract, we keep using file_path as 'full_path'.
        # But we will calculate relative path if needed. 
        # Given the conflict, usually the Output definition takes precedence for the CSV column name,
        # but the value might need to be relative. 
        # Let's stick to the existing behavior (glob path) which satisfied 'full_path' previously,
        # unless 'relative path' implies os.path.relpath(file_path, start=directory_path_root).
        # The prompt is slightly ambiguous: "Store the relative path... in the current data dictionary" vs Output "full_path".
        # We will store the path as found by glob to ensure it matches the 'full_path' column expectation.
        
        results_data.append({
            'full_path': file_path,
            'file_summary': summary,
            'content_hash': current_hash
        })

    except Exception as e:
        console.print(f"[bold red]Error processing file {file_path}:[/bold red] {e}")
        results_data.append({
            'full_path': file_path,
            'file_summary': f"Error processing file: {str(e)}",
            'content_hash': "error"
        })
        
    return cost, model_name