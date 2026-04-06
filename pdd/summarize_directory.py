from __future__ import annotations

import glob
import hashlib
import io
import csv
import os
import subprocess
import json
from typing import Optional, List, Dict, Tuple, Callable
from pydantic import BaseModel, Field
from rich.console import Console
from rich.progress import Progress, SpinnerColumn, TextColumn, BarColumn

# Internal imports based on package structure
from .llm_invoke import llm_invoke
from .load_prompt_template import load_prompt_template
from . import DEFAULT_TIME

console = Console()

# Binary extensions that can't be meaningfully summarized
BINARY_EXTENSIONS = {
    '.png', '.jpg', '.jpeg', '.gif', '.ico', '.webp', '.svg', '.bmp',
    '.mp4', '.webm', '.mov', '.avi', '.mp3', '.wav', '.ogg',
    '.zip', '.tar', '.gz', '.rar', '.7z',
    '.woff', '.woff2', '.ttf', '.eot', '.otf',
    '.pdf', '.exe', '.dll', '.so', '.dylib',
    '.pyc', '.pyo',  # Python bytecode
}


def _get_files_from_git(directory_path: str) -> Optional[List[str]]:
    """Get tracked files using git ls-files (respects .gitignore)."""
    try:
        abs_path = os.path.abspath(directory_path)

        # Determine the working directory and relative path for git
        if os.path.isdir(abs_path):
            cwd = abs_path
            git_path = '.'
        else:
            cwd = os.path.dirname(abs_path)
            git_path = os.path.basename(abs_path)

        result = subprocess.run(
            ['git', 'ls-files', git_path],
            capture_output=True,
            text=True,
            check=True,
            cwd=cwd,
            timeout=30
        )
        files = [f for f in result.stdout.strip().split('\n') if f]
        # Convert to absolute paths
        return [os.path.join(cwd, f) for f in files]
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, FileNotFoundError):
        return None  # Not a git repo or git not available


def _get_files_from_glob(directory_path: str) -> List[str]:
    """Fallback: get files using glob with basic filtering."""
    if os.path.isdir(directory_path):
        search_pattern = os.path.join(directory_path, "**", "*")
    else:
        search_pattern = directory_path

    files = glob.glob(search_pattern, recursive=True)

    # Basic directory filtering for non-git fallback
    ignore_dirs = {'node_modules', '.next', '__pycache__', '.git', 'dist', 'build', 'coverage'}

    filtered = []
    for f in files:
        if not os.path.isfile(f):
            continue
        if any(d in f.split(os.sep) for d in ignore_dirs):
            continue
        filtered.append(f)
    return filtered


class FileSummary(BaseModel):
    """Pydantic model for structured LLM output."""
    file_summary: str = Field(..., description="A concise summary of the file contents.")
    key_exports: List[str] = Field(..., description="List of the file's key public exports.")
    dependencies: List[str] = Field(..., description="List of the file's direct import dependencies.")

def _flush_csv_to_disk(results_data: List[Dict[str, str]], csv_path: str) -> None:
    """Write current results_data to disk as a complete CSV, preserving partial progress."""
    output_io = io.StringIO()
    fieldnames = ['full_path', 'file_summary', 'key_exports', 'dependencies', 'content_hash']
    writer = csv.DictWriter(output_io, fieldnames=fieldnames)
    writer.writeheader()
    writer.writerows(results_data)
    with open(csv_path, 'w', encoding='utf-8') as f:
        f.write(output_io.getvalue())


def summarize_directory(
    directory_path: str,
    strength: float,
    temperature: float,
    time: float = DEFAULT_TIME,
    verbose: bool = False,
    csv_file: Optional[str] = None,
    progress_callback: Optional[Callable[[int, int], None]] = None,
    include_docs: bool = False,
    max_workers: int = 1,
    csv_path: Optional[str] = None,
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
        include_docs: When True, also discover and summarize doc files (.md, .txt, .rst).
        max_workers: When > 1, parallelize LLM calls via ThreadPoolExecutor.
        csv_path: Optional file path to flush CSV results to disk after each file,
            so partial progress survives if the user interrupts mid-run.

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
                    # Default missing columns (old-format entries)
                    # Mark as backfilled so cache logic can force re-summarization
                    if 'key_exports' not in row or 'dependencies' not in row:
                        row.setdefault('key_exports', '[]')
                        row.setdefault('dependencies', '[]')
                        row['_backfilled'] = True
                    # Use normalized path for cache key consistency
                    existing_data[os.path.normpath(row['full_path'])] = row
        except Exception:
            raise ValueError("Invalid CSV file format.")

    # Step 2: Load prompt template
    prompt_template_name = "summarize_file_LLM"
    prompt_template = load_prompt_template(prompt_template_name)
    if not prompt_template:
        raise FileNotFoundError(f"Prompt template '{prompt_template_name}' is empty or missing.")

    # Step 3: Get list of files
    # Try git first (respects .gitignore), fall back to glob
    files = _get_files_from_git(directory_path)
    if files is None:
        files = _get_files_from_glob(directory_path)

    # Documentation extensions — included only when include_docs is True
    doc_extensions = {'.md', '.txt', '.rst'}

    # Filter out binary files and prompt files that can't be summarized
    filtered_files = []
    for f in files:
        if not os.path.isfile(f):
            continue
        _, ext = os.path.splitext(f)
        if ext.lower() in BINARY_EXTENSIONS:
            continue
        # Skip .prompt files — they are the consumers of dependencies, not
        # dependencies themselves.  Including them adds noise to auto-deps.
        if ext.lower() == '.prompt':
            continue
        # Skip doc files unless include_docs is True
        if not include_docs and ext.lower() in doc_extensions:
            continue
        filtered_files.append(f)

    files = filtered_files

    # Step 4: Return early if no files
    if not files:
        # No files discovered, but preserve any existing cached entries
        output_io = io.StringIO()
        fieldnames = ['full_path', 'file_summary', 'key_exports', 'dependencies', 'content_hash']
        writer = csv.DictWriter(output_io, fieldnames=fieldnames)
        writer.writeheader()
        for entry in existing_data.values():
            writer.writerow({k: entry.get(k, '') for k in fieldnames})
        return output_io.getvalue(), 0.0, "None"

    # Determine base directory for relative paths
    if os.path.isdir(directory_path):
        base_dir = os.path.abspath(directory_path)
    else:
        prefix = directory_path.split('*')[0]
        if os.path.isdir(prefix):
            base_dir = os.path.abspath(prefix)
        else:
            base_dir = os.path.abspath(os.path.dirname(prefix))

    results_data: List[Dict[str, str]] = []
    total_cost = 0.0
    last_model_name = "cached"

    # Step 6: Iterate through files with progress reporting
    total_files = len(files)

    def _process_file(i: int, file_path: str) -> Tuple[float, str]:
        """Process a single file and accumulate results."""
        rel_path = os.path.relpath(file_path, base_dir)
        return _process_single_file_logic(
            file_path,
            rel_path,
            existing_data,
            prompt_template,
            strength,
            temperature,
            time,
            verbose,
            results_data
        )

    if max_workers > 1:
        import threading
        from concurrent.futures import ThreadPoolExecutor, as_completed
        cost_lock = threading.Lock()

        def _threaded_process(i: int, file_path: str) -> Tuple[int, float, str]:
            """Thread-safe wrapper that returns index for ordering."""
            rel_path = os.path.relpath(file_path, base_dir)
            local_results: List[Dict[str, str]] = []
            cost, model = _process_single_file_logic(
                file_path,
                rel_path,
                existing_data,
                prompt_template,
                strength,
                temperature,
                time,
                verbose,
                local_results
            )
            return i, cost, model, local_results[0] if local_results else None

        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {
                executor.submit(_threaded_process, i, fp): i
                for i, fp in enumerate(files)
            }
            completed = 0
            for future in as_completed(futures):
                idx, cost, model, result_row = future.result()
                with cost_lock:
                    total_cost += cost
                    if model != "cached":
                        last_model_name = model
                    if result_row:
                        results_data.append(result_row)
                    if csv_path:
                        _flush_csv_to_disk(results_data, csv_path)
                completed += 1
                if progress_callback:
                    progress_callback(completed, total_files)
    elif progress_callback:
        for i, file_path in enumerate(files):
            progress_callback(i + 1, total_files)
            cost, model = _process_file(i, file_path)
            total_cost += cost
            if model != "cached":
                last_model_name = model
            if csv_path:
                _flush_csv_to_disk(results_data, csv_path)
    elif verbose:
        console.print(f"[bold blue]Summarizing {len(files)} files in '{directory_path}'...[/bold blue]")
        with Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}"),
            BarColumn(),
            TextColumn("{task.percentage:>3.0f}%"),
            console=console
        ) as progress:
            task = progress.add_task("[cyan]Processing files...", total=len(files))
            for i, file_path in enumerate(files):
                cost, model = _process_file(i, file_path)
                total_cost += cost
                if model != "cached":
                    last_model_name = model
                if csv_path:
                    _flush_csv_to_disk(results_data, csv_path)
                progress.advance(task)
    else:
        for i, file_path in enumerate(files):
            cost, model = _process_file(i, file_path)
            total_cost += cost
            if model != "cached":
                last_model_name = model
            if csv_path:
                _flush_csv_to_disk(results_data, csv_path)

    # Step 7: Merge in existing entries that were not part of this scan.
    # This preserves cached summaries for files outside the current
    # directory_path / glob scope so they are not silently dropped.
    scanned_paths = set()
    for row in results_data:
        scanned_paths.add(os.path.normpath(row['full_path']))
        # Also track the absolute version so entries keyed by absolute path
        # are recognized as already present when the scan wrote a relative path.
        abs_candidate = os.path.normpath(os.path.join(base_dir, row['full_path']))
        scanned_paths.add(abs_candidate)
    fieldnames = ['full_path', 'file_summary', 'key_exports', 'dependencies', 'content_hash']
    for norm_path, entry in existing_data.items():
        if norm_path not in scanned_paths:
            results_data.append({k: entry.get(k, '') for k in fieldnames})

    # Step 8: Generate CSV output
    output_io = io.StringIO()
    writer = csv.DictWriter(output_io, fieldnames=fieldnames)

    writer.writeheader()
    writer.writerows(results_data)

    csv_output = output_io.getvalue()

    return csv_output, total_cost, last_model_name

def _process_single_file_logic(
    file_path: str,
    rel_path: str,
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
        key_exports = "[]"
        dependencies = "[]"
        
        # Step 6c: Check cache (using normalized relative path)
        normalized_path = os.path.normpath(rel_path)
        cache_hit = False
        
        # Also check absolute path for backward compatibility with older caches
        abs_normalized_path = os.path.normpath(file_path)
        
        cached_entry = existing_data.get(normalized_path) or existing_data.get(abs_normalized_path)
        
        if cached_entry:
            # Step 6d: Check hash match and that entry was produced by the new format
            # (old-format entries lack key_exports/dependencies columns entirely;
            #  the CSV parser defaults those to '[]' AND sets a marker flag).
            # A new-format entry may legitimately have '[]' for either field.
            if (
                cached_entry.get('content_hash') == current_hash and
                not cached_entry.get('_backfilled')
            ):
                # Step 6e: Reuse summary
                summary = cached_entry.get('file_summary', "")
                key_exports = cached_entry.get('key_exports', "[]")
                dependencies = cached_entry.get('dependencies', "[]")
                cache_hit = True
                if verbose:
                    console.print(f"[dim]Cache hit for {rel_path}[/dim]")

        # Step 6f: Summarize if needed
        if not cache_hit:
            if verbose:
                console.print(f"[dim]Summarizing {rel_path}...[/dim]")
            
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
            key_exports = json.dumps(file_summary_obj.key_exports)
            dependencies = json.dumps(file_summary_obj.dependencies)
            
            cost = llm_result.get('cost', 0.0)
            model_name = llm_result.get('model_name', "unknown")

        # Print verbose per-file summary (only for freshly summarized files)
        if verbose and not cache_hit:
            console.print(f"  [bold]{rel_path}[/bold]")
            console.print(f"    Summary:      {summary}")
            console.print(f"    Dependencies: {dependencies}")
            console.print(f"    Key Exports:  {key_exports}")

        # Step 6g: Store data
        results_data.append({
            'full_path': rel_path,
            'file_summary': summary,
            'key_exports': key_exports,
            'dependencies': dependencies,
            'content_hash': current_hash
        })

    except Exception as e:
        console.print(f"[bold red]Error processing file {file_path}:[/bold red] {e}")
        results_data.append({
            'full_path': rel_path,
            'file_summary': f"Error processing file: {str(e)}",
            'key_exports': "[]",
            'dependencies': "[]",
            'content_hash': "error"
        })
        
    return cost, model_name
