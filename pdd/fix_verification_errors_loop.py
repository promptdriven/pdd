# -*- coding: utf-8 -*-
"""
Module for iteratively fixing code verification errors using LLMs.
"""

import os
import subprocess
import shutil
import time
import logging
from pathlib import Path
from typing import Dict, Any, Tuple, Optional

# Use Rich for pretty console output
from rich.console import Console
from rich.panel import Panel
from rich.syntax import Syntax
from rich.text import Text

# --- Relative Imports for Internal Package Modules ---
# Attempt relative imports, falling back to standard if run as script
try:
    # Assumes fix_verification_errors is in the same package directory or a submodule
    from .fix_verification_errors import fix_verification_errors
    # Example: If other helpers were needed
    # from .utils import some_helper_function
except ImportError:
    # Fallback for running the script directly or if packaging is not set up
    # This might fail if fix_verification_errors isn't directly runnable/importable
    # Or adjust the path manipulation if needed based on project structure
    print("Warning: Could not perform relative import. Attempting standard import.")
    print("Ensure 'fix_verification_errors' is available in the Python path.")
    # This assumes 'fix_verification_errors.py' is in the same directory
    # or the package 'pdd' is installed/in PYTHONPATH
    try:
        from fix_verification_errors import fix_verification_errors
    except ImportError as e:
        print(f"Error: Failed to import 'fix_verification_errors'. {e}")
        print("Please ensure the 'pdd' package structure is correct or dependencies are installed.")
        # Exit or raise a more specific error if this is critical
        raise

# --- Constants ---
DEFAULT_VERIFICATION_LOG_FILE = "verification_log.txt"
BACKUP_SUFFIX_FORMAT = "_iteration_{}_failed_verification"
BEST_BACKUP_SUFFIX = "_best_iteration_{}"

# --- Setup Logging and Console ---
console = Console(record=True)
# Configure standard logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')


# --- Helper Functions ---

def _run_program(program_path: Path, log_file: Path, verbose: bool = False) -> Tuple[bool, str, int]:
    """
    Runs a Python program using subprocess, captures output, and logs.

    Args:
        program_path: Path to the Python program file.
        log_file: Path to the verification log file.
        verbose: If True, print detailed execution info.

    Returns:
        A tuple containing:
        - bool: True if the program exited with code 0, False otherwise.
        - str: Combined stdout and stderr of the program.
        - int: The return code of the program.
    """
    if not program_path.is_file():
        error_msg = f"Program file not found: {program_path}"
        console.print(f"[bold red]Error:[/bold red] {error_msg}")
        _append_to_log(log_file, f"ERROR: {error_msg}")
        return False, error_msg, -1 # Indicate file not found error

    command = ["python", str(program_path)]
    if verbose:
        console.print(f"\n[bold blue]Executing:[/bold blue] {' '.join(command)}")

    try:
        process = subprocess.run(
            command,
            capture_output=True,
            text=True,
            check=False,  # Don't raise exception for non-zero exit codes
            encoding='utf-8',
            errors='replace' # Handle potential encoding errors
        )
        output = f"--- stdout ---\n{process.stdout}\n--- stderr ---\n{process.stderr}"
        success = process.returncode == 0
        if verbose:
            console.print(f"[dim]Return Code:[/dim] {process.returncode}")
            # Use Syntax for potentially large/complex output
            # console.print(Panel(Syntax(output, "text", theme="default", word_wrap=True), title="Program Output", border_style="dim"))
            # Simpler output for potentially very long logs
            console.print("[dim]--- Program Output ---[/dim]")
            console.print(Text(output, style="dim"))
            console.print("[dim]--- End Program Output ---[/dim]")

        return success, output, process.returncode

    except FileNotFoundError:
        error_msg = f"Error: 'python' command not found. Ensure Python is installed and in PATH."
        console.print(f"[bold red]{error_msg}[/bold red]")
        _append_to_log(log_file, f"ERROR: {error_msg}")
        return False, error_msg, -1
    except Exception as e:
        error_msg = f"Error running program {program_path}: {e}"
        console.print(f"[bold red]{error_msg}[/bold red]")
        _append_to_log(log_file, f"ERROR: {error_msg}")
        return False, error_msg, -1

def _append_to_log(log_file: Path, message: str):
    """Appends a message to the specified log file."""
    try:
        with log_file.open("a", encoding='utf-8') as f:
            f.write(f"{time.strftime('%Y-%m-%d %H:%M:%S')} - {message}\n")
    except IOError as e:
        console.print(f"[bold red]Error writing to log file {log_file}: {e}[/bold red]")

def _read_file_content(file_path: Path) -> Optional[str]:
    """Reads the content of a file."""
    if not file_path.is_file():
        console.print(f"[bold red]Error:[/bold red] File not found: {file_path}")
        return None
    try:
        return file_path.read_text(encoding='utf-8')
    except Exception as e:
        console.print(f"[bold red]Error reading file {file_path}: {e}[/bold red]")
        return None

def _write_file_content(file_path: Path, content: str):
    """Writes content to a file."""
    try:
        file_path.write_text(content, encoding='utf-8')
        if console: # Check if console is initialized
             console.print(f"[green]Successfully wrote changes to:[/green] {file_path}")
    except Exception as e:
        if console:
            console.print(f"[bold red]Error writing file {file_path}: {e}[/bold red]")
        raise # Re-raise exception to handle it in the main loop

def _create_backup(file_path: Path, backup_path: Path, verbose: bool = False):
    """Creates a backup copy of a file."""
    try:
        shutil.copy2(file_path, backup_path) # copy2 preserves metadata
        if verbose:
            console.print(f"[dim]Created backup:[/dim] {backup_path}")
    except Exception as e:
        console.print(f"[bold red]Error creating backup for {file_path} to {backup_path}: {e}[/bold red]")
        # Decide if this is fatal or recoverable

def _restore_from_backup(backup_path: Path, target_path: Path, verbose: bool = False):
    """Restores a file from its backup."""
    if not backup_path.is_file():
        console.print(f"[bold red]Error:[/bold red] Backup file not found: {backup_path}")
        return False
    try:
        shutil.copy2(backup_path, target_path)
        if verbose:
            console.print(f"[yellow]Restored {target_path.name} from backup:[/yellow] {backup_path.name}")
        return True
    except Exception as e:
        console.print(f"[bold red]Error restoring {target_path} from {backup_path}: {e}[/bold red]")
        return False

def _escape_rich_markup(text: str) -> str:
    """Escapes square brackets for safe printing with Rich."""
    return text.replace("[", "\\[")

# --- Main Function ---

def fix_verification_errors_loop(
    program_file: str,
    code_file: str,
    prompt: str,
    verification_program: str,
    strength: float,
    temperature: float,
    max_attempts: int,
    budget: float,
    verification_log_file: str = DEFAULT_VERIFICATION_LOG_FILE,
    verbose: bool = False,
) -> Dict[str, Any]:
    """
    Attempts to fix errors in a code file iteratively based on program execution
    output compared against a prompt, using an LLM.

    Args:
        program_file: Path to the Python program that exercises the code_file.
        code_file: Path to the code file being tested/verified.
        prompt: The prompt defining the intended behavior of the code_file.
        verification_program: Path to a secondary Python program for basic
                              verification (e.g., syntax check) of the code_file.
        strength: LLM strength parameter (0.0 to 1.0).
        temperature: LLM temperature parameter (>= 0.0).
        max_attempts: Maximum number of fix attempts.
        budget: Maximum allowed cost for LLM calls.
        verification_log_file: Path for the verification log (default: verification_log.txt).
        verbose: Enable detailed logging (default: False).

    Returns:
        A dictionary containing:
        - 'success': bool - True if the code was successfully fixed.
        - 'final_program': str - Contents of the final program file.
        - 'final_code': str - Contents of the final code file.
        - 'total_attempts': int - Number of fix attempts made.
        - 'total_cost': float - Total cost of LLM calls.
        - 'model_name': str - Name of the LLM model used (if any).
        - 'statistics': dict - Detailed statistics about the process.
    """
    console.print(Panel(f"Starting Iterative Verification Fix Process", title="[bold cyan]PDD Fix Loop[/bold cyan]", border_style="cyan"))

    # --- Input Validation and Path Setup ---
    program_path = Path(program_file).resolve()
    code_path = Path(code_file).resolve()
    verification_program_path = Path(verification_program).resolve()
    log_path = Path(verification_log_file).resolve()

    required_files = {
        "Program File": program_path,
        "Code File": code_path,
        "Verification Program": verification_program_path,
    }
    for name, path in required_files.items():
        if not path.is_file():
            msg = f"{name} not found at: {path}"
            console.print(f"[bold red]Error:[/bold red] {msg}")
            return {
                "success": False, "final_program": "", "final_code": "",
                "total_attempts": 0, "total_cost": 0.0, "model_name": "",
                "statistics": {"error": msg}
            }

    if not (0.0 <= strength <= 1.0):
        console.print(f"[bold yellow]Warning:[/bold yellow] Strength ({strength}) is outside the typical range [0.0, 1.0].")
    if not (temperature >= 0.0):
         console.print(f"[bold yellow]Warning:[/bold yellow] Temperature ({temperature}) should be >= 0.0.")
    if max_attempts <= 0:
        console.print(f"[bold yellow]Warning:[/bold yellow] max_attempts ({max_attempts}) should be positive. Setting to 1.")
        max_attempts = 1
    if budget < 0:
        console.print(f"[bold yellow]Warning:[/bold yellow] budget ({budget}) should be non-negative. Setting to 0.0.")
        budget = 0.0

    # --- Initialization ---
    attempts = 0
    total_cost = 0.0
    model_name = "N/A" # Default if LLM is never called
    best_iteration_data = {
        "attempt": -1, # -1 for initial state
        "program_backup_path": None,
        "code_backup_path": None,
        "program_output": "",
        "analysis_issues_found": True, # Assume issues initially unless proven otherwise
        "secondary_verification_passed": False # Assume false initially
    }
    stats = {
        "initial_state": {"output": "", "issues_found": None}, # Based on fix_verification_errors analysis
        "final_state": {"output": "", "issues_found": None},
        "best_iteration": -1,
        "best_iteration_issues_found": None,
        "improvements_made": False, # Tracks if any fix attempt led to a better state
        "iterations": [] # List to store per-iteration results
    }

    # Step 1: Remove existing log file
    try:
        if log_path.exists():
            log_path.unlink()
            if verbose:
                console.print(f"[dim]Removed existing log file:[/dim] {log_path}")
        log_path.touch() # Create new empty log file
        _append_to_log(log_path, "Starting verification fix loop.")
    except OSError as e:
        console.print(f"[bold red]Error managing log file {log_path}: {e}[/bold red]")
        # Continue if log file is not critical, but log the error

    # --- Step 3: Initial Run ---
    console.print("\n[bold]Running initial verification...[/bold]")
    initial_success, initial_output, initial_retcode = _run_program(program_path, log_path, verbose)
    _append_to_log(log_path, f"Initial Run (Return Code: {initial_retcode}):\n{initial_output}\n---")
    console.print("[bold]Initial Program Output:[/bold]")
    console.print(_escape_rich_markup(initial_output))

    # Initial analysis using fix_verification_errors to gauge starting point
    # We run it here just for analysis, not fixing yet.
    # Read initial file contents
    initial_program_content = _read_file_content(program_path)
    initial_code_content = _read_file_content(code_path)
    if initial_program_content is None or initial_code_content is None:
         # Error already printed by _read_file_content
         return {
             "success": False, "final_program": "", "final_code": "",
             "total_attempts": 0, "total_cost": 0.0, "model_name": "",
             "statistics": {"error": "Failed to read initial files."}
         }

    console.print("\n[bold]Analyzing initial output against prompt...[/bold]")
    try:
        # Use strength=0 to potentially use a cheaper model just for analysis, if supported
        # Or use the provided strength if analysis quality is important
        analysis_results = fix_verification_errors(
            program=initial_program_content,
            prompt=prompt,
            code=initial_code_content,
            output=initial_output,
            strength=strength, # Use configured strength for consistency
            temperature=0.0, # Low temp for deterministic analysis
            verbose=verbose,
            # Pass log file? The example doesn't show it, assume it logs internally if needed
        )
        initial_issues_found = len(analysis_results.get('explanation', [])) > 1 # Check if more than just the header exists
        total_cost += analysis_results.get('total_cost', 0.0)
        model_name = analysis_results.get('model_name', model_name) # Capture model name early
        stats["initial_state"]["output"] = initial_output
        stats["initial_state"]["issues_found"] = initial_issues_found
        best_iteration_data["program_output"] = initial_output
        best_iteration_data["analysis_issues_found"] = initial_issues_found
        best_iteration_data["secondary_verification_passed"] = True # Assume initial code passes basic checks

        if not initial_issues_found:
            console.print("[bold green]Initial analysis indicates code meets prompt intent.[/bold green]")
            # If initial state is already good, we might stop early or just record it as best
            best_iteration_data["attempt"] = 0 # Mark initial state as best so far
        else:
            console.print("[bold yellow]Initial analysis found potential issues based on output.[/bold yellow]")
            if verbose:
                 console.print("[dim]Issues:[/dim]")
                 for issue in analysis_results.get('explanation', ["No details provided."]):
                     console.print(f"[dim]- {issue}[/dim]")

    except Exception as e:
        console.print(f"[bold red]Error during initial analysis call to fix_verification_errors: {e}[/bold red]")
        _append_to_log(log_path, f"ERROR: Initial analysis failed: {e}")
        # Decide how to proceed: maybe assume issues exist?
        stats["initial_state"]["issues_found"] = True # Assume failure if analysis crashes
        best_iteration_data["analysis_issues_found"] = True

    # --- Step 4: Iterative Fixing Loop ---
    current_program_content = initial_program_content
    current_code_content = initial_code_content
    last_successful_program_backup = None
    last_successful_code_backup = None
    program_output = initial_output # Start with the initial output for the first loop check
    analysis_issues_found = stats["initial_state"]["issues_found"] # Start with initial analysis result

    while attempts < max_attempts and total_cost < budget:
        console.print(f"\n[bold cyan]--- Attempt {attempts + 1} / {max_attempts} ---[/bold cyan]")
        _append_to_log(log_path, f"--- Starting Attempt {attempts + 1} ---")

        # Step 4b: Run program (or use result from previous iteration/initial run)
        # We already have 'program_output' and 'analysis_issues_found' from the previous step or initial run

        # Step 4c: Analyze output (already done via 'analysis_issues_found')
        if not analysis_issues_found:
            console.print("[bold green]Verification successful! Program output aligns with prompt intent.[/bold green]")
            _append_to_log(log_path, f"Attempt {attempts + 1}: Verification successful based on analysis.")
            break # Exit loop successfully

        # Step 4d: Verification failed, attempt fix
        console.print("[yellow]Verification failed or issues found. Attempting fix...[/yellow]")
        _append_to_log(log_path, f"Attempt {attempts + 1}: Verification failed. Output:\n{program_output}\n---")

        # Print output to console (escaped)
        console.print("[bold]Program Output (Attempt {attempts + 1}):[/bold]")
        console.print(_escape_rich_markup(program_output))

        # Create backups *before* attempting modification
        backup_dir = program_path.parent
        program_backup_path = backup_dir / f"{program_path.stem}{BACKUP_SUFFIX_FORMAT.format(attempts + 1)}{program_path.suffix}"
        code_backup_path = code_path.parent / f"{code_path.stem}{BACKUP_SUFFIX_FORMAT.format(attempts + 1)}{code_path.suffix}"
        _create_backup(program_path, program_backup_path, verbose)
        _create_backup(code_path, code_backup_path, verbose)

        # Read current contents (redundant if tracking vars are perfect, but safer)
        current_program_content = _read_file_content(program_path)
        current_code_content = _read_file_content(code_path)
        if current_program_content is None or current_code_content is None:
            _append_to_log(log_path, f"ERROR: Failed to read files before fix attempt {attempts + 1}.")
            break # Cannot proceed if files can't be read

        # Call the fixing function
        try:
            console.print(f"\n[bold]Calling LLM to fix issues (Strength: {strength}, Temp: {temperature})...[/bold]")
            fix_results = fix_verification_errors(
                program=current_program_content,
                prompt=prompt,
                code=current_code_content,
                output=program_output, # Use the output that indicated failure
                strength=strength,
                temperature=temperature,
                verbose=verbose,
                # log_file=verification_log_file # Pass log file if function supports it
            )

            attempt_cost = fix_results.get('total_cost', 0.0)
            total_cost += attempt_cost
            model_name = fix_results.get('model_name', model_name) # Update model name if changed
            updated_program = fix_results.get('fixed_program', current_program_content) != current_program_content
            updated_code = fix_results.get('fixed_code', current_code_content) != current_code_content
            fixed_program_content = fix_results.get('fixed_program', current_program_content)
            fixed_code_content = fix_results.get('fixed_code', current_code_content)
            fix_explanation = fix_results.get('explanation', ["No explanation provided."])

            _append_to_log(log_path, f"Attempt {attempts + 1}: LLM Fix Cost: ${attempt_cost:.6f}, Total Cost: ${total_cost:.6f}")
            _append_to_log(log_path, f"Attempt {attempts + 1}: LLM Model: {model_name}")
            _append_to_log(log_path, f"Attempt {attempts + 1}: Fix Explanation:\n" + "\n".join(fix_explanation))
            _append_to_log(log_path, f"Attempt {attempts + 1}: Program Updated: {updated_program}, Code Updated: {updated_code}")

            if verbose:
                console.print(f"[dim]LLM Cost (Attempt {attempts + 1}):[/dim] ${attempt_cost:.6f}")
                console.print(f"[dim]Total Cost:[/dim] ${total_cost:.6f}")
                console.print(f"[dim]Model Used:[/dim] {model_name}")
                console.print("[dim]Fix Explanation:[/dim]")
                for line in fix_explanation:
                     console.print(f"[dim]- {line}[/dim]")

            # Check budget
            if total_cost >= budget:
                console.print(f"[bold yellow]Budget exceeded (${total_cost:.2f} >= ${budget:.2f}). Stopping.[/bold yellow]")
                _append_to_log(log_path, "Budget exceeded. Stopping.")
                break

            # Check if any changes were made
            if not updated_program and not updated_code:
                console.print("[yellow]LLM did not suggest any changes. Stopping.[/yellow]")
                _append_to_log(log_path, "LLM suggested no changes. Stopping.")
                break

            # Apply changes and verify
            secondary_verification_passed_this_iter = True # Assume pass unless failed
            if updated_code:
                console.print("[bold]Applying code changes and running secondary verification...[/bold]")
                try:
                    _write_file_content(code_path, fixed_code_content)
                    current_code_content = fixed_code_content # Update tracked content

                    # Run secondary verification program
                    sec_verify_success, sec_verify_output, sec_verify_retcode = _run_program(
                        verification_program_path, log_path, verbose
                    )
                    _append_to_log(log_path, f"Attempt {attempts + 1}: Secondary Verification (Return Code: {sec_verify_retcode}):\n{sec_verify_output}\n---")

                    if not sec_verify_success:
                        console.print("[bold red]Secondary verification failed after code update![/bold red]")
                        console.print("[bold]Secondary Verification Output:[/bold]")
                        console.print(_escape_rich_markup(sec_verify_output))
                        _append_to_log(log_path, f"Attempt {attempts + 1}: Secondary verification FAILED. Restoring code file.")
                        secondary_verification_passed_this_iter = False

                        # Restore code file from backup created at the start of this iteration
                        if not _restore_from_backup(code_backup_path, code_path, verbose):
                             console.print("[bold red]CRITICAL: Failed to restore code file after secondary verification failure![/bold red]")
                             _append_to_log(log_path, "CRITICAL: Failed to restore code file.")
                             # Decide whether to break or try to continue (might be risky)
                             break
                        else:
                             current_code_content = _read_file_content(code_path) # Re-read restored content
                             # Continue to the next attempt loop, maybe the next fix will work better
                             # We don't run the main program again as the code change was reverted.
                             attempts += 1
                             stats["iterations"].append({
                                 "attempt": attempts,
                                 "cost": attempt_cost,
                                 "model": model_name,
                                 "program_updated": updated_program,
                                 "code_updated": updated_code,
                                 "secondary_verification_passed": False,
                                 "primary_issues_found": analysis_issues_found, # State before reverted fix
                                 "output": program_output # Output before reverted fix
                             })
                             console.print("[yellow]Code restored. Continuing to next attempt.[/yellow]")
                             continue # Skip rest of the loop for this attempt

                    else: # Secondary verification passed
                        console.print("[green]Secondary verification passed.[/green]")
                        # Keep track of the last known good backup state
                        last_successful_code_backup = code_backup_path
                        # Proceed to potentially update program file and run primary verification

                except Exception as e:
                    console.print(f"[bold red]Error applying code changes or running secondary verification: {e}[/bold red]")
                    _append_to_log(log_path, f"ERROR: Applying code changes/secondary verification failed: {e}")
                    secondary_verification_passed_this_iter = False
                    # Attempt restore if possible
                    _restore_from_backup(code_backup_path, code_path, verbose)
                    current_code_content = _read_file_content(code_path)
                    # Break or continue? Let's break as state is uncertain.
                    break

            if updated_program:
                 console.print("[bold]Applying program changes...[/bold]")
                 try:
                     _write_file_content(program_path, fixed_program_content)
                     current_program_content = fixed_program_content
                     last_successful_program_backup = program_backup_path # Track successful backup
                 except Exception as e:
                     console.print(f"[bold red]Error applying program changes: {e}[/bold red]")
                     _append_to_log(log_path, f"ERROR: Applying program changes failed: {e}")
                     # Attempt restore
                     _restore_from_backup(program_backup_path, program_path, verbose)
                     current_program_content = _read_file_content(program_path)
                     break # Break if program update fails

            # Increment attempt counter *after* successful application (or reverted failure)
            attempts += 1

            # Run the main program again to see if the fix worked
            console.print(f"\n[bold]Re-running main program after applying fixes (Attempt {attempts})...[/bold]")
            run_success, run_output, run_retcode = _run_program(program_path, log_path, verbose)
            program_output = run_output # Update program_output for the next iteration's analysis
            _append_to_log(log_path, f"Attempt {attempts}: Post-Fix Run (Return Code: {run_retcode}):\n{program_output}\n---")

            console.print(f"[bold]Program Output (Post-Fix Attempt {attempts}):[/bold]")
            console.print(_escape_rich_markup(program_output))

            # Analyze the new output
            console.print("\n[bold]Analyzing new output against prompt...[/bold]")
            try:
                analysis_results = fix_verification_errors(
                    program=current_program_content,
                    prompt=prompt,
                    code=current_code_content,
                    output=program_output,
                    strength=strength,
                    temperature=0.0, # Low temp for analysis
                    verbose=verbose,
                )
                new_issues_found = len(analysis_results.get('explanation', [])) > 1
                analysis_cost = analysis_results.get('total_cost', 0.0)
                total_cost += analysis_cost # Add analysis cost
                model_name = analysis_results.get('model_name', model_name)
                analysis_issues_found = new_issues_found # Update for the next loop check

                _append_to_log(log_path, f"Attempt {attempts}: Post-Fix Analysis Cost: ${analysis_cost:.6f}, Total Cost: ${total_cost:.6f}")
                _append_to_log(log_path, f"Attempt {attempts}: Post-Fix Analysis Issues Found: {analysis_issues_found}")

                if verbose:
                    console.print(f"[dim]Analysis Cost (Attempt {attempts}):[/dim] ${analysis_cost:.6f}")
                    console.print(f"[dim]Total Cost:[/dim] ${total_cost:.6f}")
                    console.print(f"[dim]Issues Found after fix:[/dim] {analysis_issues_found}")
                    if analysis_issues_found:
                         console.print("[dim]Issues:[/dim]")
                         for issue in analysis_results.get('explanation', ["No details provided."]):
                             console.print(f"[dim]- {issue}[/dim]")

                # Update statistics for this iteration
                stats["iterations"].append({
                    "attempt": attempts,
                    "cost": attempt_cost + analysis_cost, # Combine fix and analysis cost for the iter
                    "model": model_name,
                    "program_updated": updated_program,
                    "code_updated": updated_code,
                    "secondary_verification_passed": secondary_verification_passed_this_iter,
                    "primary_issues_found": analysis_issues_found,
                    "output": program_output
                })

                # Update best iteration tracker
                # Best is defined as: No issues found, secondary verification passed.
                # If multiple iterations achieve this, the earliest one is best.
                # If no iteration achieves this, the initial state might be the "best" if it had no issues.
                current_iter_is_good = not analysis_issues_found and secondary_verification_passed_this_iter
                best_iter_is_good = not best_iteration_data["analysis_issues_found"] and best_iteration_data["secondary_verification_passed"]

                if current_iter_is_good:
                    stats["improvements_made"] = True # Mark that an improvement occurred
                    if not best_iter_is_good or attempts < best_iteration_data["attempt"]:
                         console.print(f"[bold green]Improvement found! Marking Attempt {attempts} as the current best.[/bold green]")
                         _append_to_log(log_path, f"Attempt {attempts} marked as best iteration so far.")
                         best_iteration_data["attempt"] = attempts
                         # Store the paths to the backups made *before* this successful attempt
                         best_iteration_data["program_backup_path"] = program_backup_path
                         best_iteration_data["code_backup_path"] = code_backup_path
                         best_iteration_data["program_output"] = program_output
                         best_iteration_data["analysis_issues_found"] = analysis_issues_found
                         best_iteration_data["secondary_verification_passed"] = secondary_verification_passed_this_iter

                # Check budget again after analysis cost
                if total_cost >= budget:
                    console.print(f"[bold yellow]Budget exceeded after analysis (${total_cost:.2f} >= ${budget:.2f}). Stopping.[/bold yellow]")
                    _append_to_log(log_path, "Budget exceeded after analysis. Stopping.")
                    break

            except Exception as e:
                console.print(f"[bold red]Error during post-fix analysis call to fix_verification_errors: {e}[/bold red]")
                _append_to_log(log_path, f"ERROR: Post-fix analysis failed for attempt {attempts}: {e}")
                # Assume issues still exist if analysis fails
                analysis_issues_found = True
                stats["iterations"].append({ # Log attempt even with analysis failure
                     "attempt": attempts, "cost": attempt_cost, "model": model_name,
                     "program_updated": updated_program, "code_updated": updated_code,
                     "secondary_verification_passed": secondary_verification_passed_this_iter,
                     "primary_issues_found": True, # Assume issues
                     "output": program_output, "error": f"Analysis failed: {e}"
                 })
                # Maybe break here as we can't determine state?
                break

        except Exception as e:
            console.print(f"[bold red]Error during fix attempt {attempts + 1}: {e}[/bold red]")
            _append_to_log(log_path, f"ERROR: Fix attempt {attempts + 1} failed: {e}")
            # Increment attempts even if the fix call failed, to avoid infinite loops on persistent errors
            attempts += 1
            # Restore from backups made at the start of this failed attempt
            _restore_from_backup(program_backup_path, program_path, verbose)
            _restore_from_backup(code_backup_path, code_path, verbose)
            current_program_content = _read_file_content(program_path)
            current_code_content = _read_file_content(code_path)
            # Break the loop as the fixing mechanism itself failed
            break

    # --- Loop End ---
    if attempts == max_attempts:
        console.print(f"\n[bold yellow]Maximum attempts ({max_attempts}) reached.[/bold yellow]")
        _append_to_log(log_path, "Maximum attempts reached.")
    elif total_cost >= budget:
         console.print(f"\n[bold yellow]Budget limit ({budget}) reached or exceeded.[/bold yellow]")
         # Already logged inside loop

    # --- Step 5: Final Run and State Determination ---
    console.print("\n[bold]Running final verification check...[/bold]")
    final_success_flag, final_output, final_retcode = _run_program(program_path, log_path, verbose)
    _append_to_log(log_path, f"Final Run (Return Code: {final_retcode}):\n{final_output}\n---")
    console.print("[bold]Final Program Output:[/bold]")
    console.print(_escape_rich_markup(final_output))

    # Final analysis to determine final state
    final_issues_found = True # Default to issues found unless analysis proves otherwise
    final_program_content = _read_file_content(program_path)
    final_code_content = _read_file_content(code_path)
    if final_program_content is not None and final_code_content is not None:
        try:
            console.print("\n[bold]Analyzing final output against prompt...[/bold]")
            analysis_results = fix_verification_errors(
                program=final_program_content,
                prompt=prompt,
                code=final_code_content,
                output=final_output,
                strength=strength,
                temperature=0.0,
                verbose=verbose,
            )
            final_issues_found = len(analysis_results.get('explanation', [])) > 1
            analysis_cost = analysis_results.get('total_cost', 0.0)
            total_cost += analysis_cost # Add final analysis cost
            model_name = analysis_results.get('model_name', model_name)
            stats["final_state"]["output"] = final_output
            stats["final_state"]["issues_found"] = final_issues_found
            _append_to_log(log_path, f"Final Analysis Cost: ${analysis_cost:.6f}, Final Total Cost: ${total_cost:.6f}")
            _append_to_log(log_path, f"Final Analysis Issues Found: {final_issues_found}")
            if verbose:
                 console.print(f"[dim]Final Analysis Cost:[/dim] ${analysis_cost:.6f}")
                 console.print(f"[dim]Final Total Cost:[/dim] ${total_cost:.6f}")
                 console.print(f"[dim]Final Issues Found:[/dim] {final_issues_found}")

        except Exception as e:
            console.print(f"[bold red]Error during final analysis: {e}[/bold red]")
            _append_to_log(log_path, f"ERROR: Final analysis failed: {e}")
            stats["final_state"]["output"] = final_output
            stats["final_state"]["issues_found"] = True # Assume issues if analysis fails
    else:
        stats["final_state"]["output"] = "Error reading final files."
        stats["final_state"]["issues_found"] = True


    # --- Step 6: Restore Best Iteration if Necessary ---
    final_state_is_good = not stats["final_state"]["issues_found"]
    best_iter_attempt = best_iteration_data["attempt"]
    best_iter_is_good = not best_iteration_data["analysis_issues_found"] and best_iteration_data["secondary_verification_passed"]

    restored_from_best = False
    if best_iter_attempt > 0 and best_iter_is_good and not final_state_is_good:
        console.print(f"\n[bold yellow]Final state has issues, but a better state was found in Attempt {best_iter_attempt}. Restoring...[/bold yellow]")
        _append_to_log(log_path, f"Restoring state from best iteration (Attempt {best_iter_attempt}).")
        restored_program = _restore_from_backup(best_iteration_data["program_backup_path"], program_path, verbose)
        restored_code = _restore_from_backup(best_iteration_data["code_backup_path"], code_path, verbose)

        if restored_program and restored_code:
            console.print(f"[green]Successfully restored files from Attempt {best_iter_attempt}.[/green]")
            # Update final contents and potentially re-run analysis for consistency? Or just trust the best state's analysis?
            # Let's trust the best state's analysis for the final report.
            final_program_content = _read_file_content(program_path)
            final_code_content = _read_file_content(code_path)
            stats["final_state"]["output"] = best_iteration_data["program_output"] # Use best output
            stats["final_state"]["issues_found"] = best_iteration_data["analysis_issues_found"] # Use best analysis
            final_issues_found = best_iteration_data["analysis_issues_found"] # Update final flag
            restored_from_best = True
            _append_to_log(log_path, "Restoration successful.")
        else:
            console.print(f"[bold red]Failed to restore files from Attempt {best_iter_attempt}. Final state might be incorrect.[/bold red]")
            _append_to_log(log_path, "ERROR: Restoration failed.")
            # Keep the current final_program_content and final_code_content

    elif best_iter_attempt == 0 and best_iter_is_good and not final_state_is_good:
         console.print(f"\n[bold yellow]Final state has issues, but the initial state was good. Cannot restore automatically (no backup created for initial state).[/bold yellow]")
         _append_to_log(log_path, "Final state worse than initial good state. Manual check advised.")
         # Keep the current final state, but report that initial was better.


    # --- Step 7: Calculate and Print Summary Statistics ---
    stats["best_iteration"] = best_iteration_data["attempt"] if best_iter_is_good else -1 # -1 if no good iteration found
    stats["best_iteration_issues_found"] = best_iteration_data["analysis_issues_found"] if best_iter_attempt != -1 else None

    # Determine overall success based on the final state (after potential restore)
    overall_success = not final_issues_found

    console.print(Panel(f"Verification Fix Process Finished", title="[bold cyan]PDD Fix Loop Summary[/bold cyan]", border_style="cyan"))
    console.print(f"[bold]Overall Success:[/bold] {'[bold green]Yes[/bold green]' if overall_success else '[bold red]No[/bold red]'}")
    console.print(f"[bold]Total Attempts Made:[/bold] {attempts}")
    console.print(f"[bold]Total LLM Cost:[/bold] ${total_cost:.6f}")
    console.print(f"[bold]LLM Model Used:[/bold] {model_name}")

    console.print("\n[bold]--- Statistics ---[/bold]")
    initial_state_str = "No Issues Found" if stats['initial_state']['issues_found'] == False else "Issues Found" if stats['initial_state']['issues_found'] == True else "Unknown"
    final_state_str = "No Issues Found" if stats['final_state']['issues_found'] == False else "Issues Found" if stats['final_state']['issues_found'] == True else "Unknown"
    console.print(f"Initial State: {initial_state_str}")
    console.print(f"Final State:   {final_state_str}")

    if stats['best_iteration'] != -1:
        best_iter_state_str = "No Issues Found" if stats['best_iteration_issues_found'] == False else "Issues Found"
        restore_msg = " (Restored)" if restored_from_best else ""
        console.print(f"Best Iteration Found: Attempt {stats['best_iteration']} ({best_iter_state_str}){restore_msg}")
    else:
        console.print("Best Iteration Found: None")

    improvement_str = "N/A"
    if stats['initial_state']['issues_found'] is not None and stats['final_state']['issues_found'] is not None:
        if stats['initial_state']['issues_found'] and not stats['final_state']['issues_found']:
            improvement_str = "[bold green]Improved (Fixed Issues)[/bold green]"
        elif not stats['initial_state']['issues_found'] and stats['final_state']['issues_found']:
             improvement_str = "[bold red]Regressed (Introduced Issues)[/bold red]"
        elif stats['initial_state']['issues_found'] and stats['final_state']['issues_found']:
             improvement_str = "[yellow]No Change (Issues Persist)[/yellow]"
        else: # Not initial issues, not final issues
             improvement_str = "[blue]No Change (No Issues Initially)[/blue]"
    console.print(f"Overall Improvement: {improvement_str}")
    console.print(f"Log File: {log_path}")

    # --- Step 8: Return Results ---
    # Ensure final contents are read after potential restoration
    final_program_content = _read_file_content(program_path) or "" # Provide empty string on read error
    final_code_content = _read_file_content(code_path) or ""

    _append_to_log(log_path, f"Finished. Overall Success: {overall_success}, Total Attempts: {attempts}, Total Cost: ${total_cost:.6f}")

    return {
        "success": overall_success,
        "final_program": final_program_content,
        "final_code": final_code_content,
        "total_attempts": attempts,
        "total_cost": total_cost,
        "model_name": model_name,
        "statistics": stats,
    }