# -*- coding: utf-8 -*-
"""
Module for iteratively fixing code verification errors using LLMs.
"""

import os
import subprocess
import shutil
import time
import datetime
import xml.etree.ElementTree as ET
from xml.dom import minidom
import tempfile
from typing import Dict, Any, Tuple, Optional

# Use Rich for pretty console output
from rich.console import Console
from rich.panel import Panel
from rich.syntax import Syntax
from rich.text import Text

# --- Internal Module Imports ---
# Attempt relative import for package structure
try:
    from .fix_verification_errors import fix_verification_errors
    from .utils import ensure_dir_exists # Assuming a utility function exists
except ImportError:
    # Fallback for standalone execution or different structure
    # This might indicate a setup issue if running as part of the package
    print("Warning: Could not perform relative import. Falling back.")
    # If fix_verification_errors is in the same directory or PYTHONPATH:
    try:
        from fix_verification_errors import fix_verification_errors
    except ImportError as e:
        raise ImportError(
            "Could not import 'fix_verification_errors'. "
            "Ensure it's in the correct path or package structure."
        ) from e
    # Define a dummy ensure_dir_exists if not available
    def ensure_dir_exists(file_path: str):
        """Ensure the directory for the given file path exists."""
        directory = os.path.dirname(file_path)
        if directory and not os.path.exists(directory):
            os.makedirs(directory)

# Initialize Rich Console
console = Console()

# --- Helper Functions ---

def _run_subprocess(command: list[str], cwd: Optional[str] = None) -> Tuple[bool, str, int]:
    """
    Runs a subprocess command and captures its output.

    Args:
        command: A list of strings representing the command and its arguments.
        cwd: The working directory to run the command in.

    Returns:
        A tuple containing:
        - success (bool): True if the command exited with code 0, False otherwise.
        - output (str): The combined stdout and stderr of the command.
        - return_code (int): The exit code of the command.
    """
    try:
        process = subprocess.run(
            command,
            capture_output=True,
            text=True,
            check=False, # Don't raise exception on non-zero exit
            cwd=cwd,
            encoding='utf-8',
            errors='replace' # Handle potential encoding errors
        )
        output = process.stdout + process.stderr
        success = process.returncode == 0
        return success, output.strip(), process.returncode
    except FileNotFoundError:
        error_msg = f"Error: Command not found: '{command[0]}'. Please ensure it's installed and in PATH."
        console.print(f"[bold red]{error_msg}[/bold red]")
        return False, error_msg, -1 # Use -1 to indicate execution failure
    except Exception as e:
        error_msg = f"Error running subprocess {' '.join(command)}: {e}"
        console.print(f"[bold red]{error_msg}[/bold red]")
        return False, error_msg, -1

def _read_file(file_path: str) -> Optional[str]:
    """Reads the content of a file."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            return f.read()
    except FileNotFoundError:
        console.print(f"[bold red]Error: File not found: {file_path}[/bold red]")
        return None
    except Exception as e:
        console.print(f"[bold red]Error reading file {file_path}: {e}[/bold red]")
        return None

def _write_file(file_path: str, content: str) -> bool:
    """Writes content to a file."""
    try:
        ensure_dir_exists(file_path)
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(content)
        return True
    except Exception as e:
        console.print(f"[bold red]Error writing file {file_path}: {e}[/bold red]")
        return False

def _create_backup(file_path: str, iteration: int) -> Optional[str]:
    """Creates a backup copy of a file."""
    if not os.path.exists(file_path):
        console.print(f"[yellow]Warning: Cannot backup non-existent file: {file_path}[/yellow]")
        return None
    try:
        base, ext = os.path.splitext(file_path)
        backup_path = f"{base}_iteration_{iteration}{ext}"
        shutil.copy2(file_path, backup_path) # copy2 preserves metadata
        return backup_path
    except Exception as e:
        console.print(f"[bold red]Error creating backup for {file_path}: {e}[/bold red]")
        return None

def _restore_backup(backup_path: str, original_path: str) -> bool:
    """Restores a file from its backup."""
    if not backup_path or not os.path.exists(backup_path):
        console.print(f"[bold red]Error: Backup file not found: {backup_path}[/bold red]")
        return False
    try:
        shutil.copy2(backup_path, original_path)
        return True
    except Exception as e:
        console.print(f"[bold red]Error restoring {original_path} from {backup_path}: {e}[/bold red]")
        return False

def _append_log_entry(log_file: str, root_element: ET.Element, entry_element: ET.Element):
    """Appends an XML element to the log file."""
    try:
        ensure_dir_exists(log_file)
        root_element.append(entry_element)
        # Use minidom for pretty printing XML
        rough_string = ET.tostring(root_element, 'utf-8')
        reparsed = minidom.parseString(rough_string)
        pretty_xml = reparsed.toprettyxml(indent="  ", encoding='utf-8')

        with open(log_file, 'wb') as f: # Write bytes for encoded XML
            f.write(pretty_xml)
    except Exception as e:
        console.print(f"[bold red]Error writing to XML log file {log_file}: {e}[/bold red]")

def _create_cdata_element(parent: ET.Element, tag_name: str, content: Optional[str]):
    """Creates an XML element with CDATA content."""
    element = ET.SubElement(parent, tag_name)
    # Use a placeholder if content is None or empty to ensure valid XML structure
    element.text = ET.CDATA(content if content is not None else "")


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
    verification_log_file: str = "verification_log.xml",
    verbose: bool = False
) -> Dict[str, Any]:
    """
    Attempts to fix errors in a code file iteratively based on program execution.

    Args:
        program_file: Path to the Python program file that exercises the code_file.
        code_file: Path to the code file being tested/verified.
        prompt: The prompt that generated the code under test.
        verification_program: Path to a secondary Python program for basic verification.
        strength: LLM strength parameter (0.0 to 1.0).
        temperature: LLM temperature parameter (>= 0.0).
        max_attempts: Maximum number of fix attempts.
        budget: Maximum allowed cost for LLM calls.
        verification_log_file: Path for detailed XML logging.
        verbose: Enable detailed console logging.

    Returns:
        A dictionary containing:
        - 'success': bool - True if the code was successfully fixed.
        - 'final_program': str - Contents of the final program file.
        - 'final_code': str - Contents of the final code file.
        - 'total_attempts': int - Number of fix attempts made.
        - 'total_cost': float - Total cost incurred.
        - 'model_name': str | None - Name of the LLM model used (last successful call).
        - 'statistics': dict - Detailed statistics about the process.
    """
    console.print(Panel(f"Starting Verification Fix Loop for [cyan]{code_file}[/cyan]", title="[bold blue]Process Start[/bold blue]", expand=False))

    # --- Step 1: Initialize Log File ---
    if os.path.exists(verification_log_file):
        try:
            os.remove(verification_log_file)
            if verbose:
                console.print(f"Removed existing log file: {verification_log_file}")
        except OSError as e:
            console.print(f"[bold red]Error removing existing log file {verification_log_file}: {e}[/bold red]")
            # Continue execution, but logging might be appended or fail later
    log_root = ET.Element("VerificationLog")
    log_root.set("startTime", datetime.datetime.now().isoformat())

    # --- Step 2: Initialize Variables ---
    attempts = 0
    total_cost = 0.0
    model_name: Optional[str] = None
    overall_success = False
    last_fix_result: Optional[Dict[str, Any]] = None # Store the result of the last fix attempt

    # Best iteration tracker: Stores the state with the minimum verified issues
    best_iteration = {
        'attempt': -1, # -1 means initial state, 0+ for loop iterations
        'issues': float('inf'),
        'program_backup_path': None,
        'code_backup_path': None,
        'model_name': None,
    }

    # Statistics tracker
    stats = {
        'initial_issues': -1, # -1 indicates not yet determined
        'final_issues': -1,
        'best_iteration_attempt': -1,
        'best_iteration_issues': float('inf'),
        'improvement_issues': 0,
        'overall_success_flag': False,
        'exit_reason': "Unknown",
    }

    # --- Input Validation ---
    if not os.path.isfile(program_file):
        console.print(f"[bold red]Error: Program file not found: {program_file}[/bold red]")
        stats['exit_reason'] = "Input Error: Program file not found"
        return {
            'success': False, 'final_program': "", 'final_code': "",
            'total_attempts': 0, 'total_cost': 0.0, 'model_name': None,
            'statistics': stats
        }
    if not os.path.isfile(code_file):
        console.print(f"[bold red]Error: Code file not found: {code_file}[/bold red]")
        stats['exit_reason'] = "Input Error: Code file not found"
        return {
            'success': False, 'final_program': "", 'final_code': "",
            'total_attempts': 0, 'total_cost': 0.0, 'model_name': None,
            'statistics': stats
        }
    if not os.path.isfile(verification_program):
        console.print(f"[bold red]Error: Secondary verification program not found: {verification_program}[/bold red]")
        stats['exit_reason'] = "Input Error: Verification program not found"
        return {
            'success': False, 'final_program': "", 'final_code': "",
            'total_attempts': 0, 'total_cost': 0.0, 'model_name': None,
            'statistics': stats
        }

    # --- Step 3: Determine Initial State ---
    if verbose:
        console.print("\n[bold]Step 3: Determining Initial State[/bold]")

    # 3a: Run initial program
    initial_run_success, initial_output, _ = _run_subprocess(['python', program_file])
    if verbose:
        console.print(f"Initial program execution {'succeeded' if initial_run_success else 'failed'}.")
        console.print("[dim]Initial Output:[/dim]")
        console.print(f"[grey37]{initial_output or '[No Output]'}[/grey37]")

    # 3b: Log initial state
    initial_state_log = ET.Element("InitialState")
    initial_state_log.set("timestamp", datetime.datetime.now().isoformat())
    _create_cdata_element(initial_state_log, "InitialProgramOutput", initial_output)
    _append_log_entry(verification_log_file, log_root, initial_state_log)

    # 3c: Read initial contents
    initial_program_contents = _read_file(program_file)
    initial_code_contents = _read_file(code_file)
    if initial_program_contents is None or initial_code_contents is None:
        stats['exit_reason'] = "File Read Error: Could not read initial program or code file."
        return {
            'success': False, 'final_program': initial_program_contents or "", 'final_code': initial_code_contents or "",
            'total_attempts': 0, 'total_cost': 0.0, 'model_name': None,
            'statistics': stats
        }

    # 3d: Call fix_verification_errors for initial assessment
    if verbose:
        console.print("Running initial assessment with 'fix_verification_errors'...")
    try:
        # Use provided strength/temp for consistency, but check budget
        if budget <= 0:
             console.print("[bold yellow]Warning: Initial budget is zero or negative. Skipping initial assessment.[/bold yellow]")
             initial_fix_result = {'total_cost': 0.0, 'verification_issues_count': float('inf'), 'model_name': None, 'explanation': ['Skipped due to budget']} # Mock result
        else:
            initial_fix_result = fix_verification_errors(
                program=initial_program_contents,
                prompt=prompt,
                code=initial_code_contents,
                output=initial_output,
                strength=strength, # Use actual strength/temp for initial check
                temperature=temperature,
                verbose=verbose # Pass verbose flag down
            )
        last_fix_result = initial_fix_result # Store for potential later use
    except Exception as e:
        console.print(f"[bold red]Error during initial call to fix_verification_errors: {e}[/bold red]")
        stats['exit_reason'] = f"LLM Error: Initial fix_verification_errors call failed: {e}"
        # Log the error
        error_log = ET.Element("Error")
        error_log.set("timestamp", datetime.datetime.now().isoformat())
        error_log.set("phase", "InitialAssessment")
        _create_cdata_element(error_log, "ErrorMessage", str(e))
        _append_log_entry(verification_log_file, log_root, error_log)
        return {
            'success': False, 'final_program': initial_program_contents, 'final_code': initial_code_contents,
            'total_attempts': 0, 'total_cost': total_cost, 'model_name': model_name,
            'statistics': stats
        }


    # 3e: Add cost
    initial_cost = initial_fix_result.get('total_cost', 0.0)
    total_cost += initial_cost
    model_name = initial_fix_result.get('model_name', model_name) # Update model name

    # 3f: Extract initial issues
    initial_issues_count = initial_fix_result.get('verification_issues_count', float('inf'))
    if initial_issues_count == float('inf'):
         console.print("[yellow]Warning: Could not determine initial issue count from fix_verification_errors.[/yellow]")
         # Decide how to handle this - maybe treat as high number of issues?
         initial_issues_count = 999 # Assign a high number if undetermined

    stats['initial_issues'] = initial_issues_count
    if verbose:
        console.print(f"Initial assessment complete. Issues found: {initial_issues_count}, Cost: ${initial_cost:.6f}")

    # 3g: Initialize best iteration with initial state
    best_iteration['attempt'] = 0 # Representing the initial state before loop
    best_iteration['issues'] = initial_issues_count
    best_iteration['program_backup_path'] = program_file # Original file path
    best_iteration['code_backup_path'] = code_file     # Original file path
    best_iteration['model_name'] = model_name

    # Log initial assessment details
    initial_assessment_log = ET.Element("InitialAssessment")
    initial_assessment_log.set("timestamp", datetime.datetime.now().isoformat())
    initial_assessment_log.set("issues_found", str(initial_issues_count))
    initial_assessment_log.set("cost", f"{initial_cost:.6f}")
    if model_name:
         initial_assessment_log.set("model_name", model_name)
    _create_cdata_element(initial_assessment_log, "Explanation", "\n".join(initial_fix_result.get('explanation', [])))
    _append_log_entry(verification_log_file, log_root, initial_assessment_log)


    # 3h: Check if already successful
    if initial_issues_count == 0:
        console.print("[bold green]Initial state already meets verification criteria (0 issues found). No fixing loop needed.[/bold green]")
        overall_success = True
        stats['final_issues'] = 0
        stats['best_iteration_attempt'] = 0
        stats['best_iteration_issues'] = 0
        stats['improvement_issues'] = 0
        stats['overall_success_flag'] = True
        stats['exit_reason'] = "Success on Initial Assessment"
        # Skip to Step 7/8 (Return)

    # --- Step 4: Fixing Loop ---
    current_program_contents = initial_program_contents
    current_code_contents = initial_code_contents

    if not overall_success: # Only enter loop if initial state wasn't perfect
        if verbose:
            console.print(f"\n[bold]Step 4: Starting Fixing Loop (Max Attempts: {max_attempts}, Budget: ${budget:.2f})[/bold]")

        while attempts < max_attempts and total_cost < budget:
            attempt_number = attempts + 1
            if verbose:
                console.print(f"\n--- Attempt {attempt_number}/{max_attempts} --- Cost so far: ${total_cost:.6f}")

            # 4a: Log attempt start (done within iteration log)
            iteration_log = ET.Element("Iteration")
            iteration_log.set("attempt", str(attempt_number))
            iteration_log.set("timestamp", datetime.datetime.now().isoformat())

            # 4b: Run the program file
            run_success, program_output, _ = _run_subprocess(['python', program_file])
            if verbose:
                console.print(f"Program execution {'succeeded' if run_success else 'failed'}.")
                # console.print("[dim]Current Output:[/dim]")
                # console.print(f"[grey37]{program_output or '[No Output]'}[/grey37]") # Can be very long

            _create_cdata_element(iteration_log, "ProgramOutputBeforeFix", program_output)

            # 4c: Read current contents (already stored in current_*)

            # 4d: Create backups
            program_backup_path = _create_backup(program_file, attempt_number)
            code_backup_path = _create_backup(code_file, attempt_number)
            if program_backup_path: iteration_log.set("program_backup", program_backup_path)
            if code_backup_path: iteration_log.set("code_backup", code_backup_path)

            # 4e: Call fix_verification_errors
            if verbose:
                console.print("Calling 'fix_verification_errors' to suggest fixes...")
            try:
                fix_result = fix_verification_errors(
                    program=current_program_contents,
                    prompt=prompt,
                    code=current_code_contents,
                    output=program_output,
                    strength=strength,
                    temperature=temperature,
                    verbose=verbose # Pass verbose flag down
                )
                last_fix_result = fix_result # Store latest result
            except Exception as e:
                console.print(f"[bold red]Error during fix_verification_errors call in attempt {attempt_number}: {e}[/bold red]")
                stats['exit_reason'] = f"LLM Error: fix_verification_errors failed in loop: {e}"
                # Log the error and break
                error_log = ET.Element("Error")
                error_log.set("timestamp", datetime.datetime.now().isoformat())
                error_log.set("phase", f"FixAttempt_{attempt_number}")
                _create_cdata_element(error_log, "ErrorMessage", str(e))
                _append_log_entry(verification_log_file, log_root, error_log)
                break # Exit loop on LLM error

            # Log inputs and results to XML
            inputs_log = ET.SubElement(iteration_log, "InputsToFixer")
            _create_cdata_element(inputs_log, "Program", current_program_contents)
            _create_cdata_element(inputs_log, "Code", current_code_contents)
            _create_cdata_element(inputs_log, "Prompt", prompt)
            _create_cdata_element(inputs_log, "ProgramOutput", program_output)

            fixer_result_log = ET.SubElement(iteration_log, "FixerResult")
            fixer_result_log.set("cost", f"{fix_result.get('total_cost', 0.0):.6f}")
            fixer_result_log.set("model_name", fix_result.get('model_name', "Unknown"))
            fixer_result_log.set("issues_found", str(fix_result.get('verification_issues_count', 'inf')))
            _create_cdata_element(fixer_result_log, "Explanation", "\n".join(fix_result.get('explanation', [])))
            _create_cdata_element(fixer_result_log, "FixedProgramSuggestion", fix_result.get('fixed_program'))
            _create_cdata_element(fixer_result_log, "FixedCodeSuggestion", fix_result.get('fixed_code'))

            # 4f: Add cost
            attempt_cost = fix_result.get('total_cost', 0.0)
            total_cost += attempt_cost
            model_name = fix_result.get('model_name', model_name) # Update model name if available
            if verbose:
                console.print(f"Fix attempt cost: ${attempt_cost:.6f}, Total cost: ${total_cost:.6f}")
                console.print(f"Issues found by fixer: {fix_result.get('verification_issues_count', 'N/A')}")


            # 4h: Check budget
            if total_cost > budget:
                console.print(f"[bold yellow]Budget exceeded (${total_cost:.2f} > ${budget:.2f}). Stopping.[/bold yellow]")
                status_log = ET.SubElement(iteration_log, "Status")
                status_log.text = "Budget Exceeded"
                _append_log_entry(verification_log_file, log_root, iteration_log)
                stats['exit_reason'] = "Budget Exceeded"
                break

            # 4i: Check for success (0 issues)
            current_issues_count = fix_result.get('verification_issues_count', float('inf'))
            if current_issues_count == 0:
                console.print("[bold green]Success! Fixer reported 0 verification issues.[/bold green]")
                status_log = ET.SubElement(iteration_log, "Status")
                status_log.text = "Success - 0 Issues Found"

                # Update best iteration (0 issues is always the best)
                best_iteration['attempt'] = attempt_number
                best_iteration['issues'] = 0
                best_iteration['program_backup_path'] = program_backup_path # Backup before successful fix
                best_iteration['code_backup_path'] = code_backup_path     # Backup before successful fix
                best_iteration['model_name'] = model_name

                # Write final successful code/program
                final_program = fix_result.get('fixed_program', current_program_contents)
                final_code = fix_result.get('fixed_code', current_code_contents)
                program_written = _write_file(program_file, final_program)
                code_written = _write_file(code_file, final_code)

                if program_written and code_written:
                     current_program_contents = final_program # Update current state
                     current_code_contents = final_code
                     if verbose:
                         console.print("Applied final successful changes to files.")
                else:
                     console.print("[bold red]Error writing final successful files![/bold red]")
                     # Success flag might be compromised if write fails

                _append_log_entry(verification_log_file, log_root, iteration_log)
                overall_success = True
                stats['exit_reason'] = "Success - Reached 0 Issues"
                break

            # 4j: Check if changes were suggested
            fixed_program = fix_result.get('fixed_program', current_program_contents)
            fixed_code = fix_result.get('fixed_code', current_code_contents)
            program_updated = fixed_program != current_program_contents
            code_updated = fixed_code != current_code_contents

            if not program_updated and not code_updated:
                console.print("[yellow]No changes suggested by the fixer in this iteration. Stopping.[/yellow]")
                status_log = ET.SubElement(iteration_log, "Status")
                status_log.text = "No Changes Suggested"
                _append_log_entry(verification_log_file, log_root, iteration_log)
                stats['exit_reason'] = "No Changes Suggested by LLM"
                break

            # 4k, 4l: Log fix attempt details
            fix_attempt_log = ET.SubElement(iteration_log, "FixAttempted")
            fix_attempt_log.set("program_change_suggested", str(program_updated))
            fix_attempt_log.set("code_change_suggested", str(code_updated))

            # 4m, 4n: Secondary Verification (only if code was modified)
            secondary_verification_passed = True # Assume pass if code not changed
            secondary_verification_output = "Not Run (Code Unchanged)"

            if code_updated:
                if verbose:
                    console.print("Code change suggested. Running secondary verification...")
                # Use a temporary file for the modified code
                temp_code_file = None
                try:
                    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False, encoding='utf-8') as tf:
                        tf.write(fixed_code)
                        temp_code_file_path = tf.name
                    if verbose:
                        console.print(f"Wrote proposed code to temporary file: {temp_code_file_path}")

                    # Run the secondary verification program.
                    # It needs to know which code file to check. We pass the temp file path.
                    # Modify this command if your verification script takes args differently.
                    verify_command = ['python', verification_program, temp_code_file_path]
                    verify_success, verify_output, verify_rc = _run_subprocess(verify_command)

                    secondary_verification_passed = verify_success
                    secondary_verification_output = verify_output
                    if verbose:
                        console.print(f"Secondary verification {'PASSED' if verify_success else 'FAILED'} (Exit Code: {verify_rc}).")
                        # console.print(f"[dim]Verification Output:[/dim]\n[grey37]{verify_output or '[No Output]'}[/grey37]")

                except Exception as e:
                    console.print(f"[bold red]Error during secondary verification: {e}[/bold red]")
                    secondary_verification_passed = False
                    secondary_verification_output = f"Error during verification: {e}"
                finally:
                    # Clean up the temporary file
                    if temp_code_file_path and os.path.exists(temp_code_file_path):
                        try:
                            os.remove(temp_code_file_path)
                        except OSError as e:
                            console.print(f"[yellow]Warning: Could not remove temp file {temp_code_file_path}: {e}[/yellow]")

            # Log secondary verification result
            sec_verify_log = ET.SubElement(iteration_log, "SecondaryVerification")
            sec_verify_log.set("run", str(code_updated))
            sec_verify_log.set("passed", str(secondary_verification_passed))
            _create_cdata_element(sec_verify_log, "Output", secondary_verification_output)

            # 4o, 4p: Apply changes or discard based on secondary verification
            if secondary_verification_passed:
                if verbose:
                    console.print("Secondary verification passed (or not needed). Applying changes.")
                status_log = ET.SubElement(iteration_log, "Status")
                status_log.text = "Changes Applied (Secondary Verification Passed or Skipped)"

                # Update best iteration if this one is better
                if current_issues_count < best_iteration['issues']:
                    if verbose:
                        console.print(f"[green]Improvement found! Issues reduced from {best_iteration['issues']} to {current_issues_count}. Updating best iteration.[/green]")
                    best_iteration['attempt'] = attempt_number
                    best_iteration['issues'] = current_issues_count
                    best_iteration['program_backup_path'] = program_backup_path # Store backup *before* this successful step
                    best_iteration['code_backup_path'] = code_backup_path
                    best_iteration['model_name'] = model_name
                elif verbose and current_issues_count >= best_iteration['issues']:
                     console.print(f"Current issues ({current_issues_count}) not better than best ({best_iteration['issues']}). Best iteration remains attempt {best_iteration['attempt']}.")


                # Apply changes to files
                files_updated = True
                if code_updated:
                    if not _write_file(code_file, fixed_code):
                        files_updated = False
                        console.print(f"[bold red]Error writing updated code to {code_file}[/bold red]")
                    else:
                         current_code_contents = fixed_code # Update current state

                if program_updated:
                    if not _write_file(program_file, fixed_program):
                        files_updated = False
                        console.print(f"[bold red]Error writing updated program to {program_file}[/bold red]")
                    else:
                         current_program_contents = fixed_program # Update current state

                if not files_updated:
                     # If writing failed, we might be in an inconsistent state. Log it.
                     ET.SubElement(iteration_log, "Error").text = "Failed to write updated files after successful verification."


            else: # Secondary verification failed
                if verbose:
                    console.print("[bold red]Secondary verification failed. Discarding suggested changes for this iteration.[/bold red]")
                status_log = ET.SubElement(iteration_log, "Status")
                status_log.text = "Changes Discarded (Secondary Verification Failed)"
                # Do not update files, do not update best_iteration

            # 4q: Append log entry for the iteration
            _append_log_entry(verification_log_file, log_root, iteration_log)

            # 4r: Increment attempt counter
            attempts += 1

            # Check if max attempts reached
            if attempts >= max_attempts:
                console.print(f"[yellow]Maximum attempts ({max_attempts}) reached. Stopping.[/yellow]")
                stats['exit_reason'] = "Max Attempts Reached"
                # Add status to log if loop didn't break for other reasons already
                if iteration_log.find("Status") is None:
                     status_log = ET.SubElement(iteration_log, "Status")
                     status_log.text = "Max Attempts Reached"
                     _append_log_entry(verification_log_file, log_root, iteration_log) # Ensure last log is written


    # --- Step 5: Post-Loop Processing ---
    if verbose:
        console.print("\n[bold]Step 5: Post-Loop Processing[/bold]")

    final_action_log = ET.Element("FinalAction")
    final_action_log.set("timestamp", datetime.datetime.now().isoformat())

    if not overall_success:
        console.print("[yellow]Fixing loop finished without reaching 0 issues.[/yellow]")
        # Check if a 'best' iteration (better than initial and passed secondary verification) was found
        if best_iteration['attempt'] > 0 and best_iteration['issues'] < stats['initial_issues']:
            console.print(f"Restoring state from best recorded iteration: Attempt {best_iteration['attempt']} (Issues: {best_iteration['issues']})")
            restored_program = _restore_backup(best_iteration['program_backup_path'], program_file)
            restored_code = _restore_backup(best_iteration['code_backup_path'], code_file)
            if restored_program and restored_code:
                console.print("[green]Successfully restored files from the best iteration.[/green]")
                final_action_log.set("action", "RestoredBestIteration")
                final_action_log.set("best_attempt", str(best_iteration['attempt']))
                final_action_log.set("best_issues", str(best_iteration['issues']))
                stats['final_issues'] = best_iteration['issues'] # Final state has this many issues
            else:
                console.print("[bold red]Error restoring files from the best iteration! Final files might be from the last attempt.[/bold red]")
                final_action_log.set("action", "RestorationFailed")
                # Final issues remain from the last attempt before loop exit, or initial if no changes applied
                stats['final_issues'] = last_fix_result.get('verification_issues_count', stats['initial_issues']) if last_fix_result else stats['initial_issues']

        elif best_iteration['attempt'] == 0: # Best was the initial state
             console.print("No improvement found compared to the initial state. Keeping original files.")
             # No restoration needed, files should be in original state unless write failed earlier
             final_action_log.set("action", "NoImprovementFound")
             stats['final_issues'] = stats['initial_issues']
        else: # No iteration ever passed secondary verification or improved
            console.print("No verified improvement was found. Final files are from the last attempted state before loop exit.")
            final_action_log.set("action", "NoVerifiedImprovement")
            # Final issues remain from the last attempt before loop exit
            stats['final_issues'] = last_fix_result.get('verification_issues_count', stats['initial_issues']) if last_fix_result else stats['initial_issues']

    else: # overall_success is True
        console.print("[bold green]Process finished successfully![/bold green]")
        final_action_log.set("action", "Success")
        stats['final_issues'] = 0 # Success means 0 issues

    _append_log_entry(verification_log_file, log_root, final_action_log)

    # --- Step 6: Read Final Contents ---
    if verbose:
        console.print("\n[bold]Step 6: Reading Final File Contents[/bold]")
    final_program_contents = _read_file(program_file)
    final_code_contents = _read_file(code_file)
    if final_program_contents is None: final_program_contents = "Error reading final program file."
    if final_code_contents is None: final_code_contents = "Error reading final code file."

    # --- Step 7: Calculate and Print Summary Statistics ---
    if verbose:
        console.print("\n[bold]Step 7: Final Statistics[/bold]")

    stats['overall_success_flag'] = overall_success
    stats['best_iteration_attempt'] = best_iteration['attempt'] if best_iteration['attempt'] >= 0 else 'N/A'
    stats['best_iteration_issues'] = best_iteration['issues'] if best_iteration['issues'] != float('inf') else 'N/A'
    if stats['initial_issues'] != float('inf') and stats['final_issues'] != float('inf') and stats['initial_issues'] >= 0 and stats['final_issues'] >= 0:
         stats['improvement_issues'] = stats['initial_issues'] - stats['final_issues']
    else:
         stats['improvement_issues'] = 'N/A' # Cannot calculate if initial/final unknown

    summary_text = Text.assemble(
        ("Initial Issues: ", "bold"), str(stats['initial_issues']), "\n",
        ("Final Issues: ", "bold"), str(stats['final_issues']), "\n",
        ("Improvement (Issues Reduced): ", "bold"), str(stats['improvement_issues']), "\n",
        ("Best Iteration Attempt: ", "bold"), str(stats['best_iteration_attempt']), "\n",
        ("Best Iteration Issues: ", "bold"), str(stats['best_iteration_issues']), "\n",
        ("Total Attempts Made: ", "bold"), str(attempts), "\n",
        ("Total LLM Cost: ", "bold"), f"${total_cost:.6f}", "\n",
        ("Model Used (Last/Best): ", "bold"), str(best_iteration.get('model_name') or model_name or 'N/A'), "\n",
        ("Exit Reason: ", "bold"), stats['exit_reason'], "\n",
        ("Overall Success: ", "bold"), (str(overall_success), "bold green" if overall_success else "bold red")
    )
    console.print(Panel(summary_text, title="[bold blue]Verification Fix Loop Summary[/bold blue]", expand=False))

    # Finalize XML log
    log_root.set("endTime", datetime.datetime.now().isoformat())
    log_root.set("totalAttempts", str(attempts))
    log_root.set("totalCost", f"{total_cost:.6f}")
    log_root.set("overallSuccess", str(overall_success))
    # Re-write the log one last time with final attributes and pretty print
    try:
        rough_string = ET.tostring(log_root, 'utf-8')
        reparsed = minidom.parseString(rough_string)
        pretty_xml = reparsed.toprettyxml(indent="  ", encoding='utf-8')
        with open(verification_log_file, 'wb') as f:
            f.write(pretty_xml)
        if verbose:
            console.print(f"Final XML log written to: {verification_log_file}")
    except Exception as e:
        console.print(f"[bold red]Error writing final XML log file {verification_log_file}: {e}[/bold red]")


    # --- Step 8: Return Results ---
    return {
        'success': overall_success,
        'final_program': final_program_contents,
        'final_code': final_code_contents,
        'total_attempts': attempts,
        'total_cost': total_cost,
        'model_name': best_iteration.get('model_name') or model_name, # Prefer model from best iter, fallback to last used
        'statistics': stats,
    }

# Example Usage (Illustrative - requires setting up files and dependencies)
if __name__ == '__main__':
    console.print(Panel("[bold yellow]Running Example Usage[/bold yellow]\nThis is illustrative and requires setting up dummy files and potentially the 'fix_verification_errors' function/package.", title="Example"))

    # --- Create Dummy Files for Demonstration ---
    temp_dir = tempfile.mkdtemp()
    console.print(f"Created temporary directory: {temp_dir}")

    dummy_program_file = os.path.join(temp_dir, "program.py")
    dummy_code_file = os.path.join(temp_dir, "code_module.py")
    dummy_verify_file = os.path.join(temp_dir, "verify.py")
    log_file = os.path.join(temp_dir, "verification_log.xml")

    # Dummy Program (uses code_module, prints success/failure)
    _write_file(dummy_program_file, """
import code_module
import sys
try:
    result = code_module.buggy_function(5)
    expected = 10
    print(f"Input: 5")
    print(f"Expected: {expected}")
    print(f"Actual: {result}")
    if result == expected:
        print("VERIFICATION_SUCCESS")
        sys.exit(0)
    else:
        print(f"VERIFICATION_FAILURE: Expected {expected}, got {result}")
        sys.exit(1)
except Exception as e:
    print(f"VERIFICATION_ERROR: {e}")
    sys.exit(2)
""")

    # Dummy Code (initially buggy)
    _write_file(dummy_code_file, """
# Code module with a bug
def buggy_function(x):
    # Intended to return x * 2, but has a bug
    return x + 1 # Bug! Should be x * 2
""")

    # Dummy Verification Script (checks basic syntax/import)
    _write_file(dummy_verify_file, """
import sys
import importlib.util
import os

if len(sys.argv) < 2:
    print("Usage: python verify.py <path_to_code_module.py>")
    sys.exit(1)

module_path = sys.argv[1]
module_name = os.path.splitext(os.path.basename(module_path))[0]

try:
    spec = importlib.util.spec_from_file_location(module_name, module_path)
    if spec is None or spec.loader is None:
         raise ImportError(f"Could not create spec for {module_path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    # Optional: Check if specific functions exist
    if not hasattr(module, 'buggy_function'):
         raise AttributeError("Function 'buggy_function' not found.")
    print(f"Verification PASSED: {module_path} imported successfully.")
    sys.exit(0) # Success
except Exception as e:
    print(f"Verification FAILED: {e}")
    sys.exit(1) # Failure
""")

    # Dummy Prompt
    dummy_prompt = "Create a Python module 'code_module.py' with a function `buggy_function(x)` that returns the input `x` multiplied by 2."

    # --- Mock fix_verification_errors ---
    # In a real scenario, this would be the actual LLM call function
    # For this example, we simulate its behavior based on attempts
    _fix_call_count = 0
    def mock_fix_verification_errors(program, prompt, code, output, strength, temperature, verbose):
        global _fix_call_count
        _fix_call_count += 1
        cost = 0.01 + (strength * 0.02) # Simulate cost based on strength
        model = f"mock-model-s{strength:.1f}"
        issues = 1 # Default to 1 issue initially
        fixed_code = code # Default to no change
        explanation = ["Initial analysis: Function seems incorrect."]

        if "VERIFICATION_FAILURE" in output or "VERIFICATION_ERROR" in output:
            issues = 1
            if _fix_call_count <= 2: # Simulate fixing on the first or second try
                 # Simulate a fix
                 fixed_code = """
# Code module - Attempting fix
def buggy_function(x):
    # Intended to return x * 2
    return x * 2 # Corrected code
"""
                 explanation = ["Identified incorrect arithmetic operation. Changed '+' to '*'."]
                 issues = 0 # Simulate 0 issues after fix
                 if verbose: print("[Mock Fixer] Suggesting corrected code.")
            else:
                 explanation = ["Analysis: Still incorrect, unable to determine fix."]
                 issues = 1 # Simulate failure to fix after 2 tries
                 if verbose: print("[Mock Fixer] Failed to find fix this time.")
        elif "VERIFICATION_SUCCESS" in output:
             issues = 0
             explanation = ["Code appears correct based on output."]
             if verbose: print("[Mock Fixer] Code seems correct.")


        return {
            'explanation': explanation,
            'fixed_program': program, # Assume program doesn't change in mock
            'fixed_code': fixed_code,
            'total_cost': cost,
            'model_name': model,
            'verification_issues_count': issues,
        }

    # Replace the actual function with the mock for this example run
    original_fix_func = fix_verification_errors
    fix_verification_errors = mock_fix_verification_errors

    # --- Run the Loop ---
    try:
        results = fix_verification_errors_loop(
            program_file=dummy_program_file,
            code_file=dummy_code_file,
            prompt=dummy_prompt,
            verification_program=dummy_verify_file,
            strength=0.5,
            temperature=0.1,
            max_attempts=3,
            budget=0.50, # $0.50 budget
            verification_log_file=log_file,
            verbose=True
        )

        console.print("\n[bold magenta]--- Final Results ---[/bold magenta]")
        console.print(f"Success: {results['success']}")
        console.print(f"Total Attempts: {results['total_attempts']}")
        console.print(f"Total Cost: ${results['total_cost']:.6f}")
        console.print(f"Model Name: {results['model_name']}")

        console.print("\nFinal Code Content:")
        console.print(Syntax(results['final_code'], "python", theme="default", line_numbers=True))

        console.print("\nStatistics:")
        import json
        console.print(json.dumps(results['statistics'], indent=2))

        console.print(f"\nLog file generated at: {log_file}")

    except Exception as e:
        console.print(f"\n[bold red]An error occurred during the example run: {e}[/bold red]")
    finally:
        # Restore original function
        fix_verification_errors = original_fix_func
        # Clean up dummy files
        try:
            shutil.rmtree(temp_dir)
            console.print(f"Cleaned up temporary directory: {temp_dir}")
        except Exception as e:
            console.print(f"[bold red]Error cleaning up temp directory {temp_dir}: {e}[/bold red]")

