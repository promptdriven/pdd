import os
import sys
import subprocess
import shutil
import datetime
import tempfile
import xml.etree.ElementTree as ET
from xml.dom import minidom
from pathlib import Path
from typing import Dict, Any, List, Tuple, Optional

# Use Rich for pretty printing
from rich.console import Console
from rich.panel import Panel
from rich.syntax import Syntax
from rich.table import Table

# Assume fix_verification_errors is in the same package directory
# Use relative import
try:
    from .fix_verification_errors import fix_verification_errors
except ImportError:
    # Fallback for scenarios where the script might be run directly
    # or the package structure isn't fully set up during testing.
    # This assumes fix_verification_errors.py is in the same directory.
    print("Warning: Relative import failed. Attempting direct import.", file=sys.stderr)
    # In a real package, this fallback might not be desirable.
    # It's included here for potential standalone execution context.
    from fix_verification_errors import fix_verification_errors


# Initialize Rich Console
console = Console()

# --- Helper Functions ---

def _run_subprocess(command: List[str], verbose: bool = False) -> Dict[str, Any]:
    """
    Runs a subprocess command, captures stdout/stderr, and returns results.

    Args:
        command: A list of strings representing the command and its arguments.
        verbose: If True, print command being executed.

    Returns:
        A dictionary containing:
            'output': Combined stdout and stderr as a string.
            'returncode': The exit code of the process.
            'success': Boolean indicating if return code was 0.
            'error': Error message if subprocess fails to start, else None.
    """
    if verbose:
        console.print(f"[dim]Executing: {' '.join(command)}[/dim]")
    try:
        process = subprocess.run(
            command,
            capture_output=True,
            text=True,
            check=False, # Don't raise exception on non-zero exit
            encoding='utf-8',
            errors='replace' # Handle potential encoding issues
        )
        output = process.stdout + process.stderr
        success = process.returncode == 0
        if verbose and not success:
             console.print(f"[yellow]Subprocess finished with non-zero exit code: {process.returncode}[/yellow]")
        elif verbose:
             console.print(f"[dim]Subprocess finished successfully (exit code 0).[/dim]")

        return {
            "output": output.strip(),
            "returncode": process.returncode,
            "success": success,
            "error": None,
        }
    except FileNotFoundError:
        error_msg = f"Error: Command not found: '{command[0]}'. Please ensure it's installed and in PATH."
        console.print(f"[bold red]{error_msg}[/bold red]")
        return {"output": "", "returncode": -1, "success": False, "error": error_msg}
    except Exception as e:
        error_msg = f"Subprocess execution failed: {e}"
        console.print(f"[bold red]{error_msg}[/bold red]")
        return {"output": "", "returncode": -1, "success": False, "error": error_msg}

def _read_file(file_path: str, verbose: bool = False) -> Optional[str]:
    """Reads a file and returns its content, handling errors."""
    try:
        return Path(file_path).read_text(encoding='utf-8')
    except FileNotFoundError:
        console.print(f"[bold red]Error: File not found: {file_path}[/bold red]")
        return None
    except IOError as e:
        console.print(f"[bold red]Error reading file {file_path}: {e}[/bold red]")
        return None

def _write_file(file_path: str, content: str, verbose: bool = False) -> bool:
    """Writes content to a file, handling errors."""
    try:
        Path(file_path).write_text(content, encoding='utf-8')
        if verbose:
            console.print(f"[dim]Successfully wrote to {file_path}[/dim]")
        return True
    except IOError as e:
        console.print(f"[bold red]Error writing file {file_path}: {e}[/bold red]")
        return False
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred writing to {file_path}: {e}[/bold red]")
        return False

def _create_backup(file_path_str: str, iteration: int, verbose: bool = False) -> Optional[str]:
    """Creates a backup copy of a file with iteration number."""
    file_path = Path(file_path_str)
    backup_path = file_path.with_name(f"{file_path.stem}_iteration_{iteration}{file_path.suffix}")
    try:
        shutil.copy2(file_path, backup_path) # copy2 preserves metadata
        if verbose:
            console.print(f"[dim]Created backup: {backup_path}[/dim]")
        return str(backup_path)
    except FileNotFoundError:
        console.print(f"[yellow]Warning: Could not create backup for non-existent file: {file_path_str}[/yellow]")
        return None
    except Exception as e:
        console.print(f"[bold red]Error creating backup for {file_path_str}: {e}[/bold red]")
        return None

def _restore_from_backup(backup_path_str: str, original_path_str: str, verbose: bool = False) -> bool:
    """Restores a file from its backup."""
    if not backup_path_str or not Path(backup_path_str).exists():
        console.print(f"[bold red]Error: Cannot restore, backup file not found: {backup_path_str}[/bold red]")
        return False
    try:
        shutil.copy2(backup_path_str, original_path_str)
        if verbose:
            console.print(f"[cyan]Restored '{original_path_str}' from '{backup_path_str}'[/cyan]")
        return True
    except Exception as e:
        console.print(f"[bold red]Error restoring {original_path_str} from {backup_path_str}: {e}[/bold red]")
        return False

def _append_xml_log_entry(root: ET.Element, entry: ET.Element, log_file: str, verbose: bool = False):
    """Appends an XML entry to the log file with pretty printing."""
    root.append(entry)
    try:
        # Use minidom for pretty printing
        rough_string = ET.tostring(root, 'utf-8')
        reparsed = minidom.parseString(rough_string)
        pretty_xml_as_string = reparsed.toprettyxml(indent="  ", encoding='utf-8')

        with open(log_file, "wb") as f: # Write bytes
            f.write(pretty_xml_as_string)
        if verbose:
            console.print(f"[dim]Appended entry to log file: {log_file}[/dim]")
    except Exception as e:
        console.print(f"[bold red]Error writing XML log file {log_file}: {e}[/bold red]")

def _create_cdata_element(parent: ET.Element, tag_name: str, text: Optional[str]):
    """Creates an element with CDATA content."""
    element = ET.SubElement(parent, tag_name)
    # ET doesn't natively support CDATA easily, wrap manually for clarity in XML
    element.text = f"<![CDATA[\n{text or ''}\n]]>"


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
    verbose: bool = False,
) -> Dict[str, Any]:
    """
    Attempts to fix errors in a code file iteratively based on program execution.

    Args:
        program_file: Path to the Python program exercising the code_file.
        code_file: Path to the code file being tested/verified.
        prompt: The prompt that generated the code under test.
        verification_program: Path to a secondary Python program for basic code verification.
        strength: LLM strength parameter (0.0 to 1.0).
        temperature: LLM temperature parameter (>= 0.0).
        max_attempts: Maximum number of fix attempts.
        budget: Maximum allowed cost for LLM calls.
        verification_log_file: Path for detailed XML logging (default: "verification_log.xml").
        verbose: Enable detailed console logging (default: False).

    Returns:
        A dictionary containing:
            'success': Boolean indicating if the code was successfully fixed.
            'final_program': Contents of the final program file.
            'final_code': Contents of the final code file.
            'total_attempts': Number of fix attempts made.
            'total_cost': Total cost incurred.
            'model_name': Name of the LLM model used (last successful call).
            'statistics': Dictionary with detailed statistics.
    """
    console.print(Panel(f"Starting Verification Fix Loop for [cyan]{code_file}[/cyan]", title="[bold blue]Process Start[/bold blue]", expand=False))

    # --- Step 1: Initialize Log File ---
    log_file_path = Path(verification_log_file)
    try:
        if log_file_path.exists():
            log_file_path.unlink()
            if verbose:
                console.print(f"[dim]Removed existing log file: {verification_log_file}[/dim]")
    except OSError as e:
        console.print(f"[bold red]Error removing existing log file {verification_log_file}: {e}[/bold red]")
        # Continue execution, but logging might be appended if file couldn't be deleted

    # Initialize XML root
    xml_root = ET.Element("VerificationLog", timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat())

    # --- Step 2: Initialize Variables ---
    total_attempts = 0
    total_cost = 0.0
    model_name = "N/A" # Default if no LLM call is made
    overall_success = False
    program_file_path = Path(program_file)
    code_file_path = Path(code_file)

    # Best iteration tracker (stores state *before* the fix attempt)
    # Attempt 0 represents the initial state
    best_iteration = {
        'attempt': 0, # Start with initial state as potential best
        'issues': float('inf'),
        'program_backup': str(program_file_path.resolve()), # Original path
        'code_backup': str(code_file_path.resolve()),       # Original path
    }

    stats = {
        'initial_issues': -1,
        'final_issues': -1,
        'best_iteration_attempt': -1,
        'best_iteration_issues': float('inf'),
        'improvement_issues': 0,
        'improvement_percent': 0.0,
        'budget_exceeded': False,
        'max_attempts_reached': False,
        'no_changes_suggested': False,
        'secondary_verification_failures': 0,
    }

    # --- Step 3: Determine Initial State ---
    if verbose:
        console.print("[cyan]Step 3: Determining Initial State...[/cyan]")

    # 3a: Run initial program
    initial_program_contents = _read_file(program_file, verbose)
    initial_code_contents = _read_file(code_file, verbose)

    if initial_program_contents is None or initial_code_contents is None:
        console.print("[bold red]Error: Cannot proceed without initial program and code files.[/bold red]")
        _append_xml_log_entry(xml_root, ET.Element("Error", text="Initial program or code file missing"), verification_log_file, verbose)
        return {
            'success': False, 'final_program': initial_program_contents or "", 'final_code': initial_code_contents or "",
            'total_attempts': 0, 'total_cost': 0.0, 'model_name': model_name, 'statistics': stats
        }

    initial_run_result = _run_subprocess([sys.executable, program_file], verbose)
    initial_output = initial_run_result["output"]

    # 3b: Log initial state
    initial_state_entry = ET.Element("InitialState", timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat())
    _create_cdata_element(initial_state_entry, "ProgramOutput", initial_output)
    _create_cdata_element(initial_state_entry, "ProgramFileContent", initial_program_contents)
    _create_cdata_element(initial_state_entry, "CodeFileContent", initial_code_contents)
    _append_xml_log_entry(xml_root, initial_state_entry, verification_log_file, verbose)

    # 3d: Call fix_verification_errors for initial assessment
    if verbose:
        console.print("[dim]Calling fix_verification_errors for initial assessment...[/dim]")
    try:
        initial_fix_result = fix_verification_errors(
            program=initial_program_contents,
            prompt=prompt,
            code=initial_code_contents,
            output=initial_output,
            strength=strength, # Use provided strength for consistency
            temperature=temperature, # Use provided temp
            verbose=verbose
        )
    except Exception as e:
        console.print(f"[bold red]Error calling fix_verification_errors during initial assessment: {e}[/bold red]")
        error_entry = ET.SubElement(initial_state_entry, "Error", text=f"fix_verification_errors call failed: {e}")
        _append_xml_log_entry(xml_root, initial_state_entry, verification_log_file, verbose) # Update log with error
        return {
            'success': False, 'final_program': initial_program_contents, 'final_code': initial_code_contents,
            'total_attempts': 0, 'total_cost': total_cost, 'model_name': model_name, 'statistics': stats
        }


    # 3e: Add initial cost
    initial_cost = initial_fix_result.get('total_cost', 0.0)
    total_cost += initial_cost
    model_name = initial_fix_result.get('model_name', model_name) # Capture model name

    # 3f: Extract initial issues
    initial_issues = initial_fix_result.get('verification_issues_count', float('inf'))
    if initial_issues == float('inf'):
         console.print("[yellow]Warning: Could not determine initial issue count from fix_verification_errors.[/yellow]")
         initial_issues = -1 # Indicate unknown

    stats['initial_issues'] = initial_issues
    initial_state_entry.set("issues_found", str(initial_issues)) # Add to XML
    initial_state_entry.set("cost", f"{initial_cost:.6f}")
    initial_state_entry.set("model_name", model_name)
    _append_xml_log_entry(xml_root, initial_state_entry, verification_log_file, verbose) # Update log

    # 3g: Initialize best iteration tracker
    best_iteration['issues'] = initial_issues
    stats['best_iteration_attempt'] = 0
    stats['best_iteration_issues'] = initial_issues
    console.print(f"Initial verification issues found: [bold yellow]{initial_issues if initial_issues >= 0 else 'Unknown'}[/bold yellow]")

    # 3h: Check for initial success
    if initial_issues == 0:
        console.print("[bold green]Initial state already meets verification criteria (0 issues). No loop needed.[/bold green]")
        overall_success = True
        stats['final_issues'] = 0
        stats['improvement_percent'] = 100.0
        # No attempts made in the loop
    elif total_cost >= budget:
         console.print(f"[bold red]Budget Exceeded ({total_cost:.4f} >= {budget:.4f}) during initial assessment.[/bold red]")
         stats['budget_exceeded'] = True
         stats['final_issues'] = initial_issues # Final state is initial state
         # No attempts made in the loop

    # --- Step 4: Iteration Loop ---
    current_program_contents = initial_program_contents
    current_code_contents = initial_code_contents

    while total_attempts < max_attempts and total_cost < budget and not overall_success:
        total_attempts += 1
        iteration_start_time = datetime.datetime.now(datetime.timezone.utc)
        console.print(f"\n--- Starting Attempt {total_attempts}/{max_attempts} ---")
        if verbose:
            console.print(f"Current Total Cost: ${total_cost:.4f} / Budget: ${budget:.4f}")

        iteration_entry = ET.Element("Iteration",
                                     attempt=str(total_attempts),
                                     timestamp=iteration_start_time.isoformat())

        # 4b: Run program
        if verbose:
            console.print(f"[dim]Running program: {program_file}[/dim]")
        run_result = _run_subprocess([sys.executable, str(program_file_path)], verbose)
        program_output = run_result["output"]
        _create_cdata_element(iteration_entry, "ProgramOutputBeforeFix", program_output)

        # 4c: Read current contents (redundant if tracking internally, but safer from file)
        current_program_contents = _read_file(str(program_file_path), verbose)
        current_code_contents = _read_file(str(code_file_path), verbose)
        if current_program_contents is None or current_code_contents is None:
             console.print("[bold red]Error reading program/code file during loop. Aborting.[/bold red]")
             ET.SubElement(iteration_entry, "Status", text="Error Reading Files")
             _append_xml_log_entry(xml_root, iteration_entry, verification_log_file, verbose)
             break # Exit loop on file read error

        # 4d: Create backups *before* calling the fixer
        program_backup_path = _create_backup(str(program_file_path), total_attempts, verbose)
        code_backup_path = _create_backup(str(code_file_path), total_attempts, verbose)

        # 4e: Call fix_verification_errors
        if verbose:
            console.print("[dim]Calling fix_verification_errors...[/dim]")
        try:
            fix_result = fix_verification_errors(
                program=current_program_contents,
                prompt=prompt,
                code=current_code_contents,
                output=program_output,
                strength=strength,
                temperature=temperature,
                verbose=verbose
            )
        except Exception as e:
            console.print(f"[bold red]Error calling fix_verification_errors in attempt {total_attempts}: {e}[/bold red]")
            ET.SubElement(iteration_entry, "Status", text=f"Fixer Error: {e}")
            _append_xml_log_entry(xml_root, iteration_entry, verification_log_file, verbose)
            # Decide whether to continue or break? Let's break for safety.
            break

        # 4f: Add cost
        attempt_cost = fix_result.get('total_cost', 0.0)
        total_cost += attempt_cost
        model_name = fix_result.get('model_name', model_name) # Update model name

        # 4g: Log inputs and results to XML
        inputs_entry = ET.SubElement(iteration_entry, "InputsToFixer")
        _create_cdata_element(inputs_entry, "ProgramContent", current_program_contents)
        _create_cdata_element(inputs_entry, "CodeContent", current_code_contents)
        _create_cdata_element(inputs_entry, "Prompt", prompt)
        _create_cdata_element(inputs_entry, "ProgramOutput", program_output)

        fixer_result_entry = ET.SubElement(iteration_entry, "FixerResult")
        fixer_result_entry.set("cost", f"{attempt_cost:.6f}")
        fixer_result_entry.set("model_name", model_name)
        fixer_result_entry.set("issues_found", str(fix_result.get('verification_issues_count', 'N/A')))
        _create_cdata_element(fixer_result_entry, "Explanation", "\n".join(fix_result.get('explanation', [])))
        _create_cdata_element(fixer_result_entry, "FixedProgramSuggestion", fix_result.get('fixed_program'))
        _create_cdata_element(fixer_result_entry, "FixedCodeSuggestion", fix_result.get('fixed_code'))

        # 4h: Check budget
        if total_cost >= budget:
            console.print(f"[bold red]Budget Exceeded ({total_cost:.4f} >= {budget:.4f}) after attempt {total_attempts}.[/bold red]")
            ET.SubElement(iteration_entry, "Status", text="Budget Exceeded")
            _append_xml_log_entry(xml_root, iteration_entry, verification_log_file, verbose)
            stats['budget_exceeded'] = True
            break

        # 4i: Check for success (0 issues)
        current_issues = fix_result.get('verification_issues_count', float('inf'))
        if current_issues == 0:
            console.print(f"[bold green]Success! 0 verification issues found in attempt {total_attempts}.[/bold green]")
            ET.SubElement(iteration_entry, "Status", text="Success - 0 Issues Found")
            overall_success = True
            stats['final_issues'] = 0
            stats['improvement_percent'] = 100.0

            # Update best iteration (this is definitively the best)
            best_iteration = {
                'attempt': total_attempts,
                'issues': 0,
                'program_backup': program_backup_path, # Backup *before* this successful fix
                'code_backup': code_backup_path,
            }
            stats['best_iteration_attempt'] = total_attempts
            stats['best_iteration_issues'] = 0

            # Write the successful code/program
            fixed_program = fix_result.get('fixed_program', current_program_contents)
            fixed_code = fix_result.get('fixed_code', current_code_contents)
            program_updated = fixed_program != current_program_contents
            code_updated = fixed_code != current_code_contents

            if program_updated:
                 _write_file(str(program_file_path), fixed_program, verbose)
            if code_updated:
                 _write_file(str(code_file_path), fixed_code, verbose)

            _append_xml_log_entry(xml_root, iteration_entry, verification_log_file, verbose)
            break # Exit loop on success

        # 4j: Check if changes were suggested
        fixed_program = fix_result.get('fixed_program', current_program_contents)
        fixed_code = fix_result.get('fixed_code', current_code_contents)
        program_updated = fixed_program != current_program_contents
        code_updated = fixed_code != current_code_contents

        if not program_updated and not code_updated:
            console.print(f"[yellow]No changes suggested by the fixer in attempt {total_attempts}. Stopping.[/yellow]")
            ET.SubElement(iteration_entry, "Status", text="No Changes Suggested")
            _append_xml_log_entry(xml_root, iteration_entry, verification_log_file, verbose)
            stats['no_changes_suggested'] = True
            # Keep overall_success as False
            break

        # 4l: Log fix attempt
        fix_attempt_entry = ET.SubElement(iteration_entry, "FixAttempted")
        fix_attempt_entry.set("program_change_suggested", str(program_updated))
        fix_attempt_entry.set("code_change_suggested", str(code_updated))

        # 4m, 4n: Secondary Verification
        secondary_verification_passed = True # Assume pass if code not updated or no verifier
        if code_updated and verification_program:
            if verbose:
                console.print(f"[dim]Running secondary verification: {verification_program}[/dim]")

            # Use a temporary file for the proposed code change
            try:
                with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False, encoding='utf-8') as temp_code_file:
                    temp_code_file.write(fixed_code)
                    temp_code_file_path = temp_code_file.name

                # Run verification program against the temp file
                verify_cmd = [sys.executable, verification_program, temp_code_file_path]
                verify_result = _run_subprocess(verify_cmd, verbose)

                secondary_verification_passed = verify_result["success"] # Assume exit code 0 is success

                # Log secondary verification result
                sec_verify_entry = ET.SubElement(iteration_entry, "SecondaryVerification")
                sec_verify_entry.set("passed", str(secondary_verification_passed))
                sec_verify_entry.set("return_code", str(verify_result["returncode"]))
                _create_cdata_element(sec_verify_entry, "Output", verify_result["output"])

                if not secondary_verification_passed:
                    console.print(f"[yellow]Secondary verification failed for attempt {total_attempts}. Discarding changes.[/yellow]")
                    stats['secondary_verification_failures'] += 1

            except Exception as e:
                console.print(f"[bold red]Error during secondary verification: {e}[/bold red]")
                secondary_verification_passed = False # Treat error as failure
                ET.SubElement(iteration_entry, "SecondaryVerification", passed="False", error=f"Exception: {e}")
            finally:
                # Clean up temporary file
                if 'temp_code_file_path' in locals() and Path(temp_code_file_path).exists():
                    try:
                        Path(temp_code_file_path).unlink()
                    except OSError:
                        pass # Ignore cleanup error

        elif code_updated and not verification_program:
             if verbose:
                 console.print("[dim]Code updated, but no secondary verification program provided. Skipping check.[/dim]")
             ET.SubElement(iteration_entry, "SecondaryVerification", passed="True", status="Skipped - No verification program provided")


        # 4o, 4p: Apply or Discard Changes based on Secondary Verification
        if secondary_verification_passed:
            console.print(f"[green]Attempt {total_attempts}: Changes passed secondary verification (or not needed). Applying.[/green]")
            console.print(f"Issues found by fixer in this attempt: [bold yellow]{current_issues if current_issues != float('inf') else 'Unknown'}[/bold yellow]")

            # Update best iteration if this one is better
            if current_issues < best_iteration['issues']:
                console.print(f"[cyan]Improvement found! Issues reduced from {best_iteration['issues']} to {current_issues}. Updating best iteration.[/cyan]")
                best_iteration = {
                    'attempt': total_attempts,
                    'issues': current_issues,
                    'program_backup': program_backup_path, # Backup *before* this fix
                    'code_backup': code_backup_path,
                }
                stats['best_iteration_attempt'] = total_attempts
                stats['best_iteration_issues'] = current_issues

            # Apply changes to files
            write_success = True
            if code_updated:
                if not _write_file(str(code_file_path), fixed_code, verbose):
                    write_success = False
            if program_updated:
                 if not _write_file(str(program_file_path), fixed_program, verbose):
                     write_success = False

            if write_success:
                 ET.SubElement(iteration_entry, "Status", text="Changes Applied (Secondary Verification Passed/Skipped)")
                 # Update internal tracking of content
                 current_program_contents = fixed_program
                 current_code_contents = fixed_code
            else:
                 console.print("[bold red]Failed to write updated files after successful verification. Stopping.[/bold red]")
                 ET.SubElement(iteration_entry, "Status", text="Error Writing Applied Changes")
                 _append_xml_log_entry(xml_root, iteration_entry, verification_log_file, verbose)
                 break # Stop if we can't write the files

        else: # Secondary verification failed
            ET.SubElement(iteration_entry, "Action", text="Changes Discarded Due To Secondary Verification Failure")
            # Do not update files, do not update best_iteration based on this attempt's issue count

        # 4q: Append iteration log entry
        _append_xml_log_entry(xml_root, iteration_entry, verification_log_file, verbose)

        # Loop continues (check max_attempts, budget)

    # --- End of Loop ---
    if not overall_success and total_attempts >= max_attempts:
        console.print(f"[bold yellow]Maximum attempts ({max_attempts}) reached.[/bold yellow]")
        stats['max_attempts_reached'] = True
        action_entry = ET.Element("Action", timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(), text="Max attempts reached")
        _append_xml_log_entry(xml_root, action_entry, verification_log_file, verbose)


    # --- Step 5: Determine Final State and Restore if Necessary ---
    if not overall_success:
        console.print("[yellow]Fixing process did not result in 0 issues.[/yellow]")
        # Check if any iteration *ever* resulted in a verified improvement (even if not 0 issues)
        if stats['best_iteration_attempt'] > 0 and stats['best_iteration_issues'] < stats['initial_issues']:
            console.print(f"[cyan]Restoring state from best recorded iteration: Attempt {stats['best_iteration_attempt']} (Issues: {stats['best_iteration_issues']})[/cyan]")
            restored_program = _restore_from_backup(best_iteration['program_backup'], str(program_file_path), verbose)
            restored_code = _restore_from_backup(best_iteration['code_backup'], str(code_file_path), verbose)

            action_entry = ET.Element("Action", timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat())
            action_entry.text = f"Restored Best Iteration {stats['best_iteration_attempt']} (Issues: {stats['best_iteration_issues']})"
            action_entry.set("program_restored", str(restored_program))
            action_entry.set("code_restored", str(restored_code))
            _append_xml_log_entry(xml_root, action_entry, verification_log_file, verbose)

            # Final issue count is the best recorded one
            stats['final_issues'] = stats['best_iteration_issues']

        elif stats['initial_issues'] != float('inf') and stats['initial_issues'] <= stats['best_iteration_issues']:
             # Initial state was the best (or equal best), restore originals if loop ran
             if total_attempts > 0:
                 console.print(f"[cyan]Initial state (Issues: {stats['initial_issues']}) was the best or only valid state. Restoring original files.[/cyan]")
                 # Best iteration still holds original paths if attempt is 0
                 restored_program = _restore_from_backup(best_iteration['program_backup'], str(program_file_path), verbose)
                 restored_code = _restore_from_backup(best_iteration['code_backup'], str(code_file_path), verbose)
                 action_entry = ET.Element("Action", timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat())
                 action_entry.text = f"Restored Original State (Issues: {stats['initial_issues']})"
                 action_entry.set("program_restored", str(restored_program))
                 action_entry.set("code_restored", str(restored_code))
                 _append_xml_log_entry(xml_root, action_entry, verification_log_file, verbose)
             else:
                 console.print(f"[cyan]Initial state (Issues: {stats['initial_issues']}) was the best. No changes applied.[/cyan]")

             stats['final_issues'] = stats['initial_issues']
        else:
            # No successful verification passed, or initial state was unknown/worse
            console.print("[yellow]No verified improvement found. Final state is the result of the last attempted change (or initial state if no attempts made/verified).[/yellow]")
            action_entry = ET.Element("Action", timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat())
            action_entry.text = "No successful iteration found or restored; final state is from last attempt/initial."
            _append_xml_log_entry(xml_root, action_entry, verification_log_file, verbose)
            # Final issues remain as the best recorded (could be inf if nothing worked)
            stats['final_issues'] = stats['best_iteration_issues'] if stats['best_iteration_issues'] != float('inf') else stats['initial_issues']


    # --- Step 6: Read Final Contents ---
    final_program = _read_file(str(program_file_path), verbose)
    final_code = _read_file(str(code_file_path), verbose)
    if final_program is None: final_program = "Error reading final program file."
    if final_code is None: final_code = "Error reading final code file."

    # --- Step 7: Calculate Final Statistics ---
    if stats['initial_issues'] >= 0 and stats['final_issues'] >= 0:
         stats['improvement_issues'] = stats['initial_issues'] - stats['final_issues']
    # Improvement percentage based on reaching 0 issues
    stats['improvement_percent'] = 100.0 if overall_success else 0.0

    # --- Print Summary ---
    summary_table = Table(title="Verification Fix Loop Summary", show_header=True, header_style="bold magenta")
    summary_table.add_column("Metric", style="dim", width=30)
    summary_table.add_column("Value")

    summary_table.add_row("Overall Success", "[bold green]True[/bold green]" if overall_success else "[bold red]False[/bold red]")
    summary_table.add_row("Total Attempts Made", str(total_attempts))
    summary_table.add_row("Total LLM Cost", f"${total_cost:.6f}")
    summary_table.add_row("LLM Model Used (Last)", model_name)
    summary_table.add_row("Initial Issues", str(stats['initial_issues']) if stats['initial_issues'] >= 0 else "Unknown")
    summary_table.add_row("Final Issues", str(stats['final_issues']) if stats['final_issues'] >= 0 else ("Unknown" if stats['final_issues'] == float('inf') else str(stats['final_issues'])))
    summary_table.add_row("Best Iteration Attempt", str(stats['best_iteration_attempt']) if stats['best_iteration_attempt'] >= 0 else "N/A")
    summary_table.add_row("Best Iteration Issues", str(stats['best_iteration_issues']) if stats['best_iteration_issues'] != float('inf') else "N/A")
    summary_table.add_row("Issue Reduction", str(stats['improvement_issues']) if stats['initial_issues'] >= 0 and stats['final_issues'] >= 0 else "N/A")
    summary_table.add_row("Improvement % (Reached 0 Issues)", f"{stats['improvement_percent']:.1f}%")
    summary_table.add_row("Budget Exceeded", "[bold red]Yes[/bold red]" if stats['budget_exceeded'] else "No")
    summary_table.add_row("Max Attempts Reached", "[bold yellow]Yes[/bold yellow]" if stats['max_attempts_reached'] else "No")
    summary_table.add_row("Stopped - No Changes Suggested", "[bold yellow]Yes[/bold yellow]" if stats['no_changes_suggested'] else "No")
    summary_table.add_row("Secondary Verification Failures", str(stats['secondary_verification_failures']))
    summary_table.add_row("Log File", verification_log_file)

    console.print(summary_table)

    # --- Step 8: Return Results ---
    return {
        'success': overall_success,
        'final_program': final_program,
        'final_code': final_code,
        'total_attempts': total_attempts,
        'total_cost': total_cost,
        'model_name': model_name,
        'statistics': stats,
    }

# Example Usage (requires setting up dummy files and potentially the pdd package)
if __name__ == '__main__':
    # This example requires dummy files and the 'fix_verification_errors' function
    # to be available (either via package or direct import fallback).
    # You would need to create:
    # 1. dummy_program.py (e.g., imports dummy_code and prints output)
    # 2. dummy_code.py (e.g., a simple function, maybe with a bug)
    # 3. dummy_verifier.py (e.g., checks syntax of a given file path argument)
    # 4. A prompt string.

    console.print(Panel("[bold yellow]Running Example Usage[/bold yellow]", expand=False))

    # Create dummy files for demonstration
    dummy_dir = Path("./dummy_fix_loop_test")
    dummy_dir.mkdir(exist_ok=True)

    program_file = dummy_dir / "dummy_program.py"
    code_file = dummy_dir / "dummy_code.py"
    verifier_file = dummy_dir / "dummy_verifier.py"

    # Dummy Program (tries to use the code)
    program_content = """
import dummy_code
import sys
try:
    result = dummy_code.buggy_multiply(5, 3)
    expected = 15
    print(f"Input: 5, 3")
    print(f"Expected: {expected}")
    print(f"Actual: {result}")
    if result == expected:
        print("VERIFICATION_SUCCESS: Correct result!")
    else:
        print(f"VERIFICATION_FAILURE: Incorrect result! Got {result}, expected {expected}")
        sys.exit(1) # Indicate failure via exit code too
except Exception as e:
    print(f"VERIFICATION_FAILURE: Error during execution: {e}")
    sys.exit(1)
"""
    program_file.write_text(program_content)

    # Dummy Code (with a bug)
    code_content_buggy = """
# Dummy code module
def buggy_multiply(a, b):
    '''Intended to multiply, but adds instead.'''
    print("Running buggy_multiply...") # Add some output
    return a + b # Bug: should be a * b
"""
    code_file.write_text(code_content_buggy)

    # Dummy Verifier (simple syntax check)
    verifier_content = """
import sys
import ast

if len(sys.argv) < 2:
    print("Verifier Error: No file path provided.")
    sys.exit(2)

file_path = sys.argv[1]
print(f"Verifier: Checking syntax of {file_path}")
try:
    with open(file_path, 'r') as f:
        source = f.read()
    ast.parse(source)
    print("Verifier: Syntax OK.")
    sys.exit(0) # Success
except FileNotFoundError:
    print(f"Verifier Error: File not found: {file_path}")
    sys.exit(3)
except SyntaxError as e:
    print(f"Verifier Error: Syntax error in {file_path}: {e}")
    sys.exit(1) # Failure
except Exception as e:
    print(f"Verifier Error: Unexpected error checking {file_path}: {e}")
    sys.exit(4)
"""
    verifier_file.write_text(verifier_content)

    # Dummy Prompt
    prompt_text = "Create a Python module 'dummy_code.py' with a function `buggy_multiply(a, b)` that returns the product of a and b."

    # --- Mock fix_verification_errors ---
    # In a real scenario, this would be the actual LLM call function.
    # Here, we mock it to simulate behavior for the example.
    _original_fix_verification_errors = fix_verification_errors # Keep original if exists
    _fix_call_count = 0
    def mock_fix_verification_errors(program, prompt, code, output, strength, temperature, verbose):
        global _fix_call_count
        _fix_call_count += 1
        cost = 0.001 * strength + 0.0005 # Dummy cost calculation
        model = f"mock-model-s{strength:.1f}"
        explanation = ["Analysis based on output."]
        issues_count = 1 # Default to 1 issue found

        fixed_program = program # Assume program doesn't need fixing
        fixed_code = code # Default to no change

        if "VERIFICATION_FAILURE" in output:
            explanation.append("Detected verification failure in output.")
            if "Incorrect result" in output and "a + b" in code:
                 explanation.append("Identified potential addition bug instead of multiplication.")
                 # Suggest the fix on the first few calls
                 if _fix_call_count <= 2:
                     fixed_code = code.replace("a + b", "a * b", 1)
                     explanation.append("Suggested fix: Changed '+' to '*'.")
                     issues_count = 0 # Assume fix resolves the issue
                 else:
                     explanation.append("Previously suggested fix, but assuming it didn't work.")
                     issues_count = 1 # Keep issues count > 0 if fix keeps failing
            else:
                 explanation.append("Could not pinpoint specific fix.")
                 issues_count = 1
        elif "VERIFICATION_SUCCESS" in output:
            explanation.append("Detected verification success.")
            issues_count = 0
        else:
            explanation.append("Output does not contain clear SUCCESS/FAILURE markers.")
            issues_count = 1 # Assume issues if unclear

        return {
            'explanation': explanation,
            'fixed_program': fixed_program,
            'fixed_code': fixed_code,
            'total_cost': cost,
            'model_name': model,
            'verification_issues_count': issues_count
        }

    # Replace the actual function with the mock for this example run
    fix_verification_errors = mock_fix_verification_errors

    # --- Run the Loop ---
    try:
        results = fix_verification_errors_loop(
            program_file=str(program_file),
            code_file=str(code_file),
            prompt=prompt_text,
            verification_program=str(verifier_file),
            strength=0.5,
            temperature=0.1,
            max_attempts=5,
            budget=0.10, # Set a budget
            verification_log_file=str(dummy_dir / "fix_loop_log.xml"),
            verbose=True
        )

        console.print("\n[bold magenta]--- Final Results ---[/bold magenta]")
        console.print(f"Success: {results['success']}")
        console.print(f"Total Attempts: {results['total_attempts']}")
        console.print(f"Total Cost: ${results['total_cost']:.6f}")
        console.print(f"Model Name: {results['model_name']}")

        console.print("\n[bold magenta]--- Final Code ---[/bold magenta]")
        console.print(Syntax(results['final_code'], "python", theme="default", line_numbers=True))

        console.print("\n[bold magenta]--- Statistics ---[/bold magenta]")
        console.print(results['statistics'])

    except Exception as e:
        console.print(f"\n[bold red]An error occurred during the example run: {e}[/bold red]")
        import traceback
        traceback.print_exc()
    finally:
        # Clean up dummy files
        # shutil.rmtree(dummy_dir)
        # console.print(f"\n[dim]Cleaned up dummy directory: {dummy_dir}[/dim]")
        # Restore original function if it was mocked
        if '_original_fix_verification_errors' in locals():
             fix_verification_errors = _original_fix_verification_errors
        pass # Keep files for inspection

