import os
import shutil
import subprocess
import datetime
import time
from pathlib import Path
from typing import Dict, Tuple, Any, Optional
from xml.sax.saxutils import escape

from rich.console import Console

# Use relative import assuming fix_verification_errors is in the same package
try:
    # Attempt relative import for package context
    from .fix_verification_errors import fix_verification_errors
except ImportError:
    # Fallback for direct script execution (e.g., testing)
    # This assumes 'pdd' package structure exists relative to the script
    try:
        from pdd.fix_verification_errors import fix_verification_errors
    except ImportError:
        raise ImportError(
            "Could not import 'fix_verification_errors'. "
            "Ensure it's available via relative import or in the 'pdd' package."
        )

# Initialize Rich Console for pretty printing
console = Console()

def _run_program(
    program_path: Path,
    args: Optional[list[str]] = None,
    timeout: int = 60
) -> Tuple[int, str]:
    """
    Runs a Python program using subprocess, capturing combined stdout and stderr.

    Args:
        program_path: Path to the Python program to run.
        args: Optional list of command-line arguments for the program.
        timeout: Timeout in seconds for the subprocess.

    Returns:
        A tuple containing the return code (int) and the combined output (str).
        Returns (-1, error_message) if the program is not found or other execution error occurs.
    """
    if not program_path.is_file():
        return -1, f"Error: Program file not found at {program_path}"

    command = ["python", str(program_path)]
    if args:
        command.extend(args)

    try:
        result = subprocess.run(
            command,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,  # Don't raise exception for non-zero exit codes
        )
        combined_output = result.stdout + result.stderr
        return result.returncode, combined_output
    except FileNotFoundError:
        return -1, f"Error: Python interpreter not found or '{program_path}' not found."
    except subprocess.TimeoutExpired:
        return -1, f"Error: Program execution timed out after {timeout} seconds."
    except Exception as e:
        return -1, f"Error: An unexpected error occurred while running the program: {e}"

def _write_log_entry(log_file_path: Path, xml_content: str):
    """Appends XML content to the log file."""
    try:
        with open(log_file_path, "a", encoding="utf-8") as f:
            f.write(xml_content + "\n")
    except IOError as e:
        console.print(f"[bold red]Error writing to log file {log_file_path}: {e}[/bold red]")

def fix_verification_errors_loop(
    program_file: str,
    code_file: str,
    prompt: str,
    verification_program: str,
    strength: float,
    temperature: float,
    max_attempts: int,
    budget: float,
    verification_log_file: str = "verification.log",
    output_code_path: Optional[str] = None,
    output_program_path: Optional[str] = None,
    verbose: bool = False,
    program_args: Optional[list[str]] = None,
) -> Dict[str, Any]:
    """
    Attempts to fix errors in a code file based on program execution output
    against the prompt's intent, iterating multiple times with secondary verification.

    Args:
        program_file: Path to the Python program exercising the code.
        code_file: Path to the code file being tested/verified.
        prompt: The prompt defining the intended behavior.
        verification_program: Path to a secondary program to verify code changes.
        strength: LLM model strength (0.0 to 1.0).
        temperature: LLM temperature (0.0 to 1.0).
        max_attempts: Maximum number of fix attempts.
        budget: Maximum allowed cost in USD.
        verification_log_file: Path for detailed XML logging (default: "verification.log").
        output_code_path: Optional path to save fixed code (default: None).
        output_program_path: Optional path to save fixed program (default: None).
        verbose: Enable verbose logging (default: False).
        program_args: Optional list of command-line arguments for the program_file.

    Returns:
        A dictionary containing:
            'success': bool - Whether the code was successfully fixed.
            'final_program': str - Contents of the final program file.
            'final_code': str - Contents of the final code file.
            'total_attempts': int - Number of fix attempts made (loop iterations started).
            'total_cost': float - Total cost of LLM calls.
            'model_name': str | None - Name of the LLM model used.
            'statistics': dict - Detailed statistics about the process.
    """
    program_path = Path(program_file).resolve()
    code_path = Path(code_file).resolve()
    verification_program_path = Path(verification_program).resolve()
    log_path = Path(verification_log_file).resolve()

    # --- Validate Inputs ---
    if not program_path.is_file():
        console.print(f"[bold red]Error: Program file not found: {program_path}[/bold red]")
        return {"success": False, "final_program": "", "final_code": "", "total_attempts": 0, "total_cost": 0.0, "model_name": None, "statistics": {}}
    if not code_path.is_file():
        console.print(f"[bold red]Error: Code file not found: {code_path}[/bold red]")
        return {"success": False, "final_program": "", "final_code": "", "total_attempts": 0, "total_cost": 0.0, "model_name": None, "statistics": {}}
    if not verification_program_path.is_file():
        console.print(f"[bold red]Error: Verification program not found: {verification_program_path}[/bold red]")
        return {"success": False, "final_program": "", "final_code": "", "total_attempts": 0, "total_cost": 0.0, "model_name": None, "statistics": {}}
    if not 0.0 <= strength <= 1.0:
        console.print(f"[bold red]Error: Strength must be between 0.0 and 1.0.[/bold red]")
        return {"success": False, "final_program": "", "final_code": "", "total_attempts": 0, "total_cost": 0.0, "model_name": None, "statistics": {}}
    if not 0.0 <= temperature <= 1.0:
         console.print(f"[bold red]Error: Temperature must be between 0.0 and 1.0.[/bold red]")
         return {"success": False, "final_program": "", "final_code": "", "total_attempts": 0, "total_cost": 0.0, "model_name": None, "statistics": {}}
    # Prompt requires positive max_attempts
    if max_attempts <= 0:
        console.print(f"[bold red]Error: Max attempts must be positive.[/bold red]")
        return {"success": False, "final_program": "", "final_code": "", "total_attempts": 0, "total_cost": 0.0, "model_name": None, "statistics": {}}
    if budget < 0:
        console.print(f"[bold red]Error: Budget cannot be negative.[/bold red]")
        return {"success": False, "final_program": "", "final_code": "", "total_attempts": 0, "total_cost": 0.0, "model_name": None, "statistics": {}}


    # Step 1: Remove existing verification log file
    try:
        if log_path.exists():
            os.remove(log_path)
            if verbose:
                console.print(f"Removed existing log file: {log_path}")
    except OSError as e:
        console.print(f"[bold red]Error removing log file {log_path}: {e}[/bold red]")
        # Continue execution, but logging might fail

    # Step 2: Initialize variables
    attempts = 0 # Counter for loop iterations started
    total_cost = 0.0
    model_name: Optional[str] = None
    overall_success = False
    best_iteration = {
        'attempt': -1, # 0 represents initial state
        'program_backup': None,
        'code_backup': None,
        'issues': float('inf')
    }
    stats = {
        'initial_issues': -1,
        'final_issues': -1,
        'best_iteration_num': -1,
        'best_iteration_issues': float('inf'),
        'improvement_issues': 0,
        'improvement_percent': 0.0,
        'status_message': 'Initialization',
    }
    initial_program_content = ""
    initial_code_content = ""
    program_contents = "" # Keep track of current contents
    code_contents = ""    # Keep track of current contents

    # --- Step 3: Determine Initial State ---
    if verbose:
        console.print("[bold cyan]Step 3: Determining Initial State...[/bold cyan]")

    try:
        initial_program_content = program_path.read_text(encoding="utf-8")
        initial_code_content = code_path.read_text(encoding="utf-8")
        program_contents = initial_program_content # Initialize current contents
        code_contents = initial_code_content       # Initialize current contents
    except IOError as e:
        console.print(f"[bold red]Error reading initial program/code files: {e}[/bold red]")
        stats['status_message'] = f'Error reading initial files: {e}' # Add status message
        return {"success": False, "final_program": "", "final_code": "", "total_attempts": 0, "total_cost": 0.0, "model_name": None, "statistics": stats}

    # 3a: Run initial program with args
    initial_return_code, initial_output = _run_program(program_path, args=program_args)
    if verbose:
        console.print(f"Initial program run exit code: {initial_return_code}")
        console.print(f"Initial program output:\n{initial_output}")

    # 3b: Log initial state
    timestamp = datetime.datetime.now().isoformat()
    initial_log_entry = f'<InitialState timestamp="{timestamp}">\n'
    initial_log_entry += f'  <ProgramFile>{escape(str(program_path))}</ProgramFile>\n'
    initial_log_entry += f'  <CodeFile>{escape(str(code_path))}</CodeFile>\n'
    initial_log_entry += f'  <ExitCode>{initial_return_code}</ExitCode>\n'
    initial_log_entry += f'  <Output>{escape(initial_output)}</Output>\n'
    initial_log_entry += '</InitialState>'
    _write_log_entry(log_path, initial_log_entry)

    # 3d: Call fix_verification_errors for initial assessment
    try:
        if verbose:
            console.print("Running initial assessment with fix_verification_errors...")
        # Use actual strength/temp for realistic initial assessment
        initial_fix_result = fix_verification_errors(
            program=initial_program_content,
            prompt=prompt,
            code=initial_code_content,
            output=initial_output,
            strength=strength,
            temperature=temperature,
            verbose=verbose
        )
        # 3e: Add cost
        initial_cost = initial_fix_result.get('total_cost', 0.0)
        total_cost += initial_cost
        model_name = initial_fix_result.get('model_name') # Capture model name early
        if verbose:
             console.print(f"Initial assessment cost: ${initial_cost:.6f}, Total cost: ${total_cost:.6f}")

        # 3f: Extract initial issues
        initial_issues_count = initial_fix_result.get('verification_issues_count', -1)
        stats['initial_issues'] = initial_issues_count
        if verbose:
            console.print(f"Initial verification issues found: {initial_issues_count}")
            if initial_fix_result.get('explanation'):
                 console.print("Initial assessment explanation:")
                 console.print(initial_fix_result['explanation'])

        # FIX: Add check for initial assessment error *before* checking success/budget
        # Check if the fixer function returned its specific error state (None explanation/model)
        if initial_fix_result.get('explanation') is None and initial_fix_result.get('model_name') is None:
             error_msg = "Error: Fixer returned invalid/error state during initial assessment"
             console.print(f"[bold red]{error_msg}. Aborting.[/bold red]")
             stats['status_message'] = error_msg
             stats['final_issues'] = -1 # Indicate unknown/error state
             # Write final action log for error on initial check
             final_log_entry = "<FinalActions>\n"
             final_log_entry += f'  <Error>{escape(error_msg)}</Error>\n'
             final_log_entry += "</FinalActions>"
             _write_log_entry(log_path, final_log_entry)
             # Return failure state
             return {
                 "success": False,
                 "final_program": initial_program_content,
                 "final_code": initial_code_content,
                 "total_attempts": 0,
                 "total_cost": total_cost, # May be non-zero if error occurred after some cost
                 "model_name": model_name, # May have been set before error
                 "statistics": stats,
             }

        # 3g: Initialize best iteration tracker
        # Store original paths as the 'backup' for iteration 0
        best_iteration = {
            'attempt': 0, # Use 0 for initial state
            'program_backup': str(program_path), # Path to original
            'code_backup': str(code_path),       # Path to original
            'issues': initial_issues_count if initial_issues_count != -1 else float('inf')
        }
        stats['best_iteration_num'] = 0
        stats['best_iteration_issues'] = best_iteration['issues']

        # 3h: Check for immediate success or budget exceeded
        if initial_issues_count == 0:
            console.print("[bold green]Initial check found 0 verification issues. No fixing loop needed.[/bold green]")
            overall_success = True
            stats['final_issues'] = 0
            stats['status_message'] = 'Success on initial check'
            stats['improvement_issues'] = 0
            stats['improvement_percent'] = 100.0 # Reached target of 0 issues

            # Write final action log for successful initial check
            final_log_entry = "<FinalActions>\n"
            final_log_entry += f'  <Action>Process finished successfully on initial check.</Action>\n'
            final_log_entry += "</FinalActions>"
            _write_log_entry(log_path, final_log_entry)

            # Step 7 (early exit): Print stats
            console.print("\n[bold]--- Final Statistics ---[/bold]")
            console.print(f"Initial Issues: {stats['initial_issues']}")
            console.print(f"Final Issues: {stats['final_issues']}")
            console.print(f"Best Iteration: {stats['best_iteration_num']} (Issues: {stats['best_iteration_issues']})")
            console.print(f"Improvement (Issues Reduced): {stats['improvement_issues']}")
            console.print(f"Improvement (Percent Towards 0 Issues): {stats['improvement_percent']:.2f}%")
            console.print(f"Overall Status: {stats['status_message']}")
            console.print(f"Total Attempts Made: {attempts}") # attempts is 0 here
            console.print(f"Total Cost: ${total_cost:.6f}")
            console.print(f"Model Used: {model_name or 'N/A'}")
            # Step 8 (early exit): Return
            return {
                "success": overall_success,
                "final_program": initial_program_content,
                "final_code": initial_code_content,
                "total_attempts": attempts, # attempts is 0
                "total_cost": total_cost,
                "model_name": model_name,
                "statistics": stats,
            }
        elif total_cost >= budget:
             console.print(f"[bold yellow]Budget ${budget:.4f} exceeded during initial assessment (Cost: ${total_cost:.4f}). Aborting.[/bold yellow]")
             stats['status_message'] = 'Budget exceeded on initial check'
             stats['final_issues'] = stats['initial_issues'] # Final issues same as initial

             # Write final action log for budget exceeded on initial check
             final_log_entry = "<FinalActions>\n"
             final_log_entry += f'  <Action>Budget exceeded on initial check.</Action>\n'
             final_log_entry += "</FinalActions>"
             _write_log_entry(log_path, final_log_entry)

             # No changes made, return initial state
             return {
                 "success": False,
                 "final_program": initial_program_content,
                 "final_code": initial_code_content,
                 "total_attempts": 0,
                 "total_cost": total_cost,
                 "model_name": model_name,
                 "statistics": stats,
             }

    except Exception as e:
        console.print(f"[bold red]Error during initial assessment with fix_verification_errors: {e}[/bold red]")
        stats['status_message'] = f'Error during initial assessment: {e}'
        # Cannot proceed without initial assessment
        return {"success": False, "final_program": initial_program_content, "final_code": initial_code_content, "total_attempts": 0, "total_cost": total_cost, "model_name": model_name, "statistics": stats}


    # --- Step 4: Enter the Fixing Loop ---
    if verbose:
        console.print("\n[bold cyan]Step 4: Starting Fixing Loop...[/bold cyan]")

    # Loop while attempts < max_attempts and budget not exceeded
    # Note: The loop condition checks attempts *before* incrementing for the current iteration
    while attempts < max_attempts:
        current_attempt = attempts + 1 # 1-based for reporting
        timestamp = datetime.datetime.now().isoformat()
        iteration_log_xml = f'<Iteration attempt="{current_attempt}" timestamp="{timestamp}">\n'

        # 4a: Print attempt number and increment counter for attempts *started*
        console.print(f"\n[bold]Attempt {current_attempt}/{max_attempts} (Cost: ${total_cost:.4f}/{budget:.4f})[/bold]")
        attempts += 1 # Increment attempts counter here for iterations started

        # Check budget *before* running expensive operations in the loop
        if total_cost >= budget:
            console.print(f"[bold yellow]Budget ${budget:.4f} already met or exceeded before starting attempt {current_attempt}. Stopping.[/bold yellow]")
            # No iteration log entry needed as the iteration didn't run
            stats['status_message'] = 'Budget Exceeded'
            attempts -= 1 # Decrement as this attempt didn't actually run
            break

        # 4b: Run the program file with args
        if verbose:
            console.print(f"Running program: {program_path} with args: {program_args}")
        return_code, program_output = _run_program(program_path, args=program_args)
        iteration_log_xml += f'  <ProgramExecution>\n'
        iteration_log_xml += f'    <ExitCode>{return_code}</ExitCode>\n'
        iteration_log_xml += f'    <OutputBeforeFix>{escape(program_output)}</OutputBeforeFix>\n'
        iteration_log_xml += f'  </ProgramExecution>\n'
        if verbose:
            console.print(f"Program exit code: {return_code}")
            # console.print(f"Program output:\n{program_output}") # Can be long

        # 4c: Read current contents (already stored in program_contents/code_contents)
        # Re-read could be added here if external modification is possible, but generally not needed
        # try:
        #     program_contents = program_path.read_text(encoding="utf-8")
        #     code_contents = code_path.read_text(encoding="utf-8")
        # except IOError as e: ...

        # 4d: Create backups
        program_backup_path = program_path.with_stem(f"{program_path.stem}_iteration_{current_attempt}").with_suffix(program_path.suffix)
        code_backup_path = code_path.with_stem(f"{code_path.stem}_iteration_{current_attempt}").with_suffix(code_path.suffix)
        try:
            # Copy from the *current* state before this iteration's fix
            program_path.write_text(program_contents, encoding="utf-8") # Ensure file matches memory state
            code_path.write_text(code_contents, encoding="utf-8")       # Ensure file matches memory state
            shutil.copy2(program_path, program_backup_path)
            shutil.copy2(code_path, code_backup_path)
            if verbose:
                console.print(f"Created backups: {program_backup_path}, {code_backup_path}")
            iteration_log_xml += f'  <Backups>\n'
            iteration_log_xml += f'    <Program>{escape(str(program_backup_path))}</Program>\n'
            iteration_log_xml += f'    <Code>{escape(str(code_backup_path))}</Code>\n'
            iteration_log_xml += f'  </Backups>\n'
        except OSError as e:
            console.print(f"[bold red]Error creating backup files during attempt {current_attempt}: {e}[/bold red]")
            iteration_log_xml += f'  <Status>Error Creating Backups</Status>\n</Iteration>'
            _write_log_entry(log_path, iteration_log_xml)
            stats['status_message'] = f'Error creating backups on attempt {current_attempt}'
            break # Don't proceed without backups

        # 4e: Call fix_verification_errors
        iteration_log_xml += f'  <InputsToFixer>\n'
        iteration_log_xml += f'    <Program>{escape(program_contents)}</Program>\n'
        iteration_log_xml += f'    <Code>{escape(code_contents)}</Code>\n'
        iteration_log_xml += f'    <Prompt>{escape(prompt)}</Prompt>\n'
        iteration_log_xml += f'    <ProgramOutput>{escape(program_output)}</ProgramOutput>\n'
        iteration_log_xml += f'  </InputsToFixer>\n'

        fix_result = {}
        try:
            if verbose:
                console.print("Calling fix_verification_errors...")
            fix_result = fix_verification_errors(
                program=program_contents,
                prompt=prompt,
                code=code_contents,
                output=program_output,
                strength=strength,
                temperature=temperature,
                verbose=verbose
            )

            # 4f: Add cost
            attempt_cost = fix_result.get('total_cost', 0.0)
            total_cost += attempt_cost
            model_name = fix_result.get('model_name', model_name) # Update if available
            current_issues_count = fix_result.get('verification_issues_count', -1)

            if verbose:
                console.print(f"Fixer cost: ${attempt_cost:.6f}, Total cost: ${total_cost:.6f}")
                console.print(f"Fixer issues found: {current_issues_count}")
                if fix_result.get('explanation'):
                    console.print("Fixer explanation:")
                    console.print(fix_result['explanation'])


            # 4g: Log fixer result
            iteration_log_xml += f'  <FixerResult '
            iteration_log_xml += f'total_cost="{attempt_cost:.6f}" '
            iteration_log_xml += f'model_name="{escape(model_name or "N/A")}" '
            iteration_log_xml += f'verification_issues_count="{current_issues_count}">\n'
            iteration_log_xml += f'    <Explanation>{escape(str(fix_result.get("explanation", "N/A")))}</Explanation>\n'
            iteration_log_xml += f'    <FixedProgram>{escape(fix_result.get("fixed_program", ""))}</FixedProgram>\n'
            iteration_log_xml += f'    <FixedCode>{escape(fix_result.get("fixed_code", ""))}</FixedCode>\n'
            iteration_log_xml += f'  </FixerResult>\n'

        except Exception as e:
            console.print(f"[bold red]Error calling fix_verification_errors on attempt {current_attempt}: {e}[/bold red]")
            iteration_log_xml += f'  <Status>Error in Fixer Call: {escape(str(e))}</Status>\n</Iteration>'
            _write_log_entry(log_path, iteration_log_xml)
            stats['status_message'] = f'Error in fixer call on attempt {current_attempt}'
            # Continue to next attempt if possible, don't break immediately
            continue

        # FIX: Add check for fixer returning error state (e.g., None explanation/model or specific issue count)
        # We use -1 as the signal for an internal error from fix_verification_errors
        if current_issues_count == -1:
            error_msg = "Error: Fixer returned invalid/error state"
            console.print(f"[bold red]{error_msg} on attempt {current_attempt}. Stopping.[/bold red]")
            iteration_log_xml += f'  <Status>{escape(error_msg)}</Status>\n</Iteration>'
            _write_log_entry(log_path, iteration_log_xml)
            stats['status_message'] = error_msg
            overall_success = False # Ensure success is false
            break # Exit loop due to fixer error

        # 4h: Check budget *after* fixer call cost is added
        if total_cost >= budget:
            console.print(f"[bold yellow]Budget ${budget:.4f} exceeded after attempt {current_attempt} (Cost: ${total_cost:.4f}). Stopping.[/bold yellow]")
            iteration_log_xml += f'  <Status>Budget Exceeded</Status>\n</Iteration>'
            _write_log_entry(log_path, iteration_log_xml)
            stats['status_message'] = 'Budget Exceeded'
            # Update best iteration if this costly attempt was still the best so far
            if current_issues_count != -1 and current_issues_count < best_iteration['issues']:
                 if verbose:
                     console.print(f"[green]New best iteration found (before budget break): Attempt {current_attempt} (Issues: {current_issues_count})[/green]")
                 best_iteration = {
                     'attempt': current_attempt,
                     'program_backup': str(program_backup_path),
                     'code_backup': str(code_backup_path),
                     'issues': current_issues_count
                 }
                 stats['best_iteration_num'] = current_attempt
                 stats['best_iteration_issues'] = current_issues_count
            break # Exit loop due to budget

        # FIX: Moved calculation of update flags earlier
        # 4j: Check if changes were suggested
        fixed_program = fix_result.get('fixed_program', program_contents)
        fixed_code = fix_result.get('fixed_code', code_contents)
        program_updated = fixed_program != program_contents
        code_updated = fixed_code != code_contents

        # 4k, 4l: Log fix attempt
        iteration_log_xml += f'  <FixAttempted program_updated="{program_updated}" code_updated="{code_updated}"/>\n'


        # FIX: Restructured logic for success check and secondary verification
        secondary_verification_passed = True # Assume pass unless changes made and verification fails
        changes_applied_this_iteration = False
        verify_ret_code = 0 # Default for skipped verification
        verify_output = "Secondary verification not run." # Default for skipped

        if code_updated:
            if verbose:
                console.print("Code change suggested, attempting secondary verification...")
            
            if verification_program is not None and verification_program_path.is_file():
                try:
                    # Temporarily write the proposed code change
                    code_path.write_text(fixed_code, encoding="utf-8")

                    # Run verification program
                    # Consider if verification_program_path needs arguments or specific env vars
                    # For now, assuming it can run directly or uses env vars set externally
                    current_verify_ret_code, current_verify_output = _run_program(verification_program_path)

                    # Determine pass/fail (simple: exit code 0 = pass)
                    secondary_verification_passed = (current_verify_ret_code == 0)
                    verify_ret_code = current_verify_ret_code
                    verify_output = current_verify_output

                    if verbose:
                        console.print(f"Secondary verification ran. Exit code: {verify_ret_code}")
                        console.print(f"Secondary verification passed: {secondary_verification_passed}")
                        # console.print(f"Secondary verification output:\\n{verify_output}")

                    if not secondary_verification_passed:
                        console.print("[yellow]Secondary verification failed. Restoring code file from memory.[/yellow]")
                        code_path.write_text(code_contents, encoding="utf-8") # Restore from memory state before this attempt
                
                except IOError as e:
                    console.print(f"[bold red]Error during secondary verification I/O: {e}[/bold red]")
                    verify_output = f"Error during secondary verification I/O: {str(e)}"
                    secondary_verification_passed = False # Treat I/O error as failure
                    verify_ret_code = -1 # Indicate error
                    try:
                        code_path.write_text(code_contents, encoding="utf-8")
                    except IOError:
                        console.print(f"[bold red]Failed to restore code file after I/O error.[/bold red]")
            else:
                # No valid verification program provided, or it's not a file
                secondary_verification_passed = True # Effectively skipped, so it doesn't block progress
                verify_ret_code = 0
                if verification_program is None:
                    verify_output = "Secondary verification skipped: No verification program provided."
                else:
                    verify_output = f"Secondary verification skipped: Verification program '{verification_program}' not found or is not a file at '{verification_program_path}'."
                if verbose:
                    console.print(f"[dim]{verify_output}[/dim]")
        else:
            # Code was not updated by the fixer, so secondary verification is not strictly needed
            secondary_verification_passed = True # No changes to verify
            verify_ret_code = 0
            verify_output = "Secondary verification not needed: Code was not modified by the fixer."
            if verbose:
                console.print(f"[dim]{verify_output}[/dim]")

        # Always log the SecondaryVerification block
        passed_str = str(secondary_verification_passed).lower()
        iteration_log_xml += f'  <SecondaryVerification passed="{passed_str}">\n'
        iteration_log_xml += f'    <ExitCode>{verify_ret_code}</ExitCode>\n'
        iteration_log_xml += f'    <Output>{escape(verify_output)}</Output>\n'
        iteration_log_xml += f'  </SecondaryVerification>\n'

        # Now, decide outcome based on issue count and verification status
        if secondary_verification_passed:
            # Update best iteration if current attempt is better
            if current_issues_count != -1 and current_issues_count < best_iteration['issues']:
                 if verbose:
                     console.print(f"[green]New best iteration found: Attempt {current_attempt} (Issues: {current_issues_count})[/green]")
                 best_iteration = {
                     'attempt': current_attempt,
                     'program_backup': str(program_backup_path),
                     'code_backup': str(code_backup_path),
                     'issues': current_issues_count
                 }
                 stats['best_iteration_num'] = current_attempt
                 stats['best_iteration_issues'] = current_issues_count

            # Apply changes (code was potentially already written for verification)
            try:
                if program_updated:
                    if verbose: console.print("Applying program changes...")
                    program_path.write_text(fixed_program, encoding="utf-8")
                    program_contents = fixed_program # Update memory state
                    iteration_log_xml += f'  <Action>Applied program changes.</Action>\n'
                    changes_applied_this_iteration = True
                if code_updated:
                     # Code already written if verification ran; update memory state
                     code_contents = fixed_code
                     iteration_log_xml += f'  <Action>Kept modified code (passed secondary verification).</Action>\n'
                     changes_applied_this_iteration = True

                if changes_applied_this_iteration:
                     # FIX: Revert status to match original tests where applicable
                     iteration_log_xml += f'  <Status>Changes Applied (Secondary Verification Passed or Not Needed)</Status>\n'
                else:
                     # This case happens if verification passed but neither program nor code changed
                     iteration_log_xml += f'  <Status>No Effective Changes Suggested (Identical Code)</Status>\n'

                # Check for SUCCESS condition HERE
                if current_issues_count == 0:
                    console.print(f"[bold green]Success! 0 verification issues found after attempt {current_attempt} and secondary verification passed.[/bold green]")
                    overall_success = True
                    stats['final_issues'] = 0
                    stats['status_message'] = f'Success on attempt {current_attempt}'
                    iteration_log_xml += '</Iteration>'
                    _write_log_entry(log_path, iteration_log_xml)
                    break # Exit loop on verified success

            except IOError as e:
                 console.print(f"[bold red]Error writing applied changes: {e}[/bold red]")
                 iteration_log_xml += f'  <Action>Error writing applied changes: {escape(str(e))}</Action>\n'
                 iteration_log_xml += f'  <Status>Error Applying Changes</Status>\n'
                 # Continue loop if possible

        else: # Secondary verification failed
            iteration_log_xml += f'  <Action>Changes Discarded Due To Secondary Verification Failure</Action>\n'
            iteration_log_xml += f'  <Status>Changes Discarded</Status>\n'
            # Memory state (program_contents, code_contents) remains unchanged from start of iteration

        # Check if loop should terminate due to no changes suggested when issues > 0
        # FIX: Adjust condition - break if secondary verification PASSED but resulted in NO effective changes
        # AND issues still remain. This avoids breaking early if verification FAILED (handled above).
        if secondary_verification_passed and not changes_applied_this_iteration and current_issues_count > 0:
            # FIX: Adjust status message for clarity
            console.print(f"[yellow]No effective changes suggested by the fixer on attempt {current_attempt} despite issues remaining ({current_issues_count}). Stopping.[/yellow]")
            iteration_log_xml += f'  <Status>No Effective Changes Suggested (Identical Code)</Status>\n' # Reuse status
            # FIX: Ensure status message matches test expectation when breaking here
            stats['status_message'] = f'No effective changes suggested on attempt {current_attempt}'
            # Update best iteration if this attempt was still the best so far
            if current_issues_count != -1 and current_issues_count < best_iteration['issues']:
                 if verbose:
                     console.print(f"[green]New best iteration found (despite no effective changes): Attempt {current_attempt} (Issues: {current_issues_count})[/green]")
                 best_iteration = {
                     'attempt': current_attempt,
                     'program_backup': str(program_backup_path),
                     'code_backup': str(code_backup_path),
                     'issues': current_issues_count
                 }
                 stats['best_iteration_num'] = current_attempt
                 stats['best_iteration_issues'] = current_issues_count

            overall_success = False # Ensure success is False
            iteration_log_xml += '</Iteration>'
            _write_log_entry(log_path, iteration_log_xml)
            break # Exit loop


        # Append iteration log (if not already done on success break or no-change break)
        iteration_log_xml += '</Iteration>'
        _write_log_entry(log_path, iteration_log_xml)

        # Small delay to avoid hitting rate limits if applicable
        time.sleep(0.5)

    # --- End of Loop ---

    # --- Step 5: Determine Final State ---
    if verbose:
        console.print("\n[bold cyan]Step 5: Determining Final State...[/bold cyan]")

    final_log_entry = "<FinalActions>\n"

    if not overall_success:
        # Determine reason for loop exit if not already set by break conditions
        # FIX: Ensure status message isn't overwritten if already set by break condition
        exit_reason_determined = stats['status_message'] not in ['Initialization', '']
        if not exit_reason_determined:
            if attempts == max_attempts:
                console.print(f"[bold yellow]Maximum attempts ({max_attempts}) reached.[/bold yellow]")
                stats['status_message'] = f'Max attempts ({max_attempts}) reached'
                final_log_entry += f'  <Action>Max attempts ({max_attempts}) reached.</Action>\n'
            else:
                # Loop likely exited due to an unexpected break or condition not setting status
                stats['status_message'] = 'Loop finished without success for unknown reason'
                final_log_entry += f'  <Action>Loop finished without reaching success state ({escape(stats["status_message"])}).</Action>\n'
        elif stats['status_message'] == 'Budget Exceeded':
             final_log_entry += f'  <Action>Loop stopped due to budget.</Action>\n'
        elif stats['status_message'].startswith('No changes suggested') or stats['status_message'].startswith('No effective changes'):
             final_log_entry += f'  <Action>Loop stopped as no changes were suggested.</Action>\n'
        elif stats['status_message'].startswith('Error'):
             final_log_entry += f'  <Action>Loop stopped due to error: {escape(stats["status_message"])}</Action>\n'
        # else: status already set by a break condition inside loop


        # 5b: Restore best iteration if one exists and is better than initial
        # Check if best_iteration recorded is actually better than initial state
        # And ensure it's not the initial state itself (attempt > 0)
        initial_issues_val = stats['initial_issues'] if stats['initial_issues'] != -1 else float('inf')
        if best_iteration['attempt'] > 0 and best_iteration['issues'] < initial_issues_val:
            console.print(f"[yellow]Restoring state from best iteration: Attempt {best_iteration['attempt']} (Issues: {best_iteration['issues']})[/yellow]")
            final_log_entry += f'  <Action>Restored Best Iteration {best_iteration["attempt"]} (Issues: {best_iteration["issues"]})</Action>\n'
            stats['status_message'] += f' - Restored best iteration {best_iteration["attempt"]}'
            try:
                best_program_path = Path(best_iteration['program_backup'])
                best_code_path = Path(best_iteration['code_backup'])
                if best_program_path.is_file() and best_code_path.is_file():
                    # Read content from backup before copying to handle potential race conditions if needed
                    restored_program_content = best_program_path.read_text(encoding='utf-8')
                    restored_code_content = best_code_path.read_text(encoding='utf-8')
                    program_path.write_text(restored_program_content, encoding='utf-8')
                    code_path.write_text(restored_code_content, encoding='utf-8')
                    program_contents = restored_program_content # Update memory state
                    code_contents = restored_code_content       # Update memory state
                    if verbose:
                        console.print(f"Restored {program_path} from {best_program_path}")
                        console.print(f"Restored {code_path} from {best_code_path}")
                    # Final issues count is the best achieved count
                    stats['final_issues'] = best_iteration['issues']
                else:
                    console.print(f"[bold red]Error: Backup files for best iteration {best_iteration['attempt']} not found! Cannot restore.[/bold red]")
                    final_log_entry += f'  <Error>Backup files for best iteration {best_iteration["attempt"]} not found.</Error>\n'
                    stats['status_message'] += ' - Error restoring best iteration (files missing)'
                    # Keep the last state, final issues remain unknown or last attempted
                    stats['final_issues'] = -1 # Indicate uncertainty

            except (OSError, IOError) as e:
                console.print(f"[bold red]Error restoring files from best iteration {best_iteration['attempt']}: {e}[/bold red]")
                final_log_entry += f'  <Error>Error restoring files from best iteration {best_iteration["attempt"]}: {escape(str(e))}</Error>\n'
                stats['status_message'] += f' - Error restoring best iteration: {e}'
                stats['final_issues'] = -1 # Indicate uncertainty

        # If no improvement was made or recorded (best is still initial state or worse)
        elif best_iteration['attempt'] <= 0 or best_iteration['issues'] >= initial_issues_val:
             console.print("[yellow]No improvement recorded over the initial state. Restoring original files.[/yellow]")
             final_log_entry += f'  <Action>No improvement found or recorded; restoring original state.</Action>\n'
             stats['final_issues'] = stats['initial_issues'] # Final issues are same as initial
             # Add restoration info to status message if not already implied
             if 'keeping original state' not in stats['status_message']:
                 stats['status_message'] += ' - keeping original state'
             # Ensure original files are restored if they were modified in a failed attempt
             try:
                 # Only write if current memory state differs from initial
                 if program_contents != initial_program_content:
                     program_path.write_text(initial_program_content, encoding='utf-8')
                     program_contents = initial_program_content
                 if code_contents != initial_code_content:
                     code_path.write_text(initial_code_content, encoding='utf-8')
                     code_contents = initial_code_content
             except IOError as e:
                 console.print(f"[bold red]Error restoring initial files: {e}[/bold red]")
                 final_log_entry += f'  <Error>Error restoring initial files: {escape(str(e))}</Error>\n'
                 stats['status_message'] += f' - Error restoring initial files: {e}'
                 stats['final_issues'] = -1 # State uncertain
        # Set final issues if not set by restoration logic (e.g., error during restore)
        if stats['final_issues'] == -1 and stats['initial_issues'] != -1:
            stats['final_issues'] = stats['initial_issues'] # Default to initial if unsure


    else: # overall_success is True
        final_log_entry += f'  <Action>Process finished successfully.</Action>\n'
        stats['final_issues'] = 0 # Success means 0 issues

    final_log_entry += "</FinalActions>"
    _write_log_entry(log_path, final_log_entry)

    # --- Step 6: Read Final Contents ---
    # Use the in-memory contents which should reflect the final state after potential restoration
    if verbose:
        console.print("\n[bold cyan]Step 6: Using Final In-Memory File Contents...[/bold cyan]")
    final_program_content = program_contents
    final_code_content = code_contents
    # Optionally re-read from disk for verification, but memory should be source of truth
    # try:
    #     final_program_content_disk = program_path.read_text(encoding="utf-8")
    #     final_code_content_disk = code_path.read_text(encoding="utf-8")
    #     if final_program_content != final_program_content_disk or final_code_content != final_code_content_disk:
    #          console.print("[bold red]Warning: Final file content on disk differs from expected state![/bold red]")
    #          # Decide whether to trust disk or memory
    # except IOError as e:
    #     console.print(f"[bold red]Error reading final program/code files for verification: {e}[/bold red]")
    #     stats['status_message'] += ' - Error reading final files for verification'


    # --- Step 7: Calculate and Print Summary Statistics ---
    if verbose:
        console.print("\n[bold cyan]Step 7: Calculating Final Statistics...[/bold cyan]")

    initial_known = stats['initial_issues'] != -1
    final_known = stats['final_issues'] != -1

    if initial_known and final_known:
        if stats['initial_issues'] > 0:
            if stats['final_issues'] == 0: # Successful fix
                stats['improvement_issues'] = stats['initial_issues']
                stats['improvement_percent'] = 100.0
            elif stats['final_issues'] < stats['initial_issues']: # Partial improvement
                stats['improvement_issues'] = stats['initial_issues'] - stats['final_issues']
                # % improvement towards reaching 0
                stats['improvement_percent'] = (stats['improvement_issues'] / stats['initial_issues']) * 100.0
            else: # No improvement or regression
                stats['improvement_issues'] = 0 # Can be negative if regression occurred
                stats['improvement_percent'] = 0.0 # Or negative? Let's cap at 0.
                if stats['final_issues'] > stats['initial_issues']:
                     stats['improvement_issues'] = stats['initial_issues'] - stats['final_issues'] # Negative value
                     # Percentage calculation might be misleading here, stick to 0% improvement towards goal.
        elif stats['initial_issues'] == 0: # Started perfect
             stats['improvement_issues'] = 0
             stats['improvement_percent'] = 100.0 # Already at target
             if stats['final_issues'] > 0: # Regression occurred during loop?
                 stats['improvement_issues'] = -stats['final_issues']
                 stats['improvement_percent'] = 0.0 # No longer at target
                 overall_success = False # Ensure success is false if regression happened after initial success
                 if 'Success on initial check' in stats['status_message']: # Update status if loop ran after initial success
                     stats['status_message'] = f'Regression occurred after initial success - Final Issues: {stats["final_issues"]}'
        # else: initial_issues < 0 (should not happen if known)
        #      stats['improvement_issues'] = 'N/A'
        #      stats['improvement_percent'] = 'N/A'
    else: # Initial or final state unknown
         stats['improvement_issues'] = 'N/A'
         stats['improvement_percent'] = 'N/A'
         if final_known and stats['final_issues'] == 0:
             overall_success = True # Assume success if final is 0, even if initial unknown
         else:
             overall_success = False # Cannot guarantee success if initial/final unknown


    console.print("\n[bold]--- Final Statistics ---[/bold]")
    console.print(f"Initial Issues: {stats['initial_issues'] if initial_known else 'Unknown'}")
    console.print(f"Final Issues: {stats['final_issues'] if final_known else 'Unknown'}")
    best_iter_num_str = stats['best_iteration_num'] if stats['best_iteration_num'] != -1 else 'N/A'
    best_iter_iss_str = stats['best_iteration_issues'] if stats['best_iteration_issues'] != float('inf') else 'N/A'
    console.print(f"Best Iteration Found: {best_iter_num_str} (Issues: {best_iter_iss_str})")
    console.print(f"Improvement (Issues Reduced): {stats['improvement_issues']}")
    improvement_percent_str = f"{stats['improvement_percent']:.2f}%" if isinstance(stats['improvement_percent'], float) else stats['improvement_percent']
    console.print(f"Improvement (Percent Towards 0 Issues): {improvement_percent_str}")
    console.print(f"Overall Status: {stats['status_message']}")
    console.print(f"Total Attempts Made: {attempts}") # Now reflects loop iterations started
    console.print(f"Total Cost: ${total_cost:.6f}")
    console.print(f"Model Used: {model_name or 'N/A'}")

    # --- Step 8: Return Results ---
    # Ensure final success status matches reality (e.g., if regression occurred)
    if final_known and stats['final_issues'] != 0:
        overall_success = False

    return {
        "success": overall_success,
        "final_program": final_program_content,
        "final_code": final_code_content,
        "total_attempts": attempts, # Return the number of loop iterations started
        "total_cost": total_cost,
        "model_name": model_name,
        "statistics": stats,
    }

# Example usage (requires setting up dummy files and potentially mocking fix_verification_errors)
if __name__ == "__main__":
    # Create dummy files for demonstration
    # In a real scenario, these files would exist and contain actual code/programs.
    console.print("[yellow]Setting up dummy files for demonstration...[/yellow]")
    temp_dir = Path("./temp_fix_verification_loop")
    temp_dir.mkdir(exist_ok=True)

    program_file = temp_dir / "my_program.py"
    code_file = temp_dir / "my_code_module.py"
    verification_program_file = temp_dir / "verify_syntax.py"

    program_file.write_text("""
import my_code_module
import sys
# Simulate using the module and checking output
val = int(sys.argv[1]) if len(sys.argv) > 1 else 5
result = my_code_module.process(val)
expected = val * 2
print(f"Input: {val}")
print(f"Result: {result}")
print(f"Expected: {expected}")
if result == expected:
    print("VERIFICATION_SUCCESS")
else:
    print(f"VERIFICATION_FAILURE: Expected {expected}, got {result}")
""", encoding="utf-8")

    # Initial code with a bug
    code_file.write_text("""
# my_code_module.py
def process(x):
    # Bug: should be x * 2
    return x + 2
""", encoding="utf-8")

    # Simple verification program (e.g., syntax check)
    verification_program_file.write_text("""
import sys
import py_compile
import os
# Check syntax of the code file (passed as argument, but we'll hardcode for simplicity here)
code_to_check = os.environ.get("CODE_FILE_TO_CHECK", "temp_fix_verification_loop/my_code_module.py")
print(f"Checking syntax of: {code_to_check}")
try:
    py_compile.compile(code_to_check, doraise=True)
    print("Syntax OK.")
    sys.exit(0) # Success
except py_compile.PyCompileError as e:
    print(f"Syntax Error: {e}")
    sys.exit(1) # Failure
except Exception as e:
    print(f"Verification Error: {e}")
    sys.exit(1) # Failure
""", encoding="utf-8")
    # Set environment variable for the verification script
    os.environ["CODE_FILE_TO_CHECK"] = str(code_file.resolve())


    # --- Mock fix_verification_errors ---
    # This is crucial for testing without actual LLM calls / costs
    # In a real test suite, use unittest.mock
    _original_fix_verification_errors = fix_verification_errors
    _call_count = 0

    def mock_fix_verification_errors(program, prompt, code, output, strength, temperature, verbose):
        global _call_count
        _call_count += 1
        cost = 0.001 * _call_count # Simulate increasing cost
        model = "mock_model_v1"
        explanation = ["Detected deviation: Output shows 'Result: 7', 'Expected: 10'.", "Issue seems to be in the `process` function calculation."]
        issues_count = 1 # Assume 1 issue initially

        fixed_program = program # Assume program doesn't need fixing
        fixed_code = code

        # Simulate fixing the code on the first *real* attempt (call_count == 2, as first is initial)
        if "VERIFICATION_FAILURE" in output and _call_count >= 2:
             explanation = ["Identified incorrect addition `x + 2`.", "Corrected to multiplication `x * 2` based on prompt intent and output mismatch."]
             fixed_code = """
# my_code_module.py
def process(x):
    # Fixed: should be x * 2
    return x * 2
"""
             issues_count = 0 # Fixed!
        elif "VERIFICATION_SUCCESS" in output:
             explanation = ["Output indicates VERIFICATION_SUCCESS."]
             issues_count = 0 # Already correct

        return {
            'explanation': explanation,
            'fixed_program': fixed_program,
            'fixed_code': fixed_code,
            'total_cost': cost,
            'model_name': model,
            'verification_issues_count': issues_count,
        }

    # Replace the real function with the mock
    # In package context, you might need to patch differently
    # For this script execution:
    # Note: This direct replacement might not work if the function is imported
    # using `from .fix_verification_errors import fix_verification_errors`.
    # A proper mock framework (`unittest.mock.patch`) is better.
    # Let's assume for this example run, we can modify the global scope *before* the loop calls it.
    # This is fragile. A better approach involves dependency injection or mocking frameworks.
    # HACK: Re-assigning the imported name in the global scope of this script
    globals()['fix_verification_errors'] = mock_fix_verification_errors


    console.print("\n[bold blue]--- Running fix_verification_errors_loop (with mock) ---[/bold blue]")

    # Example program_args: Pass input value 10 and another arg 5
    # Note: The example program only uses the first arg sys.argv[1]
    example_args = ["10", "another_arg"]

    results = fix_verification_errors_loop(
        program_file=str(program_file),
        code_file=str(code_file),
        prompt="Create a module 'my_code_module.py' with a function 'process(x)' that returns the input multiplied by 2.",
        verification_program=str(verification_program_file),
        strength=0.5,
        temperature=0.1,
        max_attempts=3,
        budget=0.10, # Set a budget
        verification_log_file=str(temp_dir / "test_verification.log"),
        verbose=True,
        program_args=example_args
    )

    console.print("\n[bold blue]--- Loop Finished ---[/bold blue]")
    console.print(f"Success: {results['success']}")
    console.print(f"Total Attempts: {results['total_attempts']}")
    console.print(f"Total Cost: ${results['total_cost']:.6f}")
    console.print(f"Model Name: {results['model_name']}")
    # console.print(f"Final Program:\n{results['final_program']}") # Can be long
    console.print(f"Final Code:\n{results['final_code']}")
    console.print(f"Statistics:\n{results['statistics']}")

    # Restore original function if needed elsewhere
    globals()['fix_verification_errors'] = _original_fix_verification_errors

    # Clean up dummy files
    # console.print("\n[yellow]Cleaning up dummy files...[/yellow]")
    # shutil.rmtree(temp_dir)
    console.print(f"\n[yellow]Dummy files and logs are in: {temp_dir}[/yellow]")
    console.print("[yellow]Please review the log file 'test_verification.log' inside that directory.[/yellow]")