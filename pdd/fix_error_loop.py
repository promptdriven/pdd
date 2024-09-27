import os
import subprocess
import shutil
from typing import Tuple
from rich import print as rprint
from rich.console import Console
from rich.panel import Panel
from unittest.mock import MagicMock
from .fix_errors_from_unit_tests import fix_errors_from_unit_tests
import re

console = Console()


def parse_pytest_results(error_output):
    # Pattern to match different result types
    pattern = r"(\d+)\s+(failed|error|passed)"
    
    # Find all matches in the error_output
    matches = re.findall(pattern, error_output)
    
    total_fails = 0
    total_errors = 0
    
    for count, result_type in matches:
        count = int(count)
        if result_type == 'failed':
            total_fails += count
        elif result_type == 'error':
            total_errors += count
    
    return total_fails, total_errors

def fix_error_loop(
    unit_test_file: str,
    code_file: str,
    prompt: str,
    verification_program: str,
    strength: float,
    temperature: float,
    max_attempts: int,
    budget: float,
    error_log_file: str = "error_log.txt"
) -> Tuple[bool, str, str, int, float, str]:
    """
    Attempt to fix errors in a unit test and its corresponding code file through multiple iterations.

    Args:
        unit_test_file (str): Path to the unit test file.
        code_file (str): Path to the code file being tested.
        prompt (str): Prompt that generated the code under test.
        verification_program (str): Path to a Python program that verifies if the code still runs correctly.
        strength (float): Strength of the LLM model to use (0 to 1).
        temperature (float): Temperature parameter for the LLM model.
        max_attempts (int): Maximum number of fix attempts before giving up.
        budget (float): Maximum cost allowed for the fixing process.
        error_log_file (str, optional): Path to the error log file. Defaults to "error_log.txt".

    Returns:
        Tuple[bool, str, str, int, float, str]: 
            - success: Whether the errors were successfully fixed.
            - final_unit_test: Contents of the final unit test file.
            - final_code: Contents of the final code file.
            - total_attempts: Number of fix attempts made.
            - total_cost: Total cost of all fix attempts.
            - model_name: Name of the LLM model used.
    """
    try:
        # Check if all input files exist
        for file in [unit_test_file, code_file, verification_program]:
            if not os.path.exists(file):
                rprint(Panel(f"[red]Error: File not found: {file}[/red]"))
                return False, "", "", 0, 0.0, ""
            
        # Step 1: Remove existing error log file
        if os.path.exists(error_log_file):
            os.remove(error_log_file)

        # Step 2: Initialize variables
        attempts = 0
        total_cost = 0.0
        best_iteration = {"errors": float('inf'), "fails": float('inf'), "attempt": 0}
        model_name = ""
        final_result = None
        final_test_error = False

        # Step 3: Main loop
        while attempts < max_attempts and total_cost < budget:
            attempts += 1
            rprint(Panel(f"[blue]Attempt {attempts} of {max_attempts}[/blue]"))
            
            try:
                result = subprocess.run(
                    ["python", "-m", "pytest", "-vv", unit_test_file],
                    capture_output=True,
                    text=True
                )
                if isinstance(result, MagicMock):
                    stdout = result.stdout if hasattr(result, 'stdout') else ""
                    stderr = result.stderr if hasattr(result, 'stderr') else ""
                else:
                    stdout = result.stdout
                    stderr = result.stderr
                with open(error_log_file, "a") as log_file:
                    log_file.write(str(stdout))
                    log_file.write(str(stderr))
            except Exception as e:
                rprint(Panel(f"[yellow]Error running pytest: {str(e)}[/yellow]"))
                continue

            if isinstance(result, MagicMock):
                returncode = result.returncode if hasattr(result, 'returncode') else 1
            else:
                returncode = result.returncode

            if returncode == 0:
                rprint(Panel("[green]All tests passed![/green]"))
                break

            # Process test failures
            with open(error_log_file, "r") as log_file:
                error_output = log_file.read()

            escaped_error_output = error_output.replace('[', r'\[').replace(']', r'\]')
            rprint(Panel(f"[red]Test failures detected in attempt {attempts}:[/red]\n{escaped_error_output}"))

            fails, errors = parse_pytest_results(stdout)
            
            # Update best iteration based on new criteria
            if errors < best_iteration["errors"] or (errors == best_iteration["errors"] and fails < best_iteration["fails"]):
                best_iteration = {"errors": errors, "fails": fails, "attempt": attempts}
                rprint(Panel(f"[green]New best iteration: Attempt {attempts} with {errors} errors and {fails} fails[/green]"))

            # Create backup copies
            backup_unit_test = f"{unit_test_file[:-3]}_{fails}_{errors}_{attempts}.py"
            backup_code = f"{code_file[:-3]}_{fails}_{errors}_{attempts}.py"
            shutil.copy2(unit_test_file, backup_unit_test)
            shutil.copy2(code_file, backup_code)

            # Read file contents
            with open(unit_test_file, "r") as f:
                unit_test_content = f.read()
            with open(code_file, "r") as f:
                code_content = f.read()

            # Call fix_errors_from_unit_tests
            with console.capture() as capture:
                update_unit_test, update_code, fixed_unit_test, fixed_code, iteration_cost, model_name = fix_errors_from_unit_tests(
                    unit_test_content, code_content, prompt, error_output, error_log_file, strength, temperature
                )

            total_cost += iteration_cost
            rprint(Panel(f"[blue]Total cost so far: {total_cost}[/blue]"))

            if total_cost > budget:
                rprint(Panel("[yellow]Budget exceeded. Stopping iterations.[/yellow]"))
                break

            if not update_unit_test and not update_code:
                rprint(Panel("[yellow]No changes were needed. Stopping iterations.[/yellow]"))
                break

            if update_unit_test:
                with open(unit_test_file, "w") as f:
                    f.write(fixed_unit_test)

            if update_code:
                with open(code_file, "w") as f:
                    f.write(fixed_code)
                # Run verification program
                try:
                    verification_result = subprocess.run(["python", verification_program], capture_output=True, text=True)
                    if isinstance(verification_result, MagicMock):
                        verification_returncode = verification_result.returncode if hasattr(verification_result, 'returncode') else 1
                    else:
                        verification_returncode = verification_result.returncode
                    if verification_returncode != 0:
                        rprint(Panel("[red]Verification failed. Restoring original code.[/red]"))
                        shutil.copy2(backup_code, code_file)
                        # Don't break here, allow for more attempts
                    else:
                        rprint(Panel("[green]Verification successful.[/green]"))
                except Exception as e:
                    rprint(Panel(f"[yellow]Error during verification: {str(e)}[/yellow]"))
                    # Don't break here, allow for more attempts

        try:
             # Step 4: Final pytest run
            final_result = subprocess.run(
                ["python", "-m", "pytest", "-vv", unit_test_file],
                capture_output=True,
                text=True
            )
            if isinstance(final_result, MagicMock):
                final_stdout = final_result.stdout if hasattr(final_result, 'stdout') else ""
                final_stderr = final_result.stderr if hasattr(final_result, 'stderr') else ""
            else:
                final_stdout = final_result.stdout
                final_stderr = final_result.stderr
            with open(error_log_file, "a") as log_file:
                log_file.write(str(final_stdout))
                log_file.write(str(final_stderr))
            
            escaped_error_output = str(final_stdout).replace('[', r'\[').replace(']', r'\]')
            rprint(Panel(f"[bold]Final test results:[/bold]\n{escaped_error_output}"))
        except Exception as e:
            rprint(Panel(f"[yellow]Error during final test run: {str(e)}[/yellow]"))
            final_test_error = True
        # Step 5: Restore best iteration if necessary
        if final_result is None or \
           (isinstance(final_result, MagicMock) and final_result.returncode != 0) or \
           (isinstance(final_result, subprocess.CompletedProcess) and final_result.returncode != 0):
            best_unit_test = f"{unit_test_file[:-3]}_{best_iteration['fails']}_{best_iteration['errors']}_{best_iteration['attempt']}.py"
            best_code = f"{code_file[:-3]}_{best_iteration['fails']}_{best_iteration['errors']}_{best_iteration['attempt']}.py"
            shutil.copy2(best_unit_test, unit_test_file)
            shutil.copy2(best_code, code_file)
            rprint(Panel(f"[yellow]Restored best iteration (attempt {best_iteration['attempt']}) with {best_iteration['errors']} errors and {best_iteration['fails']} fails.[/yellow]"))
        # Step 6: Prepare return values
        success = (isinstance(final_result, MagicMock) and final_result.returncode == 0) or \
                  (isinstance(final_result, subprocess.CompletedProcess) and final_result.returncode == 0 and not final_test_error)
        with open(unit_test_file, "r") as f:
            final_unit_test = f.read()
        with open(code_file, "r") as f:
            final_code = f.read()

        return success, final_unit_test, final_code, attempts, total_cost, model_name

    except Exception as e:
        rprint(Panel(f"[red]An error occurred: {str(e)}[/red]"))
        return False, "", "", attempts, total_cost, model_name
