#!/usr/bin/env python3
import os
import sys
import subprocess
import shutil
from datetime import datetime
import json

# Added for the new pytest-based reporting:
# import pytest
# import io

from rich import print as rprint
from rich.console import Console

# Relative import from an internal module.
from .fix_errors_from_unit_tests import fix_errors_from_unit_tests

console = Console()

def escape_brackets(text: str) -> str:
    """Escape square brackets so Rich doesn't misinterpret them."""
    return text.replace("[", "\\[").replace("]", "\\]")

def run_pytest_on_file(test_file: str) -> (int, int, int, str):
    """
    Run pytest on the specified test file using subprocess.
    Returns a tuple: (failures, errors, warnings, logs)
    """
    try:
        # Include "--json-only" to ensure only valid JSON is printed.
        cmd = [sys.executable, "-m", "pdd.pytest_output", "--json-only", test_file]
        result = subprocess.run(cmd, capture_output=True, text=True)
        
        # Parse the JSON output from stdout
        try:
            output = json.loads(result.stdout)
            test_results = output.get('test_results', [{}])[0]
            
            # Check pytest's return code first
            return_code = test_results.get('return_code', 1)
            if return_code != 0:
                return 1, 1, 0, f"Pytest failed with return code {return_code}\n{result.stdout}\n{result.stderr}"
            
            failures = test_results.get('failures', 0)
            errors = test_results.get('errors', 0)
            warnings = test_results.get('warnings', 0)
            
            # Combine stdout and stderr from the test results
            logs = test_results.get('standard_output', '') + '\n' + test_results.get('standard_error', '')
            
            return failures, errors, warnings, logs
            
        except json.JSONDecodeError:
            # If JSON parsing fails, return the raw output
            return 1, 1, 0, f"Failed to parse pytest output:\n{result.stdout}\n{result.stderr}"
            
    except Exception as e:
        return 1, 1, 0, f"Error running pytest: {str(e)}"

def fix_error_loop(unit_test_file: str,
                   code_file: str,
                   prompt: str,
                   verification_program: str,
                   strength: float,
                   temperature: float,
                   max_attempts: int,
                   budget: float,
                   error_log_file: str = "error_log.txt",
                   verbose: bool = False):
    """
    Attempt to fix errors in a unit test and corresponding code using repeated iterations, 
    counting only the number of times we actually call the LLM fix function. 
    The tests are re-run in the same iteration after a fix to see if we've succeeded,
    so that 'attempts' matches the number of fix attempts (not the total test runs).

    This updated version uses pytest's API directly to retrieve failures, errors, and warnings.

    Inputs:
        unit_test_file: Path to the file containing unit tests.
        code_file: Path to the file containing the code under test.
        prompt: Prompt that generated the code under test.
        verification_program: Path to a Python program that verifies the code still works.
        strength: float [0,1] representing LLM fix strength.
        temperature: float [0,1] representing LLM temperature.
        max_attempts: Maximum number of fix attempts.
        budget: Maximum cost allowed for the fixing process.
        error_log_file: Path to file to log errors (default: "error_log.txt").
        verbose: Enable verbose logging (default: False).

    Outputs:
        success: Boolean indicating if the overall process succeeded.
        final_unit_test: String contents of the final unit test file.
        final_code: String contents of the final code file.
        total_attempts: Number of fix attempts actually made.
        total_cost: Total cost accumulated.
        model_name: Name of the LLM model used.
    """
    # Check if unit_test_file and code_file exist.
    if not os.path.isfile(unit_test_file):
        rprint(f"[red]Error:[/red] Unit test file '{unit_test_file}' does not exist.")
        return False, "", "", 0, 0.0, ""
    if not os.path.isfile(code_file):
        rprint(f"[red]Error:[/red] Code file '{code_file}' does not exist.")
        return False, "", "", 0, 0.0, ""
    if verbose:
        rprint("[cyan]Starting fix error loop process.[/cyan]")

    # Remove existing error log file if it exists.
    if os.path.exists(error_log_file):
        try:
            os.remove(error_log_file)
            if verbose:
                rprint(f"[green]Removed old error log file:[/green] {error_log_file}")
        except Exception as e:
            rprint(f"[red]Error:[/red] Could not remove error log file: {e}")
            return False, "", "", 0, 0.0, ""

    # We use fix_attempts to track how many times we actually call the LLM:
    fix_attempts = 0
    total_cost = 0.0
    model_name = ""
    best_iteration_info = {
        "attempt": None,
        "fails": sys.maxsize,
        "errors": sys.maxsize,
        "warnings": sys.maxsize,
        "unit_test_backup": None,
        "code_backup": None
    }

    # For differentiating backup filenames:
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    # We do up to max_attempts fix attempts or until budget is exceeded
    iteration = 0
    while fix_attempts < max_attempts and total_cost < budget:
        iteration += 1
        iteration_header = f"=== Attempt iteration {iteration} ==="
        rprint(f"[bold blue]{iteration_header}[/bold blue]")
        with open(error_log_file, "a") as elog:
            elog.write(f"\n{iteration_header}\n")

        # 1) Run the unit tests using pytest's API directly.
        try:
            fails, errors, warnings, pytest_output = run_pytest_on_file(unit_test_file)
        except Exception as e:
            rprint(f"[red]Error running pytest:[/red] {e}")
            return False, "", "", fix_attempts, total_cost, model_name

        # Append to error log:
        with open(error_log_file, "a") as elog:
            elog.write(pytest_output + "\n")

        # Print to console (escaped):
        rprint(f"[magenta]Pytest output:[/magenta]\n{escape_brackets(pytest_output)}")
        if verbose:
            rprint(f"[cyan]Iteration summary: {fails} failed, {errors} errors, {warnings} warnings[/cyan]")

        # If tests are fully successful, we break out:
        if fails == 0 and errors == 0 and warnings == 0:
            rprint("[green]All tests passed with no warnings! Exiting loop.[/green]")
            break

        # We only attempt to fix if test is failing or has warnings:
        # Let's create backups:
        unit_test_dir, unit_test_name = os.path.split(unit_test_file)
        code_dir, code_name = os.path.split(code_file)
        unit_test_backup = os.path.join(
            unit_test_dir,
            f"{os.path.splitext(unit_test_name)[0]}_{iteration}_{errors}_{fails}_{warnings}_{timestamp}.py"
        )
        code_backup = os.path.join(
            code_dir,
            f"{os.path.splitext(code_name)[0]}_{iteration}_{errors}_{fails}_{warnings}_{timestamp}.py"
        )
        try:
            shutil.copy(unit_test_file, unit_test_backup)
            shutil.copy(code_file, code_backup)
            if verbose:
                rprint(f"[green]Created backup for unit test:[/green] {unit_test_backup}")
                rprint(f"[green]Created backup for code file:[/green] {code_backup}")
        except Exception as e:
            rprint(f"[red]Error creating backup files:[/red] {e}")
            return False, "", "", fix_attempts, total_cost, model_name

        # Update best iteration if needed:
        if (errors < best_iteration_info["errors"] or
            (errors == best_iteration_info["errors"] and fails < best_iteration_info["fails"]) or
            (errors == best_iteration_info["errors"] and fails == best_iteration_info["fails"] and warnings < best_iteration_info["warnings"])):
            best_iteration_info = {
                "attempt": iteration,
                "fails": fails,
                "errors": errors,
                "warnings": warnings,
                "unit_test_backup": unit_test_backup,
                "code_backup": code_backup
            }

        # Read file contents:
        try:
            with open(unit_test_file, "r") as f:
                unit_test_contents = f.read()
            with open(code_file, "r") as f:
                code_contents = f.read()
        except Exception as e:
            rprint(f"[red]Error reading input files:[/red] {e}")
            return False, "", "", fix_attempts, total_cost, model_name

        # Call fix:
        try:
            # Read error log file into pytest_output so it has history of all previous attempts:
            with open(error_log_file, "r") as f:
                pytest_output = f.read()

            updated_unit_test, updated_code, fixed_unit_test, fixed_code, cost, model_name = fix_errors_from_unit_tests(
                unit_test_contents,
                code_contents,
                prompt,
                pytest_output,
                error_log_file,
                strength,
                temperature,
                verbose=verbose
            )
        except Exception as e:
            rprint(f"[red]Error during fix_errors_from_unit_tests call:[/red] {e}")
            break

        fix_attempts += 1  # We used one fix attempt
        total_cost += cost
        if verbose:
            rprint(f"[cyan]Iteration fix cost: ${cost:.6f}, Total cost: ${total_cost:.6f}[/cyan]")
        if total_cost > budget:
            rprint(f"[red]Exceeded the budget of ${budget:.6f}. Ending fixing loop.[/red]")
            break

        # Update unit test file if needed.
        if updated_unit_test:
            try:
                with open(unit_test_file, "w") as f:
                    f.write(fixed_unit_test)
                if verbose:
                    rprint("[green]Unit test file updated.[/green]")
            except Exception as e:
                rprint(f"[red]Error writing updated unit test:[/red] {e}")
                break

        # Update code file and run verification if needed.
        if updated_code:
            try:
                with open(code_file, "w") as f:
                    f.write(fixed_code)
                if verbose:
                    rprint("[green]Code file updated.[/green]")
            except Exception as e:
                rprint(f"[red]Error writing updated code file:[/red] {e}")
                break

            # Run the verification:
            try:
                verify_cmd = [sys.executable, verification_program]
                verify_result = subprocess.run(verify_cmd, capture_output=True, text=True)
                # Safely handle None for stdout or stderr:
                verify_stdout = verify_result.stdout or ""
                verify_stderr = verify_result.stderr or ""
                verify_output = verify_stdout + "\n" + verify_stderr
            except Exception as e:
                rprint(f"[red]Error running verification program:[/red] {e}")
                verify_output = f"Verification program error: {e}"

            with open(error_log_file, "a") as elog:
                elog.write(f"\n[Verification attempt at iteration {iteration}]\n")
                elog.write(verify_output + "\n")

            rprint(f"[blue]Verification program output:[/blue]\n{escape_brackets(verify_output)}")

            if verify_result.returncode != 0:
                rprint("[red]Verification failed. Restoring last working code file from backup.[/red]")
                try:
                    shutil.copy(code_backup, code_file)
                    with open(error_log_file, "a") as elog:
                        elog.write(f"Restored code file from backup: {code_backup}\n")
                except Exception as e:
                    rprint(f"[red]Error restoring backup code file:[/red] {e}")
                    break

        # Re-run the tests in the same iteration:
        try:
            fails2, errors2, warnings2, second_run_output = run_pytest_on_file(unit_test_file)
        except Exception as e:
            rprint(f"[red]Error running second pytest attempt in iteration {iteration}:[/red] {e}")
            return False, "", "", fix_attempts, total_cost, model_name

        with open(error_log_file, "a") as elog:
            elog.write("\n=== Second Pytest Check (same iteration) ===\n")
            elog.write(second_run_output + "\n")

        rprint(f"[magenta]Second pytest check:[/magenta]\n{escape_brackets(second_run_output)}")

        if fails2 == 0 and errors2 == 0 and warnings2 == 0:
            rprint("[green]All tests passed on the second run of this iteration! Exiting loop.[/green]")
            break
        else:
            if (errors2 < best_iteration_info["errors"] or
                (errors2 == best_iteration_info["errors"] and fails2 < best_iteration_info["fails"]) or
                (errors2 == best_iteration_info["errors"] and fails2 == best_iteration_info["fails"] and warnings2 < best_iteration_info["warnings"])):
                best_iteration_info = {
                    "attempt": iteration,
                    "fails": fails2,
                    "errors": errors2,
                    "warnings": warnings2,
                    "unit_test_backup": unit_test_backup,
                    "code_backup": code_backup
                }

    # Final test run:
    try:
        final_fails, final_errors, final_warnings, final_output = run_pytest_on_file(unit_test_file)
    except Exception as e:
        rprint(f"[red]Error running final pytest:[/red] {e}")
        final_output = f"Error: {e}"
        final_fails = final_errors = final_warnings = sys.maxsize

    with open(error_log_file, "a") as elog:
        elog.write("\n=== Final Pytest Run ===\n")
        elog.write(final_output + "\n")

    rprint(f"[blue]Final pytest output:[/blue]\n{escape_brackets(final_output)}")

    # Possibly restore best iteration if the final run is not as good:
    if best_iteration_info["attempt"] is not None:
        is_better_final = False
        if final_errors < best_iteration_info["errors"]:
            is_better_final = True
        elif final_errors == best_iteration_info["errors"] and final_fails < best_iteration_info["fails"]:
            is_better_final = True
        elif (final_errors == best_iteration_info["errors"] and 
              final_fails == best_iteration_info["fails"] and 
              final_warnings < best_iteration_info["warnings"]):
            is_better_final = True
        
        if not is_better_final:
            # restore
            if verbose:
                rprint(f"[cyan]Restoring best iteration ({best_iteration_info['attempt']}) from backups.[/cyan]")
            try:
                if best_iteration_info["unit_test_backup"]:
                    shutil.copy(best_iteration_info["unit_test_backup"], unit_test_file)
                if best_iteration_info["code_backup"]:
                    shutil.copy(best_iteration_info["code_backup"], code_file)
            except Exception as e:
                rprint(f"[red]Error restoring best iteration backups:[/red] {e}")

    # Read final file contents
    try:
        with open(unit_test_file, "r") as f:
            final_unit_test = f.read()
        with open(code_file, "r") as f:
            final_code = f.read()
    except Exception as e:
        rprint(f"[red]Error reading final files:[/red] {e}")
        final_unit_test, final_code = "", ""

    success = (final_fails == 0 and final_errors == 0 and final_warnings == 0)
    if success:
        rprint("[green]Final tests passed with no warnings.[/green]")
    else:
        rprint("[red]Final tests still failing or producing warnings.[/red]")

    return success, final_unit_test, final_code, fix_attempts, total_cost, model_name

# If this module is run directly for testing purposes:
if __name__ == "__main__":
    # Example usage of fix_error_loop.
    unit_test_file = "tests/test_example.py"
    code_file = "src/code_example.py"
    prompt = "Write a function that adds two numbers"
    verification_program = "verify_code.py"  # Program that verifies the code
    strength = 0.5
    temperature = 0.0
    max_attempts = 5
    budget = 1.0  # Maximum cost budget
    error_log_file = "error_log.txt"
    verbose = True

    success, final_unit_test, final_code, attempts, total_cost, model_name = fix_error_loop(
        unit_test_file,
        code_file,
        prompt,
        verification_program,
        strength,
        temperature,
        max_attempts,
        budget,
        error_log_file,
        verbose
    )

    rprint(f"\n[bold]Process complete.[/bold]")
    rprint(f"Success: {success}")
    rprint(f"Attempts: {attempts}")
    rprint(f"Total cost: ${total_cost:.6f}")
    rprint(f"Model used: {model_name}")
    rprint(f"Final unit test contents:\n{final_unit_test}")
    rprint(f"Final code contents:\n{final_code}")