#!/usr/bin/env python3
import os
import sys
import re
import subprocess
import shutil
from datetime import datetime

from rich import print as rprint
from rich.console import Console

# Relative import from an internal module.
from .fix_errors_from_unit_tests import fix_errors_from_unit_tests

console = Console()

def escape_brackets(text: str) -> str:
    """Escape square brackets so Rich doesn't misinterpret them."""
    return text.replace("[", "\\[").replace("]", "\\]")

def extract_pytest_summary(log_contents: str) -> (int, int, int):
    """
    Extract the number of fails, errors and warnings from pytest output.
    Try to match a typical summary line first; if not found fall back to individual regex searches.
    Returns a tuple: (fails, errors, warnings)
    """
    fails, errors, warnings = sys.maxsize, sys.maxsize, sys.maxsize  # defaults if not found
    summary_pattern = re.compile(
        r"=+\s*(\d+)\s+failed.*?,.*?(\d+)\s+passed.*?,.*?(\d+)\s+warnings", re.IGNORECASE | re.DOTALL
    )
    match = summary_pattern.search(log_contents)
    if match:
        fails = int(match.group(1))
        # In some pytest outputs, failures and errors may be reported separately.
        errors = int(match.group(1))  # assume same value if no distinct errors are provided
        warnings = int(match.group(3))
    else:
        failed_match = re.search(r"(\d+)\s+failed", log_contents, re.IGNORECASE)
        errors_match = re.search(r"(\d+)\s+error", log_contents, re.IGNORECASE)
        warnings_match = re.search(r"(\d+)\s+warning", log_contents, re.IGNORECASE)
        fails = int(failed_match.group(1)) if failed_match else 0
        errors = int(errors_match.group(1)) if errors_match else 0
        warnings = int(warnings_match.group(1)) if warnings_match else 0

    return fails, errors, warnings

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
    Attempt to fix errors in a unit test and corresponding code using repeated iterations.
    
    Inputs:
        unit_test_file: Path to the file containing unit tests.
        code_file: Path to the file containing the code under test.
        prompt: Prompt that generated the code under test.
        verification_program: Path to a Python program that verifies the code still works.
        strength: float [0,1] representing LLM fix strength.
        temperature: float [0,1] representing LLM temperature.
        max_attempts: Maximum number of iterations for fixes.
        budget: Maximum cost allowed for the fixing process.
        error_log_file: Path to file to log errors (default: "error_log.txt").
        verbose: Enable verbose logging (default: False).

    Outputs:
        success: Boolean indicating if the overall process succeeded.
        final_unit_test: String contents of the final unit test file.
        final_code: String contents of the final code file.
        total_attempts: Number of fix attempts made.
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

    attempt = 0
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

    # Timestamp for backup naming.
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    
    while attempt < max_attempts and total_cost < budget:
        attempt += 1
        iteration_header = f"=== Attempt {attempt} ==="
        rprint(f"[bold blue]{iteration_header}[/bold blue]")
        # Append header to error log.
        with open(error_log_file, "a") as elog:
            elog.write(f"\n{iteration_header}\n")
        
        # Step 2a: Run pytest on the unit test file.
        try:
            # Run pytest via subprocess.
            # Here we assume that the unit_test_file is discoverable or we pass it explicitly.
            pytest_cmd = [sys.executable, "-m", "pytest", "-vv", "--no-cov", unit_test_file]
            result = subprocess.run(pytest_cmd, capture_output=True, text=True)
            pytest_output = result.stdout + "\n" + result.stderr
        except Exception as e:
            rprint(f"[red]Error running pytest:[/red] {e}")
            return False, "", "", attempt, total_cost, model_name

        # Append the pytest output to the error log file.
        with open(error_log_file, "a") as elog:
            elog.write(pytest_output + "\n")
        
        # Escape square brackets for safe rprint.
        output_escaped = escape_brackets(pytest_output)
        rprint(f"[magenta]Pytest output:[/magenta]\n{output_escaped}")

        # Step 2b: Extract numbers of fails, errors, warnings.
        fails, errors, warnings = extract_pytest_summary(pytest_output)
        if verbose:
            rprint(f"[cyan]Iteration summary: {fails} failed, {errors} errors, {warnings} warnings[/cyan]")

        # Check if tests passed and there are no warnings.
        if fails == 0 and errors == 0 and warnings == 0:
            rprint("[green]All tests passed with no warnings! Exiting loop.[/green]")
            break

        # Step 2c: Create backup copies for unit_test_file and code_file.
        unit_test_dir, unit_test_name = os.path.split(unit_test_file)
        code_dir, code_name = os.path.split(code_file)
        unit_test_backup = os.path.join(unit_test_dir,
                                        f"{os.path.splitext(unit_test_name)[0]}_{attempt}_{errors}_{fails}_{warnings}_{timestamp}.py")
        code_backup = os.path.join(code_dir,
                                   f"{os.path.splitext(code_name)[0]}_{attempt}_{errors}_{fails}_{warnings}_{timestamp}.py")
        try:
            shutil.copy(unit_test_file, unit_test_backup)
            shutil.copy(code_file, code_backup)
            if verbose:
                rprint(f"[green]Created backup for unit test:[/green] {unit_test_backup}")
                rprint(f"[green]Created backup for code file:[/green] {code_backup}")
        except Exception as e:
            rprint(f"[red]Error creating backup files:[/red] {e}")
            return False, "", "", attempt, total_cost, model_name

        # Update best_iteration tracker if this iteration has fewer errors, fails, warnings.
        if (errors < best_iteration_info["errors"] or
           (errors == best_iteration_info["errors"] and fails < best_iteration_info["fails"]) or
           (errors == best_iteration_info["errors"] and fails == best_iteration_info["fails"] and warnings < best_iteration_info["warnings"])):
            best_iteration_info = {
                "attempt": attempt,
                "fails": fails,
                "errors": errors,
                "warnings": warnings,
                "unit_test_backup": unit_test_backup,
                "code_backup": code_backup
            }
            if verbose:
                rprint(f"[cyan]Updated best iteration to attempt {attempt} (errors: {errors}, fails: {fails}, warnings: {warnings}).[/cyan]")
        
        # Step 2d: Read file contents.
        try:
            with open(unit_test_file, "r") as f:
                unit_test_contents = f.read()
            with open(code_file, "r") as f:
                code_contents = f.read()
        except Exception as e:
            rprint(f"[red]Error reading input files:[/red] {e}")
            return False, "", "", attempt, total_cost, model_name

        # Call the internal fix_errors_from_unit_tests function.
        try:
            (updated_unit_test,
             updated_code,
             fixed_unit_test,
             fixed_code,
             cost,
             model_name) = fix_errors_from_unit_tests(
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

        # Add cost.
        total_cost += cost
        if verbose:
            rprint(f"[cyan]Iteration fix cost: ${cost:.6f}, Total cost: ${total_cost:.6f}[/cyan]")
        if total_cost > budget:
            rprint(f"[red]Exceeded the budget of ${budget:.6f}. Ending fixing loop.[/red]")
            break

        # If neither unit test nor code was updated, likely no changes were needed.
        if not updated_unit_test and not updated_code:
            rprint("[yellow]No changes were suggested by the LLM. Exiting loop.[/yellow]")
            break

        # Step 2e: If updated_unit_test is True, write the updates back.
        if updated_unit_test:
            try:
                with open(unit_test_file, "w") as f:
                    f.write(fixed_unit_test)
                if verbose:
                    rprint(f"[green]Unit test file updated.[/green]")
            except Exception as e:
                rprint(f"[red]Error writing updated unit test file:[/red] {e}")
                break

        # Increment attempt counter is already performed at loop start.
        # Step 2f: If updated_code is True, update code file and verify.
        if updated_code:
            try:
                with open(code_file, "w") as f:
                    f.write(fixed_code)
                if verbose:
                    rprint(f"[green]Code file updated.[/green]")
            except Exception as e:
                rprint(f"[red]Error writing updated code file:[/red] {e}")
                break

            # Run the verification program.
            try:
                verify_cmd = [sys.executable, verification_program]
                verify_result = subprocess.run(verify_cmd, capture_output=True, text=True)
                verify_output = verify_result.stdout + "\n" + verify_result.stderr
            except Exception as e:
                rprint(f"[red]Error running verification program:[/red] {e}")
                verify_output = f"Verification program error: {e}"

            # Log verification output.
            with open(error_log_file, "a") as elog:
                elog.write(f"\n[Verification attempt at iteration {attempt}]\n")
                elog.write(verify_output + "\n")
            rprint(f"[blue]Verification program output:[/blue]\n{escape_brackets(verify_output)}")

            # Check if verification failed. Assume non-zero return code indicates failure.
            if verify_result.returncode != 0:
                rprint(f"[red]Verification failed. Restoring last working code file from backup.[/red]")
                try:
                    # Restore code file from the backup of this iteration.
                    shutil.copy(code_backup, code_file)
                    with open(error_log_file, "a") as elog:
                        elog.write(f"Restored code file from backup: {code_backup}\n")
                except Exception as e:
                    rprint(f"[red]Error restoring backup code file:[/red] {e}")
                    break
                continue  # Continue next loop iteration after restore.
        
        # End of while loop iteration.
    
    # Step 4: After loop, run pytest one last time.
    try:
        final_pytest_cmd = [sys.executable, "-m", "pytest", "-vv", "--no-cov", unit_test_file]
        final_result = subprocess.run(final_pytest_cmd, capture_output=True, text=True)
        final_output = final_result.stdout + "\n" + final_result.stderr
    except Exception as e:
        rprint(f"[red]Error running final pytest:[/red] {e}")
        final_output = f"Error: {e}"

    # Append final output to error log.
    with open(error_log_file, "a") as elog:
        elog.write("\n=== Final Pytest Run ===\n")
        elog.write(final_output + "\n")
    rprint(f"[blue]Final pytest output:[/blue]\n{escape_brackets(final_output)}")
    
    # Step 5: If the last iteration is not the best, restore the best iteration backups.
    best_attempt = best_iteration_info.get("attempt")
    if best_attempt is not None:
        # Optionally compare the last iteration numbers with best_iteration_info here.
        if verbose:
            rprint(f"[cyan]Restoring best iteration ({best_attempt}) from backups.[/cyan]")
        try:
            if best_iteration_info["unit_test_backup"]:
                shutil.copy(best_iteration_info["unit_test_backup"], unit_test_file)
            if best_iteration_info["code_backup"]:
                shutil.copy(best_iteration_info["code_backup"], code_file)
        except Exception as e:
            rprint(f"[red]Error restoring best iteration backups:[/red] {e}")
    
    # Read final file contents.
    try:
        with open(unit_test_file, "r") as f:
            final_unit_test = f.read()
        with open(code_file, "r") as f:
            final_code = f.read()
    except Exception as e:
        rprint(f"[red]Error reading final files:[/red] {e}")
        final_unit_test, final_code = "", ""

    # Determine success based on final pytest result: pass if no failures, errors or warnings.
    final_fails, final_errors, final_warnings = extract_pytest_summary(final_output)
    success = (final_fails == 0 and final_errors == 0 and final_warnings == 0)
    if success:
        rprint("[green]Final tests passed with no warnings.[/green]")
    else:
        rprint("[red]Final tests still failing or producing warnings.[/red]")
    
    return success, final_unit_test, final_code, attempt, total_cost, model_name

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