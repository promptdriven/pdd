import os
import subprocess
import shutil
from typing import Tuple
from rich import print as rprint
from rich.console import Console
from rich.panel import Panel
from .fix_errors_from_unit_tests import fix_errors_from_unit_tests

console = Console()

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
        # Step 1: Remove existing error log file
        if os.path.exists(error_log_file):
            os.remove(error_log_file)

        # Step 2: Initialize variables
        attempts = 0
        total_cost = 0.0
        best_iteration = {"fails": float('inf'), "errors": float('inf'), "attempt": 0}
        model_name = ""

        # Step 3: Main loop
        while attempts < max_attempts and total_cost < budget:
            attempts += 1
            
            # Run pytest and capture output
            with open(error_log_file, "a") as log_file:
                result = subprocess.run(
                    ["python", "-m", "pytest", "-vv", unit_test_file],
                    capture_output=True,
                    text=True
                )
                log_file.write(result.stdout)
                log_file.write(result.stderr)

            # Check if tests pass
            if result.returncode == 0:
                rprint(Panel("[green]All tests passed![/green]"))
                break

            # Process test failures
            with open(error_log_file, "r") as log_file:
                error_output = log_file.read()

            rprint(Panel(f"[red]Test failures detected in attempt {attempts}:[/red]\n{error_output}"))

            fails = result.stdout.count("FAILED")
            errors = result.stdout.count("ERROR")
            
            # Adjust for -vv flag doubling the messages
            fails //= 2
            errors //= 2

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
                verification_result = subprocess.run(["python", verification_program], capture_output=True, text=True)
                if verification_result.returncode != 0:
                    rprint(Panel("[red]Verification failed. Restoring original code.[/red]"))
                    shutil.copy2(backup_code, code_file)
                else:
                    rprint(Panel("[green]Verification successful.[/green]"))
                    if fails + errors < best_iteration["fails"] + best_iteration["errors"]:
                        best_iteration = {"fails": fails, "errors": errors, "attempt": attempts}

        # Step 4: Final pytest run
        with open(error_log_file, "a") as log_file:
            final_result = subprocess.run(
                ["python", "-m", "pytest", "-vv", unit_test_file],
                capture_output=True,
                text=True
            )
            log_file.write(final_result.stdout)
            log_file.write(final_result.stderr)

        rprint(Panel(f"[bold]Final test results:[/bold]\n{final_result.stdout}"))

        # Step 5: Restore best iteration if necessary
        if final_result.returncode != 0 and best_iteration["attempt"] != attempts:
            best_unit_test = f"{unit_test_file[:-3]}_{best_iteration['fails']}_{best_iteration['errors']}_{best_iteration['attempt']}.py"
            best_code = f"{code_file[:-3]}_{best_iteration['fails']}_{best_iteration['errors']}_{best_iteration['attempt']}.py"
            shutil.copy2(best_unit_test, unit_test_file)
            shutil.copy2(best_code, code_file)
            rprint(Panel(f"[yellow]Restored best iteration (attempt {best_iteration['attempt']}).[/yellow]"))

        # Step 6: Prepare return values
        success = final_result.returncode == 0
        with open(unit_test_file, "r") as f:
            final_unit_test = f.read()
        with open(code_file, "r") as f:
            final_code = f.read()

        return success, final_unit_test, final_code, attempts, total_cost, model_name

    except Exception as e:
        rprint(Panel(f"[red]An error occurred: {str(e)}[/red]"))
        return False, "", "", 0, 0.0, ""
