import os
import shutil
import subprocess
from typing import Tuple
from rich.console import Console
from rich.panel import Panel
from fix_errors_from_unit_tests import fix_errors_from_unit_tests

console = Console()

def fix_error_loop(
    unit_test_file: str,
    code_file: str,
    verification_program: str,
    strength: float,
    temperature: float,
    max_attempts: int,
    budget: float
) -> Tuple[bool, str, str, int, float]:
    """
    Attempts to fix errors in the code by running unit tests and applying fixes.

    :param unit_test_file: Path to the unit test file.
    :param code_file: Path to the code file.
    :param verification_program: Program used for verification.
    :param strength: Strength parameter for error fixing.
    :param temperature: Temperature parameter for error fixing.
    :param max_attempts: Maximum number of attempts to fix errors.
    :param budget: Budget for the total cost of fixing errors.
    :return: Tuple indicating success, updated unit test, updated code, number of attempts, and total cost.
    """

    # Step 1: Remove existing error.log file
    if os.path.exists("error.log"):
        os.remove("error.log")

    # Step 2: Initialize variables
    attempts = 0
    total_cost = 0.0
    best_iteration = {"fails": float('inf'), "errors": float('inf'), "attempt": 0}

    # Step 3: Main loop
    while attempts < max_attempts and total_cost < budget:
        attempts += 1
        console.print(Panel(f"Attempt {attempts}", style="bold magenta"))

        # Run pytest and capture output
        try:
            result = subprocess.run(
                ["python", "-m", "pytest", "-vv", unit_test_file],
                capture_output=True,
                text=True
            )
            with open("error.log", "a") as log_file:
                log_file.write(result.stdout + result.stderr)
        except subprocess.SubprocessError as e:
            console.print(f"[bold red]Error running pytest: {e}[/bold red]")
            continue

        # Check if tests passed
        if result.returncode == 0:
            console.print("[bold green]All tests passed. Exiting loop.[/bold green]")
            break

        # Parse error message and count fails/errors
        error_message = result.stdout + result.stderr
        fails = error_message.count("FAILED")
        errors = error_message.count("ERROR")
        console.print(f"[yellow]Fails: {fails}, Errors: {errors}[/yellow]")

        # Create backup files
        backup_suffix = f"{fails}_{errors}_{attempts}"
        unit_test_backup = f"{unit_test_file[:-3]}_{backup_suffix}.py"
        code_backup = f"{code_file[:-3]}_{backup_suffix}.py"
        shutil.copy(unit_test_file, unit_test_backup)
        shutil.copy(code_file, code_backup)

        # Read file contents
        with open(unit_test_file, "r") as f:
            unit_test_content = f.read()
        with open(code_file, "r") as f:
            code_content = f.read()

        # Call fix_errors_from_unit_tests
        try:
            update_unit_test, update_code, fixed_unit_test, fixed_code, iteration_cost = fix_errors_from_unit_tests(
                unit_test=unit_test_content,
                code=code_content,
                error=error_message,
                strength=strength,
                temperature=temperature
            )
            total_cost += iteration_cost

            with open("error.log", "a") as log_file:
                log_file.write(f"\n{'='*50}\nFix attempt output:\n")
                log_file.write(f"Update Unit Test: {update_unit_test}\n")
                log_file.write(f"Update Code: {update_code}\n")
                log_file.write(f"Fixed Unit Test:\n{fixed_unit_test}\n")
                log_file.write(f"Fixed Code:\n{fixed_code}\n")
                log_file.write(f"Iteration Cost: ${iteration_cost:.6f}\n{'='*50}\n")

        except Exception as e:
            console.print(f"[bold red]Error in fix_errors_from_unit_tests: {e}[/bold red]")
            continue

        if total_cost > budget:
            console.print("[bold red]Budget exceeded. Exiting loop.[/bold red]")
            break

    return (result.returncode == 0, update_unit_test, update_code, attempts, total_cost)