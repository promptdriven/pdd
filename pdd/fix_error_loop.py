import os
import shutil
import subprocess
from typing import Tuple
from rich.console import Console
from rich.panel import Panel
from .fix_errors_from_unit_tests import fix_errors_from_unit_tests

console = Console()

def fix_error_loop(
    unit_test_file: str,
    code_file: str,
    verification_program: str,
    strength: float,
    temperature: float,
    max_attempts: int,
    budget: float,
    error_log_file: str = "error_log.txt"
) -> Tuple[bool, str, str, int, float]:
    """
    Attempts to fix errors in the code by running unit tests and applying fixes.

    :param unit_test_file: Path to the unit test file.
    :param code_file: Path to the code file.
    :param verification_program: Path to the verification program.
    :param strength: Strength parameter for the error fixing function.
    :param temperature: Temperature parameter for the error fixing function.
    :param max_attempts: Maximum number of attempts to fix errors.
    :param budget: Maximum budget for fixing errors.
    :param error_log_file: Path to the error log file (default: "error_log.txt").
    :return: Tuple containing success status, final unit test content, final code content, number of attempts, and total cost.
    """

    if os.path.exists(error_log_file):
        os.remove(error_log_file)

    attempts = 0
    total_cost = 0.0
    success = False

    # Read initial contents of unit test and code files
    with open(unit_test_file, 'r') as f:
        unit_test_content = f.read()
    with open(code_file, 'r') as f:
        code_content = f.read()

    # Keep track of the last working version
    last_working_unit_test = unit_test_content
    last_working_code = code_content

    while attempts < max_attempts and total_cost < budget:
        attempts += 1
        console.print(Panel(f"[bold cyan]Attempt {attempts}[/bold cyan]"))

        try:
            result = subprocess.run(['python', '-m', 'pytest', '-vv', unit_test_file], 
                                    capture_output=True, text=True)
            with open(error_log_file, 'w') as f:  # Use 'w' mode to overwrite previous errors
                f.write(result.stdout)
                f.write(result.stderr)

            if result.returncode == 0:
                console.print("[bold green]All tests passed![/bold green]")
                success = True
                break

            console.print("[bold red]Test failed. Error message:[/bold red]")
            console.print(result.stderr)

            fails = result.stdout.count("FAILED")
            errors = result.stdout.count("ERROR")
            fails //= 2  # Account for -vv flag doubling the messages
            errors //= 2

            backup_unit_test = f"unit_test_{fails}_{errors}_{attempts}.py"
            backup_code = f"code_{fails}_{errors}_{attempts}.py"
            shutil.copy(unit_test_file, backup_unit_test)
            shutil.copy(code_file, backup_code)

            with open(error_log_file, 'r') as f:
                error_content = f.read()

            console.print("[bold yellow]Attempting to fix errors...[/bold yellow]")
            update_unit_test, update_code, fixed_unit_test, fixed_code, fix_cost = fix_errors_from_unit_tests(
                unit_test=unit_test_content,
                code=code_content,
                error=error_content,
                error_file=error_log_file,
                strength=strength,
                temperature=temperature
            )

            total_cost += fix_cost
            console.print(f"[bold]Cost for this fix attempt: ${fix_cost:.6f}[/bold]")
            console.print(f"[bold]Total cost so far: ${total_cost:.6f}[/bold]")

            if total_cost > budget:
                console.print("[bold red]Budget exceeded. Stopping.[/bold red]")
                break

            if not update_unit_test and not update_code:
                console.print("[bold yellow]No changes were needed. Stopping.[/bold yellow]")
                break

            if update_unit_test:
                # Apply changes
                unit_test_content = fixed_unit_test
                with open(unit_test_file, 'w') as f:
                    f.write(fixed_unit_test)
          
            if update_code:
                # Apply changes
                code_content = fixed_code
                with open(code_file, 'w') as f:
                    f.write(fixed_code)

                console.print("[bold]Running verification program...[/bold]")
                verification_result = subprocess.run(['python', verification_program], 
                                                     capture_output=True, text=True)
                
                if verification_result.returncode == 0:
                    console.print("[bold green]Verification passed. Saving this version.[/bold green]")
                    last_working_code = code_content
                else:
                    console.print("[bold red]Verification failed. Reverting to last working version.[/bold red]")
                    code_content = last_working_code
                    with open(code_file, 'w') as f:
                        f.write(last_working_code)

        except Exception as e:
            console.print(f"[bold red]An error occurred: {e}[/bold red]")
            break

    return (success, unit_test_content, code_content, attempts, total_cost)