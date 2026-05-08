import os
import shutil
import subprocess
from rich import print
from rich.console import Console
from fix_errors_from_unit_tests import fix_errors_from_unit_tests

console = Console()

def fix_error_loop(unit_test_file: str, code_file: str, verification_program: str, strength: float, temperature: float, max_attempts: int) -> tuple:
    """
    Iteratively attempts to fix errors in unit tests and code files.

    Args:
        unit_test_file (str): Path to the unit test file.
        code_file (str): Path to the code file.
        verification_program (str): Path to the verification program.
        strength (float): Strength parameter for error fixing.
        temperature (float): Temperature parameter for error fixing.
        max_attempts (int): Maximum number of attempts to fix errors.

    Returns:
        tuple: A tuple containing success status, final unit test contents,
               final code contents, and total number of attempts.
    """
    # Step 1: Remove the existing error.log file if it exists
    error_log_path = "error.log"
    if os.path.exists(error_log_path):
        os.remove(error_log_path)

    # Step 2: Initialize a counter for the number of attempts
    attempts = 0
    success = False

    # Step 3: Enter a while loop that continues until max_attempts is reached
    while attempts < max_attempts:
        attempts += 1

        # a. Run the unit_test_file with 'python -m pytest -vv' and pipe all output to error.log
        console.print(f"[bold blue]Running pytest for attempt {attempts}...[/bold blue]")
        with open(error_log_path, "w") as error_log:
            result = subprocess.run(
                ["python", "-m", "pytest", unit_test_file, "-vv"],
                stdout=error_log,
                stderr=subprocess.STDOUT
            )

        # b. If the test passes, break the loop
        if result.returncode == 0:
            console.print("[bold green]Tests passed![/bold green]")
            success = True
            break

        # c. If the test fails:
        console.print("[bold red]Tests failed. Reading error log...[/bold red]")
        with open(error_log_path, "r") as error_log:
            error_message = error_log.read()
            console.print(error_message)

        # Count the number of 'FAILED' and 'ERROR' from the error log
        fail_count = error_message.count("FAILED")
        error_count = error_message.count("ERROR")

        # Create backup copies of the unit_test_file and code_file
        backup_unit_test = f"unit_test_{fail_count}_{error_count}_{attempts}.py"
        backup_code = f"code_{fail_count}_{error_count}_{attempts}.py"
        shutil.copy(unit_test_file, backup_unit_test)
        shutil.copy(code_file, backup_code)

        # Read the contents of the unit_test_file and code_file
        with open(unit_test_file, "r") as f:
            unit_test_code = f.read()
        with open(code_file, "r") as f:
            code_under_test = f.read()

        # Call fix_errors_from_unit_tests
        try:
            update_unit_test, update_code, fixed_unit_test, fixed_code, _ = fix_errors_from_unit_tests(
                unit_test=unit_test_code,
                code=code_under_test,
                error=error_message,
                strength=strength,
                temperature=temperature
            )
        except Exception as e:
            console.print(f"[bold red]Error during fix attempt: {e}[/bold red]")
            break

        # If both updated_unit_test and updated_code are False, break the loop
        if not update_unit_test and not update_code:
            console.print("[bold yellow]No changes were needed. Exiting loop.[/bold yellow]")
            break

        # If either updated_unit_test or updated_code is True, write the changes
        if update_unit_test:
            with open(unit_test_file, "w") as f:
                f.write(fixed_unit_test)
        if update_code:
            with open(code_file, "w") as f:
                f.write(fixed_code)

        # Run the verification_program
        console.print("[bold blue]Running verification program...[/bold blue]")
        verification_result = subprocess.run(
            ["python", verification_program],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )

        if verification_result.returncode != 0:
            console.print("[bold red]Verification failed. Restoring backups...[/bold red]")
            shutil.copy(backup_unit_test, unit_test_file)
            shutil.copy(backup_code, code_file)
        else:
            console.print("[bold green]Verification succeeded.[/bold green]")

    # Step 4: After the loop ends, run pytest one last time
    console.print("[bold blue]Final pytest run...[/bold blue]")
    with open(error_log_path, "w") as error_log:
        subprocess.run(
            ["python", "-m", "pytest", unit_test_file, "-vv"],
            stdout=error_log,
            stderr=subprocess.STDOUT
        )
    with open(error_log_path, "r") as error_log:
        console.print(error_log.read())

    # Step 5: Return the success status, final unit test contents, final code contents, and total number of attempts
    with open(unit_test_file, "r") as f:
        final_unit_test = f.read()
    with open(code_file, "r") as f:
        final_code = f.read()

    return success, final_unit_test, final_code, attempts
