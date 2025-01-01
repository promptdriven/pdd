import os
import subprocess
import shutil
from rich.console import Console
from rich import print as rprint
from pdd.fix_code_module_errors import fix_code_module_errors

def fix_code_loop(
    code_file: str,
    prompt: str,
    verification_program: str,
    strength: float,
    temperature: float,
    max_attempts: int,
    budget: float,
    error_log_file: str = "error_code.log",
    verbose: bool = False,
) -> tuple[bool, str, str, int, float, str]:
    """
    Attempts to fix errors in a code module through multiple iterations.

    Args:
        code_file: Path to the code file being tested.
        prompt: Prompt that generated the code under test.
        verification_program: Path to a Python program that verifies if the code runs correctly.
        strength: Strength of the LLM model to use.
        temperature: Temperature parameter for the LLM model.
        max_attempts: Maximum number of fix attempts before giving up.
        budget: Maximum cost allowed for the fixing process.
        error_log_file: Path to the error log file (default: "error_code.log").
        verbose: Enable detailed logging of the fixing process (default: False).

    Returns:
        success: Whether the errors were successfully fixed.
        final_program: Contents of the final verification program file.
        final_code: Contents of the final code file.
        total_attempts: Number of fix attempts made.
        total_cost: Total cost of all fix attempts.
        model_name: Name of the LLM model used.
    """

    console = Console()

    # Step 1: Remove existing error log file
    if os.path.exists(error_log_file):
        os.remove(error_log_file)

    # Step 2: Initialize variables
    total_attempts = 0
    total_cost = 0.0
    model_name = ""

    # Check if verification program exists
    if not os.path.exists(verification_program):
        error_message = f"Error: Verification program not found at {verification_program}"
        rprint(f"[bold red]{error_message}[/bold red]")
        with open(error_log_file, "a") as f:
            f.write(error_message + "\n")
        return False, "", "", total_attempts, total_cost, model_name

    # Create backup copies of the original files
    original_verification_program = verification_program + ".original"
    original_code_file = code_file + ".original"
    shutil.copy(verification_program, original_verification_program)
    shutil.copy(code_file, original_code_file)

    # Step 3: Main loop
    success = False
    while total_attempts < max_attempts:
        rprint(f"\n[bold blue]Attempt: {total_attempts + 1}[/bold blue]")
        with open(error_log_file, "a") as f:
            f.write(f"\nAttempt: {total_attempts + 1}\n")

        # Run the verification program
        try:
            result = subprocess.run(
                ["python", verification_program],
                capture_output=True,
                text=True,
                check=False,
            )
            with open(error_log_file, "a") as f:
                f.write(result.stdout)
                f.write(result.stderr)

            # Check for successful execution
            if result.returncode == 0:
                rprint("[bold green]Code ran successfully![/bold green]")
                success = True
                break

        except FileNotFoundError:
            error_message = f"Error: Verification program not found at {verification_program}"
            rprint(f"[bold red]{error_message}[/bold red]")
            with open(error_log_file, "a") as f:
                f.write(error_message + "\n")
            return False, "", "", total_attempts, total_cost, model_name

        # If we get here, code failed
        rprint("[bold red]Code execution failed.[/bold red]")
        with open(error_log_file, "r") as f:
            error_message = f.read()

        # Escape square brackets for Rich printing
        escaped_error_message = error_message.replace("[", "\\[").replace("]", "\\]")
        rprint(f"[bold red]Errors found:\n[/bold red]{escaped_error_message}")

        # Create iteration backups
        verification_program_backup = (verification_program.rsplit(".", 1)[0]
                                       + f"_{total_attempts + 1}."
                                       + verification_program.rsplit(".", 1)[1])
        code_file_backup = (code_file.rsplit(".", 1)[0]
                            + f"_{total_attempts + 1}."
                            + code_file.rsplit(".", 1)[1])
        shutil.copy(verification_program, verification_program_backup)
        shutil.copy(code_file, code_file_backup)

        # Read current file contents
        try:
            with open(verification_program, "r") as f:
                program_content = f.read()
            with open(code_file, "r") as f:
                code_content = f.read()
        except FileNotFoundError as e:
            rprint(f"[bold red]Error reading files: {e}[/bold red]")
            with open(error_log_file, "a") as f:
                f.write(f"Error reading files: {e}\n")
            return False, "", "", total_attempts, total_cost, model_name

        # Check budget before calling fix_code_module_errors
        if total_cost >= budget:
            rprint(f"[bold red]Budget exceeded. Stopping.[/bold red]")
            success = False
            break

        # Call fix_code_module_errors
        temp_console = Console(file=open(os.devnull, "w"), record=True)
        with temp_console.capture() as capture:
            update_program, update_code, fixed_program, fixed_code, cost, model_name = fix_code_module_errors(
                program=program_content,
                prompt=prompt,
                code=code_content,
                errors=error_message,
                strength=strength,
                temperature=temperature,
                verbose=verbose,
            )
        captured_output = temp_console.export_text()
        rprint(captured_output)
        with open(error_log_file, "a") as f:
            f.write(captured_output)

        # Add the cost of this fix attempt
        total_cost += cost

        # Now increment attempts right after we’ve incurred cost
        total_attempts += 1

        # Check budget after fix
        if total_cost > budget:
            rprint("[bold red]Budget exceeded after fix attempt. Stopping.[/bold red]")
            success = False
            break

        # If no changes to either file, nothing more to do
        if not update_program and not update_code:
            rprint("[bold yellow]No changes needed. Stopping.[/bold yellow]")
            success = False
            break

        # Overwrite code file if updated
        if update_code:
            try:
                with open(code_file, "w") as f:
                    f.write(fixed_code)
            except FileNotFoundError as e:
                rprint(f"[bold red]Error writing to code file: {e}[/bold red]")
                with open(error_log_file, "a") as f:
                    f.write(f"Error writing to code file: {e}\n")
                return False, "", "", total_attempts, total_cost, model_name

        # Overwrite verification program if updated
        if update_program:
            try:
                with open(verification_program, "w") as f:
                    f.write(fixed_program)
            except FileNotFoundError as e:
                rprint(f"[bold red]Error writing to verification program: {e}[/bold red]")
                with open(error_log_file, "a") as f:
                    f.write(f"Error writing to verification program: {e}\n")
                return False, "", "", total_attempts, total_cost, model_name

    # Step 4: If not successful, restore the original files
    if not success:
        rprint("[bold yellow]Restoring original files.[/bold yellow]")
        shutil.copy(original_verification_program, verification_program)
        shutil.copy(original_code_file, code_file)
        final_program = ""
        final_code = ""
    else:
        try:
            with open(verification_program, "r") as f:
                final_program = f.read()
            with open(code_file, "r") as f:
                final_code = f.read()
        except FileNotFoundError as e:
            rprint(f"[bold red]Error reading final files: {e}[/bold red]")
            with open(error_log_file, "a") as f:
                f.write(f"Error reading final files: {e}\n")
            return False, "", "", total_attempts, total_cost, model_name

    return success, final_program, final_code, total_attempts, total_cost, model_name