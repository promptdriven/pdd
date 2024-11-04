import os
import shutil
import subprocess
from pathlib import Path
from typing import Tuple
from rich import print
from rich.console import Console
from io import StringIO
import sys

# Relative import for internal module
from .fix_code_module_errors import fix_code_module_errors

def fix_code_loop(
    code_file: str,
    prompt: str,
    verification_program: str,
    strength: float,
    temperature: float,
    max_attempts: int,
    budget: float,
    error_log_file: str = "error_code.log"
) -> Tuple[bool, str, str, int, float, str]:
    """
    Attempts to fix errors in a code module through multiple iterations.

    Args:
        code_file (str): Path to the code file being tested.
        prompt (str): Prompt that generated the code under test.
        verification_program (str): Path to a Python program that verifies if the code runs correctly.
        strength (float): Strength of the LLM model to use (0 <= strength <= 1).
        temperature (float): Temperature parameter for the LLM model (0 <= temperature <= 1).
        max_attempts (int): Maximum number of fix attempts before giving up.
        budget (float): Maximum cost allowed for the fixing process.
        error_log_file (str, optional): Path to the error log file. Defaults to "error_code.log".

    Returns:
        Tuple[bool, str, str, int, float, str]:
            success (bool): Whether the errors were successfully fixed.
            final_program (str): Contents of the final verification program file.
            final_code (str): Contents of the final code file.
            total_attempts (int): Number of fix attempts made.
            total_cost (float): Total cost of all fix attempts.
            model_name (str): Name of the LLM model used.
    """
    console = Console()

    # Input Validation
    try:
        if not isinstance(code_file, str) or not Path(code_file).is_file():
            raise ValueError(f"Invalid code_file path: {code_file}")
        if not isinstance(prompt, str) or not prompt.strip():
            raise ValueError("Prompt must be a non-empty string.")
        if not isinstance(verification_program, str) or not Path(verification_program).is_file():
            raise ValueError(f"Invalid verification_program path: {verification_program}")
        if not (0 <= strength <= 1):
            raise ValueError("Strength must be a float between 0 and 1.")
        if not (0 <= temperature <= 1):
            raise ValueError("Temperature must be a float between 0 and 1.")
        if not isinstance(max_attempts, int) or max_attempts <= 0:
            raise ValueError("max_attempts must be a positive integer.")
        if not isinstance(budget, (int, float)) or budget <= 0:
            raise ValueError("budget must be a positive float.")
        if not isinstance(error_log_file, str):
            raise ValueError("error_log_file must be a string.")
    except Exception as e:
        console.print(f"[red]Input Validation Error:[/red] {e}")
        return False, "", "", 0, 0.0, ""

    error_log_path = Path(error_log_file)

    # Step 1: Remove existing error log file if it exists
    try:
        if error_log_path.exists():
            error_log_path.unlink()
            console.print(f"[yellow]Removed existing error log file: {error_log_file}[/yellow]")
    except Exception as e:
        console.print(f"[red]Failed to remove error log file:[/red] {e}")
        return False, "", "", 0, 0.0, ""

    # Step 2: Initialize variables
    attempts = 0
    total_cost = 0.0
    success = False
    model_name = ""
    original_program_backup = verification_program + ".backup_original"
    original_code_backup = code_file + ".backup_original"

    try:
        # Create backups of the original files
        shutil.copyfile(verification_program, original_program_backup)
        shutil.copyfile(code_file, original_code_backup)
    except Exception as e:
        console.print(f"[red]Failed to create backups of original files:[/red] {e}")
        return False, "", "", 0, 0.0, ""

    # Step 3: Enter the fix attempts loop
    while attempts < max_attempts and total_cost <= budget:
        attempts += 1
        console.print(f"\n[bold blue]Attempt {attempts}[/bold blue]")
        with open(error_log_path, "a") as log_file:
            log_file.write(f"\n=== Attempt {attempts} ===\n")

        # Step 3b: Run the verification program
        try:
            result = subprocess.run(
                [sys.executable, verification_program],
                capture_output=True,
                text=True,
                timeout=60  # Prevent hanging
            )
            stdout = result.stdout
            stderr = result.stderr
            with open(error_log_path, "a") as log_file:
                log_file.write(stdout)
                log_file.write(stderr)

            if result.returncode == 0:
                console.print(f"[green]Verification program ran successfully.[/green]")
                success = True
                break
            else:
                error_message = stderr.strip()
                # Escape square brackets
                escaped_error = error_message.replace("[", "\\[").replace("]", "\\]")
                console.print(f"[red]Error in verification program:[/red]\n{escaped_error}")
        except subprocess.TimeoutExpired:
            error_message = "Verification program timed out."
            escaped_error = error_message.replace("[", "\\[").replace("]", "\\]")
            console.print(f"[red]{escaped_error}[/red]")
            with open(error_log_path, "a") as log_file:
                log_file.write(escaped_error + "\n")
            break
        except Exception as e:
            error_message = f"Failed to run verification program: {e}"
            escaped_error = error_message.replace("[", "\\[").replace("]", "\\]")
            console.print(f"[red]{escaped_error}[/red]")
            with open(error_log_path, "a") as log_file:
                log_file.write(escaped_error + "\n")
            break

        # Step 3d: If program fails, attempt to fix
        try:
            # Create backup copies with iteration number
            verification_backup = Path(verification_program)
            code_backup = Path(code_file)
            verification_backup_copy = verification_backup.with_name(
                verification_backup.stem + f"_{attempts}" + verification_backup.suffix
            )
            code_backup_copy = code_backup.with_name(
                code_backup.stem + f"_{attempts}" + code_backup.suffix
            )
            shutil.copyfile(verification_program, verification_backup_copy)
            shutil.copyfile(code_file, code_backup_copy)
            console.print(f"[yellow]Backup created: {verification_backup_copy} and {code_backup_copy}[/yellow]")

            # Read contents of verification_program and code_file
            with open(verification_program, "r") as vp_file:
                verification_content = vp_file.read()
            with open(code_file, "r") as cf_file:
                code_content = cf_file.read()

            # Read errors from error log file
            with open(error_log_path, "r") as log_file:
                log_contents = log_file.read()
            last_errors = log_contents.split("=== Attempt", attempts+1)[-1].strip()

            # Capture the output of fix_code_module_errors
            captured_output = StringIO()
            temp_console = Console(file=captured_output, record=True)
            try:
                # Redirect the Rich console to capture output
                original_console = fix_code_module_errors.__globals__['console']
                fix_code_module_errors.__globals__['console'] = temp_console

                # Call the fix function
                fix_results = fix_code_module_errors(
                    program=verification_content,
                    prompt=prompt,
                    code=code_content,
                    errors=last_errors,
                    strength=strength,
                    temperature=temperature
                )

                # Restore the original console
                fix_code_module_errors.__globals__['console'] = original_console
            except Exception as e:
                fix_results = (False, False, "", "", 0.0, "")
                fix_error = f"fix_code_module_errors failed: {e}"
                captured_output.write(fix_error + "\n")
                temp_console.print(f"[red]{fix_error}[/red]")

            fix_output = captured_output.getvalue()
            # Print and log the fix_output
            console.print(fix_output)
            with open(error_log_path, "a") as log_file:
                log_file.write(fix_output + "\n")

            # Unpack the results
            if isinstance(fix_results, tuple) and len(fix_results) == 6:
                update_program, update_code, fixed_program, fixed_code, attempt_cost, used_model = fix_results
                model_name = used_model
            else:
                console.print("[red]Invalid response from fix_code_module_errors.[/red]")
                break

            total_cost += attempt_cost

            if total_cost > budget:
                console.print(f"[red]Budget exceeded: ${total_cost:.4f} > ${budget:.4f}[/red]")
                break

            if not update_program and not update_code:
                console.print("[yellow]No updates made by fix_code_module_errors. Stopping attempts.[/yellow]")
                break

            # Apply the fixes
            if update_code:
                try:
                    with open(code_file, "w") as cf_file:
                        cf_file.write(fixed_code)
                    console.print(f"[green]Updated code file: {code_file}[/green]")
                except Exception as e:
                    console.print(f"[red]Failed to update code file: {e}[/red]")
                    break

            if update_program:
                try:
                    with open(verification_program, "w") as vp_file:
                        vp_file.write(fixed_program)
                    console.print(f"[green]Updated verification program: {verification_program}[/green]")
                except Exception as e:
                    console.print(f"[red]Failed to update verification program: {e}[/red]")
                    break

        except Exception as e:
            console.print(f"[red]An error occurred during the fixing process: {e}[/red]")
            with open(error_log_path, "a") as log_file:
                log_file.write(f"Fixing process error: {e}\n")
            break

    # Step 4: Restore original files if not successful
    if not success:
        try:
            shutil.copyfile(original_program_backup, verification_program)
            shutil.copyfile(original_code_backup, code_file)
            console.print(f"[yellow]Restored original files from backups.[/yellow]")
        except Exception as e:
            console.print(f"[red]Failed to restore original files: {e}[/red]")

    # Step 5: Read final contents
    try:
        with open(verification_program, "r") as vp_file:
            final_program = vp_file.read()
        with open(code_file, "r") as cf_file:
            final_code = cf_file.read()
    except Exception as e:
        console.print(f"[red]Failed to read final files: {e}[/red]")
        final_program = ""
        final_code = ""

    # Cleanup backups
    try:
        if Path(original_program_backup).exists():
            Path(original_program_backup).unlink()
        if Path(original_code_backup).exists():
            Path(original_code_backup).unlink()
    except Exception as e:
        console.print(f"[red]Failed to remove backup files: {e}[/red]")

    return success, final_program, final_code, attempts, total_cost, model_name
