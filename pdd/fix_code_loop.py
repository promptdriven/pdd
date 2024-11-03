import os
import shutil
import subprocess
from pathlib import Path
from rich import print as rprint
from typing import Tuple
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
        code_file: Path to the code file being tested
        prompt: Prompt that generated the code under test
        verification_program: Path to the verification program
        strength: Strength of the LLM model (0-1)
        temperature: Temperature parameter for the LLM model (0-1)
        max_attempts: Maximum number of fix attempts
        budget: Maximum cost allowed for fixing
        error_log_file: Path to the error log file
    
    Returns:
        Tuple containing:
        - success: Whether errors were fixed
        - final_program: Contents of final verification program
        - final_code: Contents of final code file
        - total_attempts: Number of fix attempts made
        - total_cost: Total cost of all fix attempts
        - model_name: Name of the LLM model used
    """
    # Input validation
    if not all(os.path.exists(f) for f in [code_file, verification_program]):
        raise FileNotFoundError("Code file or verification program not found")
    if not (0 <= strength <= 1 and 0 <= temperature <= 1):
        raise ValueError("Strength and temperature must be between 0 and 1")
    if max_attempts < 1:
        raise ValueError("max_attempts must be at least 1")
    if budget <= 0:
        raise ValueError("budget must be positive")

    # Step 1: Remove existing error log file
    if os.path.exists(error_log_file):
        os.remove(error_log_file)

    # Step 2: Initialize variables
    attempt_count = 0
    total_cost = 0.0
    model_name = ""
    best_iteration = {"errors": float('inf'), "iteration": 0}

    # Create backup of original files
    code_path = Path(code_file)
    verif_path = Path(verification_program)
    original_code = code_path.read_text()
    original_program = verif_path.read_text()

    while attempt_count < max_attempts:
        attempt_count += 1
        
        # Step 3a: Print iteration information
        rprint(f"[bold blue]Attempt {attempt_count}/{max_attempts}[/bold blue]")
        
        # Step 3b: Run verification program
        with open(error_log_file, 'a') as log:
            result = subprocess.run(
                ['python', verification_program],
                capture_output=True,
                text=True
            )
            log.write(f"\n--- Attempt {attempt_count} ---\n")
            log.write(result.stderr if result.stderr else result.stdout)

        # Step 3c: Check if program runs without errors
        if result.returncode == 0:
            rprint("[bold green]Success! No errors found.[/bold green]")
            break

        # Step 3d: Handle program failure
        with open(error_log_file, 'r') as log:
            error_content = log.read()
            # Escape square brackets for rich print
            rprint(f"[bold red]Errors found:[/bold red]\n{error_content.replace('[', '\\[').replace(']', '\\]')}")

        # Create backup files
        backup_code = code_path.with_name(f"{code_path.stem}_{attempt_count}{code_path.suffix}")
        backup_verif = verif_path.with_name(f"{verif_path.stem}_{attempt_count}{verif_path.suffix}")
        shutil.copy2(code_file, backup_code)
        shutil.copy2(verification_program, backup_verif)

        # Call fix_code_module_errors
        update_program, update_code, fixed_program, fixed_code, cost, current_model = fix_code_module_errors(
            program=verif_path.read_text(),
            prompt=prompt,
            code=code_path.read_text(),
            errors=error_content,
            strength=strength,
            temperature=temperature
        )

        total_cost += cost
        model_name = current_model

        # Check budget
        if total_cost > budget:
            rprint("[bold red]Budget exceeded. Stopping fixes.[/bold red]")
            break

        # Check if no changes needed
        if not update_program and not update_code:
            rprint("[bold yellow]No changes needed in this iteration.[/bold yellow]")
            break

        # Update files if needed
        if update_code:
            code_path.write_text(fixed_code)
        if update_program:
            verif_path.write_text(fixed_program)

    # Step 4: Restore original files if not successful
    success = result.returncode == 0
    if not success:
        code_path.write_text(original_code)
        verif_path.write_text(original_program)
        rprint("[bold red]Could not fix all errors. Restored original files.[/bold red]")

    # Step 5: Return results
    return (
        success,
        verif_path.read_text(),
        code_path.read_text(),
        attempt_count,
        total_cost,
        model_name
    )