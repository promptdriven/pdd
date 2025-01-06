import os
import re
import shutil
import subprocess
from dataclasses import dataclass
from typing import Tuple, Optional
from rich import print as rprint

from .fix_errors_from_unit_tests import fix_errors_from_unit_tests

@dataclass
class IterationResult:
    fails: int
    errors: int
    iteration: int
    total_fails_and_errors: int

    def is_better_than(self, other: Optional['IterationResult']) -> bool:
        if other is None:
            return True
        if self.total_fails_and_errors < other.total_fails_and_errors:
            return True
        if self.total_fails_and_errors == other.total_fails_and_errors:
            return self.errors < other.errors  # Prioritize fewer errors
        return False

def extract_test_results(pytest_output: str) -> Tuple[int, int]:
    """Extract the number of fails and errors from pytest output.
    
    Args:
        pytest_output (str): The complete pytest output text
        
    Returns:
        Tuple[int, int]: Number of fails and errors respectively
    """
    fails = errors = 0
    
    # First try to match the summary line
    summary_match = re.search(r'=+ (\d+) failed[\,\s]', pytest_output)
    if summary_match:
        fails = int(summary_match.group(1))
    else:
        # Fallback to looking for any "X failed" pattern
        fail_match = re.search(r'(\d+)\s+failed', pytest_output)
        if fail_match:
            fails = int(fail_match.group(1))
    
    # Look for error patterns
    error_match = re.search(r'(\d+)\s+error', pytest_output)
    if error_match:
        errors = int(error_match.group(1))
        
    return fails, errors

def create_backup_files(unit_test_file: str, code_file: str, fails: int, 
                       errors: int, iteration: int) -> Tuple[str, str]:
    """Create backup files with iteration information in the filename."""
    unit_test_backup = f"{os.path.splitext(unit_test_file)[0]}_{fails}_{errors}_{iteration}.py"
    code_backup = f"{os.path.splitext(code_file)[0]}_{fails}_{errors}_{iteration}.py"
    
    shutil.copy2(unit_test_file, unit_test_backup)
    shutil.copy2(code_file, code_backup)
    
    return unit_test_backup, code_backup

def fix_error_loop(
    unit_test_file: str,
    code_file: str,
    prompt: str,
    verification_program: str,
    strength: float,
    temperature: float,
    max_attempts: int,
    budget: float,
    error_log_file: str = "error_log.txt",
    verbose: bool = False
) -> Tuple[bool, str, str, int, float, str]:
    """
    Attempt to fix errors in a unit test and its corresponding code file through multiple iterations.
    """
    # Input validation
    if not all([os.path.exists(f) for f in [unit_test_file, code_file, verification_program]]):
        raise FileNotFoundError("One or more input files do not exist")
    if not (0 <= strength <= 1 and 0 <= temperature <= 1):
        raise ValueError("Strength and temperature must be between 0 and 1")
    
    # Step 1: Remove existing error log file if it exists
    try:
        if os.path.exists(error_log_file):
            os.remove(error_log_file)
    except FileNotFoundError:
        pass  # File doesn't exist, which is fine
    
    # Step 2: Initialize variables
    attempt_count = 0
    total_cost = 0.0
    best_iteration: Optional[IterationResult] = None
    model_name = ""
    
    while attempt_count < max_attempts:
        rprint(f"[bold yellow]Attempt {attempt_count + 1}[/bold yellow]")
        
        # Increment attempt counter first
        attempt_count += 1
        
        # Step 3a: Run pytest
        with open(error_log_file, 'a') as f:
            result = subprocess.run(['python', '-m', 'pytest', '-vv', '--no-cov', unit_test_file],
                                 capture_output=True, text=True)
            f.write("\n****************************************************************************************************\n")
            f.write("\nAttempt " + str(attempt_count) + ":\n")
            f.write("\n****************************************************************************************************\n")
            f.write(result.stdout + result.stderr)
        
        # Extract test results
        fails, errors = extract_test_results(result.stdout)
        current_iteration = IterationResult(fails, errors, attempt_count, fails + errors)
        
        # Step 3b: Check if tests pass
        if fails == 0 and errors == 0:
            break
            
        # Step 3c: Handle test failures
        with open(error_log_file, 'r') as f:
            error_content = f.read()
        rprint(f"[bold red]Test output (attempt {attempt_count}):[/bold red]")
        rprint(error_content.replace('[', '\\[').replace(']', '\\]'))
        
        # Create backups
        backup_unit_test, backup_code = create_backup_files(
            unit_test_file, code_file, fails, errors, attempt_count
        )
        
        # Read current files
        with open(unit_test_file, 'r') as f:
            current_unit_test = f.read()
        with open(code_file, 'r') as f:
            current_code = f.read()
            
        # Try to fix errors
        update_unit_test, update_code, fixed_unit_test, fixed_code, iteration_cost, model_name = (
            fix_errors_from_unit_tests(
                current_unit_test, current_code, prompt, error_content,
                error_log_file, strength, temperature,
                verbose=verbose
            )
        )
        
        total_cost += iteration_cost
        if total_cost > budget:
            rprint("[bold red]Budget exceeded![/bold red]")
            break
            
        if not (update_unit_test or update_code):
            rprint("[bold yellow]No changes needed or possible.[/bold yellow]")
            break
            
        # Update files if needed
        if update_unit_test:
            with open(unit_test_file, 'w') as f:
                f.write(fixed_unit_test)

        if update_code:
            with open(code_file, 'w') as f:
                f.write(fixed_code)
                
            # Run verification
            rprint("[bold yellow]Running Verification.[/bold yellow]")
            verification_result = subprocess.run(['python', verification_program],
                                              capture_output=True, text=True)

            if verification_result.returncode != 0:
                rprint("[bold red]Verification failed! Restoring previous code.[/bold red]")
                shutil.copy2(backup_code, code_file)
                with open(error_log_file, 'a') as f:
                    f.write("****************************************************************************************************\n")
                    f.write("\nVerification program failed! Here is the output and errors from the verification program that was running the code under test:\n" + verification_result.stdout + verification_result.stderr)
                    f.write("****************************************************************************************************\n")
                    f.write(f"\nRestoring previous working code.\n")
                continue
                
        # Update best iteration if current is better
        if current_iteration.is_better_than(best_iteration):
            best_iteration = current_iteration
            
        # Check budget after increment
        if total_cost > budget:
            rprint("[bold red]Budget exceeded![/bold red]")
            break
            
    # Step 4: Final test run
    with open(error_log_file, 'a') as f:
        final_result = subprocess.run(['python', '-m', 'pytest', '-vv', unit_test_file],
                                    capture_output=True, text=True)
        f.write("\nFinal test run:\n" + final_result.stdout + final_result.stderr)
    rprint("[bold]Final test output:[/bold]")
    rprint(final_result.stdout.replace('[', '\\[').replace(']', '\\]'))
    
    # Step 5: Restore best iteration if needed
    final_fails, final_errors = extract_test_results(final_result.stdout)
    if best_iteration and (final_fails + final_errors) > best_iteration.total_fails_and_errors:
        rprint(f"[bold yellow]Restoring best iteration: {best_iteration.iteration} [/bold yellow]")
        best_unit_test = f"{os.path.splitext(unit_test_file)[0]}_{best_iteration.fails}_{best_iteration.errors}_{best_iteration.iteration}.py"
        best_code = f"{os.path.splitext(code_file)[0]}_{best_iteration.fails}_{best_iteration.errors}_{best_iteration.iteration}.py"
        shutil.copy2(best_unit_test, unit_test_file)
        shutil.copy2(best_code, code_file)
    
    # Step 6: Return results
    with open(unit_test_file, 'r') as f:
        final_unit_test = f.read()
    with open(code_file, 'r') as f:
        final_code = f.read()
        
    success = final_fails == 0 and final_errors == 0
    
    return success, final_unit_test, final_code, attempt_count, total_cost, model_name