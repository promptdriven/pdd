#!/usr/bin/env python3
import os
import sys
import subprocess
import shutil
import json
from datetime import datetime
from pathlib import Path

from rich import print as rprint
from rich.console import Console

# Relative import from an internal module.
from .get_language import get_language
from .fix_errors_from_unit_tests import fix_errors_from_unit_tests
from . import DEFAULT_TIME  # Import DEFAULT_TIME
from .python_env_detector import detect_host_python_executable
from .agentic_fix import run_agentic_fix
from .agentic_langtest import default_verify_cmd_for


console = Console()

def escape_brackets(text: str) -> str:
    """Escape square brackets so Rich doesn't misinterpret them."""
    return text.replace("[", "\\[").replace("]", "\\]")

# ---------- Normalize any agentic return shape to a 4-tuple ----------
def _normalize_agentic_result(result):
    """
    Normalize run_agentic_fix result into: (success: bool, msg: str, cost: float, model: str, changed_files: List[str])
    Handles older 2/3/4-tuple shapes used by tests/monkeypatches.
    """
    if isinstance(result, tuple):
        if len(result) == 5:
            ok, msg, cost, model, changed_files = result
            return bool(ok), str(msg), float(cost), str(model or "agentic-cli"), list(changed_files or [])
        if len(result) == 4:
            ok, msg, cost, model = result
            return bool(ok), str(msg), float(cost), str(model or "agentic-cli"), []
        if len(result) == 3:
            ok, msg, cost = result
            return bool(ok), str(msg), float(cost), "agentic-cli", []
        if len(result) == 2:
            ok, msg = result
            return bool(ok), str(msg), 0.0, "agentic-cli", []
    # Fallback (shouldn't happen)
    return False, "Invalid agentic result shape", 0.0, "agentic-cli", []

def _safe_run_agentic_fix(*, prompt_file, code_file, unit_test_file, error_log_file, cwd=None):
    """
    Call (possibly monkeypatched) run_agentic_fix and normalize its return.
    """
    res = run_agentic_fix(
        prompt_file=prompt_file,
        code_file=code_file,
        unit_test_file=unit_test_file,
        error_log_file=error_log_file,
        cwd=cwd,
    )
    return _normalize_agentic_result(res)
# ---------------------------------------------------------------------


def run_pytest_on_file(test_file: str) -> tuple[int, int, int, str]:
    """
    Run pytest on the specified test file using the subprocess-based runner.
    Returns a tuple: (failures, errors, warnings, logs)
    """
    from .pytest_output import run_pytest_and_capture_output
    # Use the subprocess-based runner to avoid module caching issues
    output_data = run_pytest_and_capture_output(test_file)
    
    # Extract results
    results = output_data.get("test_results", [{}])[0]
    
    failures = results.get("failures", 0)
    errors = results.get("errors", 0)
    warnings = results.get("warnings", 0)
    
    # Combine stdout/stderr for the log
    logs = (results.get("standard_output", "") or "") + "\n" + (results.get("standard_error", "") or "")
    
    return failures, errors, warnings, logs

def format_log_for_output(log_structure):
    """
    Format the structured log into a human-readable text format with XML tags.
    """
    formatted_text = ""
    
    # Initial test output (only for first iteration)
    if log_structure["iterations"] and "initial_test_output" in log_structure["iterations"][0]:
        formatted_text += "<pytest_output iteration=1>\n"
        formatted_text += f"{log_structure['iterations'][0]['initial_test_output']}\n"
        formatted_text += "</pytest_output>\n\n"
    
    for i, iteration in enumerate(log_structure["iterations"]):
        formatted_text += f"=== Attempt iteration {iteration['number']} ===\n\n"
        
        # Fix attempt with XML tags
        if iteration.get("fix_attempt"):
            formatted_text += f"<fix_attempt iteration={iteration['number']}>\n"
            if iteration.get("model_name"):
                formatted_text += f"Model: {iteration['model_name']}\n"
            formatted_text += f"{iteration['fix_attempt']}\n"
            formatted_text += "</fix_attempt>\n\n"
        
        # Verification with XML tags
        if iteration.get("verification"):
            formatted_text += f"<verification_output iteration={iteration['number']}>\n"
            formatted_text += f"{iteration['verification']}\n"
            formatted_text += "</verification_output>\n\n"
        
        # Post-fix test results (except for last iteration to avoid duplication)
        if i < len(log_structure["iterations"]) - 1 and iteration.get("post_test_output"):
            formatted_text += f"<pytest_output iteration={iteration['number']+1}>\n"
            formatted_text += f"{iteration['post_test_output']}\n"
            formatted_text += "</pytest_output>\n\n"
    
    # Final run (using last iteration's post-test output)
    if log_structure["iterations"] and log_structure["iterations"][-1].get("post_test_output"):
        formatted_text += "=== Final Pytest Run ===\n"
        formatted_text += f"{log_structure['iterations'][-1]['post_test_output']}\n"
    
    return formatted_text

def fix_error_loop(unit_test_file: str,
                   code_file: str,
                   prompt_file: str,
                   prompt: str,
                   verification_program: str,
                   strength: float,
                   temperature: float,
                   max_attempts: int,
                   budget: float,
                   error_log_file: str = "error_log.txt",
                   verbose: bool = False,
                   time: float = DEFAULT_TIME,
                   agentic_fallback: bool = True):
    """
    Attempt to fix errors in a unit test and corresponding code using repeated iterations, 
    counting only the number of times we actually call the LLM fix function. 
    The tests are re-run in the same iteration after a fix to see if we've succeeded,
    so that 'attempts' matches the number of fix attempts (not the total test runs).

    This updated version uses structured logging to avoid redundant entries.

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
        time: Time parameter for the fix_errors_from_unit_tests call.
        agentic_fallback: Whether to trigger cli agentic fallback when fix fails.
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

    # Initialize structured log
    log_structure = {
        "iterations": []
    }

    # We use fix_attempts to track how many times we actually call the LLM:
    fix_attempts = 0
    total_cost = 0.0
    model_name = ""
    # Initialize these variables now
    final_unit_test = ""
    final_code = ""
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
    # Run an initial test to determine starting state
    try:
        is_python = str(code_file).lower().endswith(".py")
        if is_python:
            initial_fails, initial_errors, initial_warnings, pytest_output = run_pytest_on_file(unit_test_file)
        else:
            # For non-Python files, run the verification program to get an initial error state
            rprint(f"[cyan]Non-Python target detected. Running verification program to get initial state...[/cyan]")
            lang = get_language(os.path.splitext(code_file)[1])
            verify_cmd = default_verify_cmd_for(lang, unit_test_file)
            if not verify_cmd:
                # No verify command available (e.g., Java without maven/gradle).
                # Trigger agentic fallback directly.
                rprint(f"[cyan]No verification command for {lang}. Triggering agentic fallback directly...[/cyan]")
                error_log_path = Path(error_log_file)
                error_log_path.parent.mkdir(parents=True, exist_ok=True)
                if not error_log_path.exists() or error_log_path.stat().st_size == 0:
                    with open(error_log_path, "w") as f:
                        f.write(f"No verification command available for language: {lang}\n")
                        f.write("Agentic fix will attempt to resolve the issue.\n")

                rprint(f"[cyan]Attempting agentic fix fallback (prompt_file={prompt_file!r})...[/cyan]")
                success, agent_msg, agent_cost, agent_model, agent_changed_files = _safe_run_agentic_fix(
                    prompt_file=prompt_file,
                    code_file=code_file,
                    unit_test_file=unit_test_file,
                    error_log_file=error_log_file,
                    cwd=Path(prompt_file).parent if prompt_file else None,
                )
                if not success:
                    rprint(f"[bold red]Agentic fix fallback failed: {agent_msg}[/bold red]")
                if agent_changed_files:
                    rprint(f"[cyan]Agent modified {len(agent_changed_files)} file(s):[/cyan]")
                    for f in agent_changed_files:
                        rprint(f"  • {f}")
                final_unit_test = ""
                final_code = ""
                try:
                    with open(unit_test_file, "r") as f:
                        final_unit_test = f.read()
                except Exception:
                    pass
                try:
                    with open(code_file, "r") as f:
                        final_code = f.read()
                except Exception:
                    pass
                return success, final_unit_test, final_code, 1, agent_cost, agent_model

            verify_result = subprocess.run(verify_cmd, capture_output=True, text=True, shell=True, stdin=subprocess.DEVNULL)
            pytest_output = (verify_result.stdout or "") + "\n" + (verify_result.stderr or "")
            if verify_result.returncode == 0:
                initial_fails, initial_errors, initial_warnings = 0, 0, 0
            else:
                initial_fails, initial_errors, initial_warnings = 1, 0, 0 # Treat any failure as one "fail"

        # Store initial state for statistics
        stats = {
            "initial_fails": initial_fails,
            "initial_errors": initial_errors, 
            "initial_warnings": initial_warnings,
            "final_fails": 0,  # Initialize to 0
            "final_errors": 0,  # Initialize to 0
            "final_warnings": 0,  # Initialize to 0
            "best_iteration": None,
            "iterations_info": []
        }
    except Exception as e:
        rprint(f"[red]Error running initial test/verification:[/red] {e}")
        return False, "", "", fix_attempts, total_cost, model_name

    # If target is not a Python file, trigger agentic fallback if tests fail
    if not is_python:
        if initial_fails > 0 or initial_errors > 0:
            rprint("[cyan]Non-Python target failed initial verification. Triggering agentic fallback...[/cyan]")
            error_log_path = Path(error_log_file)
            error_log_path.parent.mkdir(parents=True, exist_ok=True)
            with open(error_log_path, "w") as f:
                f.write(pytest_output)
            
            rprint(f"[cyan]Attempting agentic fix fallback (prompt_file={prompt_file!r})...[/cyan]")
            success, agent_msg, agent_cost, agent_model, agent_changed_files = _safe_run_agentic_fix(
                prompt_file=prompt_file,
                code_file=code_file,
                unit_test_file=unit_test_file,
                error_log_file=error_log_file,
                cwd=Path(prompt_file).parent if prompt_file else None,
            )
            if not success:
                rprint(f"[bold red]Agentic fix fallback failed: {agent_msg}[/bold red]")
            if agent_changed_files:
                rprint(f"[cyan]Agent modified {len(agent_changed_files)} file(s):[/cyan]")
                for f in agent_changed_files:
                    rprint(f"  • {f}")
            final_unit_test = ""
            final_code = ""
            try:
                with open(unit_test_file, "r") as f:
                    final_unit_test = f.read()
            except Exception:
                pass
            try:
                with open(code_file, "r") as f:
                    final_code = f.read()
            except Exception:
                pass
            return success, final_unit_test, final_code, 1, agent_cost, agent_model
        else:
            # Non-python tests passed, so we are successful.
            rprint("[green]Non-Python tests passed. No fix needed.[/green]")
            try:
                with open(unit_test_file, "r") as f:
                    final_unit_test = f.read()
                with open(code_file, "r") as f:
                    final_code = f.read()
            except Exception as e:
                rprint(f"[yellow]Warning: Could not read final files: {e}[/yellow]")
            return True, final_unit_test, final_code, 0, 0.0, "N/A"

    fails, errors, warnings = initial_fails, initial_errors, initial_warnings
    
    # Determine success state immediately
    success = (fails == 0 and errors == 0 and warnings == 0)

    # Track if tests were initially passing
    initially_passing = success

    while fix_attempts < max_attempts and total_cost < budget:
        iteration += 1

        # Add this iteration to the structured log
        if iteration == 1:
            # For first iteration, include the initial test output
            iteration_data = {
                "number": iteration,
                "initial_test_output": pytest_output,
                "fix_attempt": None,
                "verification": None,
                "post_test_output": None
            }
        else:
            # For subsequent iterations, don't duplicate test output
            iteration_data = {
                "number": iteration,
                "fix_attempt": None,
                "verification": None,
                "post_test_output": None
            }
        log_structure["iterations"].append(iteration_data)
            
        # If tests pass initially, no need to fix anything
        if success:
            rprint("[green]All tests already pass with no warnings! No fixes needed on this iteration.[/green]")
            stats["final_fails"] = 0  # Explicitly set to 0
            stats["final_errors"] = 0  # Explicitly set to 0
            stats["final_warnings"] = 0  # Explicitly set to 0
            stats["best_iteration"] = 0
            
            # Update structured log
            log_structure["iterations"][-1]["post_test_output"] = pytest_output

            # Write formatted log to file
            error_log_path = Path(error_log_file)
            error_log_path.parent.mkdir(parents=True, exist_ok=True)
            with open(error_log_path, "w") as elog:
                elog.write(format_log_for_output(log_structure))
            
            # Set success to True (already determined)
            # Read the actual fixed files to return the successful state
            try:
                with open(unit_test_file, "r") as f:
                    final_unit_test = f.read()
                with open(code_file, "r") as f:  
                    final_code = f.read()
            except Exception as e:
                rprint(f"[yellow]Warning: Could not read fixed files: {e}[/yellow]")
                # Keep empty strings as fallback
            break
        
        iteration_header = f"=== Attempt iteration {iteration} ==="
        rprint(f"[bold blue]{iteration_header}[/bold blue]")
        
        # Print to console (escaped):
        rprint(f"[magenta]Pytest output:[/magenta]\n{escape_brackets(pytest_output)}")
        if verbose:
            rprint(f"[cyan]Iteration summary: {fails} failed, {errors} errors, {warnings} warnings[/cyan]")

        # Track this iteration's stats
        iteration_stats = {
            "iteration": iteration,
            "fails": fails,
            "errors": errors,
            "warnings": warnings
        }
        stats["iterations_info"].append(iteration_stats)

        # If tests are fully successful, we break out:
        if fails == 0 and errors == 0 and warnings == 0:
            rprint("[green]All tests passed with no warnings! Exiting loop.[/green]")
            success = True  # Set success flag
            stats["final_fails"] = 0  # Explicitly set to 0
            stats["final_errors"] = 0  # Explicitly set to 0
            stats["final_warnings"] = 0  # Explicitly set to 0
            break

        # We only attempt to fix if test is failing or has warnings:
        # Let's create backups in .pdd/backups/ to avoid polluting code/test directories
        code_name = os.path.basename(code_file)
        code_basename = os.path.splitext(code_name)[0]
        unit_test_name = os.path.basename(unit_test_file)
        unit_test_ext = os.path.splitext(unit_test_name)[1]
        code_ext = os.path.splitext(code_name)[1]

        backup_dir = Path.cwd() / '.pdd' / 'backups' / code_basename / timestamp
        backup_dir.mkdir(parents=True, exist_ok=True)

        unit_test_backup = str(backup_dir / f"test_{iteration}_{errors}_{fails}_{warnings}{unit_test_ext}")
        code_backup = str(backup_dir / f"code_{iteration}_{errors}_{fails}_{warnings}{code_ext}")
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
            # Format the log for the LLM
            formatted_log = format_log_for_output(log_structure)

            updated_unit_test, updated_code, fixed_unit_test, fixed_code, analysis, cost, model_name = fix_errors_from_unit_tests(
                unit_test_contents,
                code_contents,
                prompt,
                formatted_log,  # Use formatted log instead of reading the file
                error_log_file,
                strength,
                temperature,
                verbose=verbose,
                time=time  # Pass time parameter
            )
            
            # Update the fix attempt in the structured log
            log_structure["iterations"][-1]["fix_attempt"] = analysis
            log_structure["iterations"][-1]["model_name"] = model_name
        except Exception as e:
            rprint(f"[red]Error during fix_errors_from_unit_tests call:[/red] {e}")
            break

        fix_attempts += 1  # We used one fix attempt
        total_cost += cost
        if verbose:
            rprint(f"[cyan]Iteration {iteration} Fix Cost: ${cost:.6f}, Cumulative Total Cost: ${total_cost:.6f}[/cyan]")
        if total_cost > budget:
            rprint(f"[red]Exceeded the budget of ${budget:.6f}. Ending fixing loop.[/red]")
            break

        # Update unit test file if needed.
        if updated_unit_test:
            try:
                # Ensure we have valid content even if the returned fixed_unit_test is empty
                content_to_write = fixed_unit_test if fixed_unit_test else unit_test_contents
                with open(unit_test_file, "w") as f:
                    f.write(content_to_write)
                if verbose:
                    rprint("[green]Unit test file updated.[/green]")
            except Exception as e:
                rprint(f"[red]Error writing updated unit test:[/red] {e}")
                break

        # Update code file and run verification if needed.
        if updated_code:
            try:
                # Ensure we have valid content even if the returned fixed_code is empty
                content_to_write = fixed_code if fixed_code else code_contents
                with open(code_file, "w") as f:
                    f.write(content_to_write)
                if verbose:
                    rprint("[green]Code file updated.[/green]")
            except Exception as e:
                rprint(f"[red]Error writing updated code file:[/red] {e}")
                break

            # Run the verification:
            try:
                verify_cmd = [detect_host_python_executable(), verification_program]
                verify_result = subprocess.run(verify_cmd, capture_output=True, text=True, stdin=subprocess.DEVNULL)
                # Safely handle None for stdout or stderr:
                verify_stdout = verify_result.stdout or ""
                verify_stderr = verify_result.stderr or ""
                verify_output = verify_stdout + "\n" + verify_stderr
                
                # Update verification in structured log
                log_structure["iterations"][-1]["verification"] = verify_output
            except Exception as e:
                rprint(f"[red]Error running verification program:[/red] {e}")
                verify_output = f"Verification program error: {e}"
                log_structure["iterations"][-1]["verification"] = verify_output

            rprint(f"[blue]Verification program output:[/blue]\n{escape_brackets(verify_output)}")

            if verify_result.returncode != 0:
                rprint("[red]Verification failed. Restoring last working code file from backup.[/red]")
                try:
                    shutil.copy(code_backup, code_file)
                    log_structure["iterations"][-1]["verification"] += f"\nRestored code file from backup: {code_backup}, because verification program failed to run."
                except Exception as e:
                    rprint(f"[red]Error restoring backup code file:[/red] {e}")
                    break

        # Run pytest for the next iteration
        try:
            fails, errors, warnings, pytest_output = run_pytest_on_file(unit_test_file)
            
            # Update post-test output in structured log
            log_structure["iterations"][-1]["post_test_output"] = pytest_output

            # Write updated structured log to file after each iteration
            error_log_path = Path(error_log_file)
            error_log_path.parent.mkdir(parents=True, exist_ok=True)
            with open(error_log_path, "w") as elog:
                elog.write(format_log_for_output(log_structure))
            
            # Update iteration stats with post-fix results
            stats["iterations_info"][-1].update({
                "post_fix_fails": fails,
                "post_fix_errors": errors,
                "post_fix_warnings": warnings,
                "improved": (fails < iteration_stats["fails"] or 
                            errors < iteration_stats["errors"] or 
                            warnings < iteration_stats["warnings"])
            })
            
            # Update success status based on latest results
            success = (fails == 0 and errors == 0 and warnings == 0)
            
            # Update final stats
            stats["final_fails"] = fails
            stats["final_errors"] = errors
            stats["final_warnings"] = warnings
        except Exception as e:
            rprint(f"[red]Error running pytest for next iteration:[/red] {e}")
            return False, "", "", fix_attempts, total_cost, model_name

    # Possibly restore best iteration if the final run is not as good:
    if best_iteration_info["attempt"] is not None and not success:
        is_better_final = False
        if stats["final_errors"] < best_iteration_info["errors"]:
            is_better_final = True
        elif stats["final_errors"] == best_iteration_info["errors"] and stats["final_fails"] < best_iteration_info["fails"]:
            is_better_final = True
        elif (stats["final_errors"] == best_iteration_info["errors"] and 
              stats["final_fails"] == best_iteration_info["fails"] and 
              stats["final_warnings"] < best_iteration_info["warnings"]):
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
                
                # Update final stats with best iteration stats
                stats["final_fails"] = best_iteration_info["fails"]
                stats["final_errors"] = best_iteration_info["errors"]
                stats["final_warnings"] = best_iteration_info["warnings"]
                stats["best_iteration"] = best_iteration_info["attempt"]
                
                # Check if the best iteration had passing tests
                success = (best_iteration_info["fails"] == 0 and 
                          best_iteration_info["errors"] == 0 and 
                          best_iteration_info["warnings"] == 0)
            except Exception as e:
                rprint(f"[red]Error restoring best iteration backups:[/red] {e}")
        else:
            # Current iteration is the best
            stats["best_iteration"] = "final"
    else:
        stats["best_iteration"] = "final"

    # Read final file contents for non-initially-passing tests
    # (Initially passing tests have files read at lines 344-348)
    try:
        if not initially_passing:
            with open(unit_test_file, "r") as f:
                final_unit_test = f.read()
            with open(code_file, "r") as f:
                final_code = f.read()
    except Exception as e:
        rprint(f"[red]Error reading final files:[/red] {e}")
        final_unit_test, final_code = "", ""

    # Print summary statistics
    rprint("\n[bold cyan]Summary Statistics:[/bold cyan]")
    rprint(f"Initial state: {initial_fails} fails, {initial_errors} errors, {initial_warnings} warnings")
    rprint(f"Final state: {stats['final_fails']} fails, {stats['final_errors']} errors, {stats['final_warnings']} warnings")
    rprint(f"Best iteration: {stats['best_iteration']}")
    rprint(f"Success: {success}")
    
    # Calculate improvements
    stats["improvement"] = {
        "fails_reduced": initial_fails - stats['final_fails'],
        "errors_reduced": initial_errors - stats['final_errors'],
        "warnings_reduced": initial_warnings - stats['final_warnings'],
        "percent_improvement": 100 if (initial_fails + initial_errors + initial_warnings) == 0 else 
                              (1 - (stats['final_fails'] + stats['final_errors'] + stats['final_warnings']) / 
                                   (initial_fails + initial_errors + initial_warnings)) * 100
    }
    
    rprint(f"Improvement: {stats['improvement']['fails_reduced']} fails, {stats['improvement']['errors_reduced']} errors, {stats['improvement']['warnings_reduced']} warnings")
    rprint(f"Overall improvement: {stats['improvement']['percent_improvement']:.2f}%")

    # Agentic fallback at end adds cost & model (normalized)
    if not success and agentic_fallback and total_cost < budget:
        # Ensure error_log_file exists before calling agentic fix
        # Write the current log structure if it hasn't been written yet
        try:
            if not os.path.exists(error_log_file) or os.path.getsize(error_log_file) == 0:
                error_log_path = Path(error_log_file)
                error_log_path.parent.mkdir(parents=True, exist_ok=True)
                with open(error_log_path, "w") as elog:
                    if log_structure["iterations"]:
                        elog.write(format_log_for_output(log_structure))
                    else:
                        # No iterations ran, write initial state info
                        elog.write(f"Initial state: {initial_fails} fails, {initial_errors} errors, {initial_warnings} warnings\n")
                        if 'pytest_output' in locals():
                            elog.write(f"\n<pytest_output>\n{pytest_output}\n</pytest_output>\n")
        except Exception as e:
            rprint(f"[yellow]Warning: Could not write error log before agentic fallback: {e}[/yellow]")

        rprint(f"[cyan]Attempting agentic fix fallback (prompt_file={prompt_file!r})...[/cyan]")
        agent_success, agent_msg, agent_cost, agent_model, agent_changed_files = _safe_run_agentic_fix(
            prompt_file=prompt_file,
            code_file=code_file,
            unit_test_file=unit_test_file,
            error_log_file=error_log_file,
            cwd=Path(prompt_file).parent if prompt_file else None,
        )
        total_cost += agent_cost
        if not agent_success:
            rprint(f"[bold red]Agentic fix fallback failed: {agent_msg}[/bold red]")
        if agent_changed_files:
            rprint(f"[cyan]Agent modified {len(agent_changed_files)} file(s):[/cyan]")
            for f in agent_changed_files:
                rprint(f"  • {f}")
        if agent_success:
            model_name = agent_model or model_name
            try:
                with open(unit_test_file, "r") as f:
                    final_unit_test = f.read()
                with open(code_file, "r") as f:
                    final_code = f.read()
            except Exception as e:
                rprint(f"[yellow]Warning: Could not read files after successful agentic fix: {e}[/yellow]")
            success = True

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

    rprint("\n[bold]Process complete.[/bold]")
    rprint(f"Success: {success}")
    rprint(f"Attempts: {attempts}")
    rprint(f"Total cost: ${total_cost:.6f}")
    rprint(f"Model used: {model_name}")
    rprint(f"Final unit test contents:\n{final_unit_test}")
