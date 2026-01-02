from __future__ import annotations
import os
import shutil
import subprocess
import sys
import threading
from pathlib import Path
from typing import Tuple, Optional, Union, List

# Try to import DEFAULT_TIME, with fallback
try:
    from . import DEFAULT_TIME
except ImportError:
    DEFAULT_TIME = 0.5

# Try to import agentic modules, with fallbacks
try:
    from .agentic_crash import run_agentic_crash
except ImportError:
    def run_agentic_crash(**kwargs):
        return (False, "Agentic crash handler not available", 0.0, "N/A", [])

try:
    from .get_language import get_language
except ImportError:
    def get_language(ext):
        return "unknown"

try:
    from .agentic_langtest import default_verify_cmd_for
except ImportError:
    def default_verify_cmd_for(lang, verification_program):
        return None

def _normalize_agentic_result(result):
    """
    Normalize run_agentic_crash result into: (success: bool, msg: str, cost: float, model: str, changed_files: List[str])
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

def _safe_run_agentic_crash(*, prompt_file, code_file, program_file, crash_log_file, cwd=None):
    """
    Call (possibly monkeypatched) run_agentic_crash and normalize its return.
    Maps arguments to the expected signature of run_agentic_crash.

    Note: cwd parameter is accepted for compatibility but not passed to run_agentic_crash
    as it determines the working directory from prompt_file.parent internally.
    """
    if not prompt_file:
        return False, "Agentic fix requires a valid prompt file.", 0.0, "agentic-cli", []

    try:
        # Ensure inputs are Path objects as expected by run_agentic_crash
        call_args = {
            "prompt_file": Path(prompt_file),
            "code_file": Path(code_file),
            "program_file": Path(program_file),
            "crash_log_file": Path(crash_log_file),
            "verbose": True,
            "quiet": False,
        }
        # Note: cwd is not passed - run_agentic_crash uses prompt_file.parent as project root

        res = run_agentic_crash(**call_args)
        return _normalize_agentic_result(res)
    except Exception as e:
        return False, f"Agentic crash handler failed: {e}", 0.0, "agentic-cli", []

# Use Rich for pretty printing to the console
try:
    from rich.console import Console
    console = Console(record=True)
    rprint = console.print
except ImportError:
    # Fallback if Rich is not available
    def rprint(*args, **kwargs):
        print(*args)

# Use relative import for internal modules
try:
    from .fix_code_module_errors import fix_code_module_errors
except ImportError:
    try:
        from fix_code_module_errors import fix_code_module_errors
    except ImportError:
        # Provide a stub that will fail gracefully
        def fix_code_module_errors(**kwargs):
            return (False, False, "", "", "Module not available", 0.0, None)


class ProcessResult:
    def __init__(self, returncode, stdout, stderr):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr

def run_process_with_output(cmd_args, timeout=300):
    """
    Runs a process, streaming stdout/stderr to the console while capturing them.
    Allows interaction via stdin.

    Uses start_new_session=True to create a new process group, allowing us to
    kill all child processes if the main process times out.
    """
    import os
    import signal

    try:
        proc = subprocess.Popen(
            cmd_args,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
            start_new_session=True  # Create new process group for clean termination
        )
    except Exception as e:
        return -1, "", str(e)

    captured_stdout = []
    captured_stderr = []

    def stream_pipe(pipe, sink, capture_list):
        while True:
            try:
                chunk = pipe.read(1)
                if not chunk:
                    break
                capture_list.append(chunk)
            except (ValueError, IOError, OSError):
                # OSError can occur when pipe is closed during read
                break

    t_out = threading.Thread(target=stream_pipe, args=(proc.stdout, sys.stdout, captured_stdout), daemon=True)
    t_err = threading.Thread(target=stream_pipe, args=(proc.stderr, sys.stderr, captured_stderr), daemon=True)

    t_out.start()
    t_err.start()

    timed_out = False
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        captured_stderr.append(b"\n[Timeout]\n")

    # Kill process and entire process group if needed
    if timed_out or proc.returncode is None:
        try:
            # Kill entire process group to handle forked children
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except (ProcessLookupError, OSError):
            # Process group may already be dead
            pass
        try:
            proc.kill()
            proc.wait(timeout=5)
        except Exception:
            pass

    # Close pipes to unblock reader threads
    try:
        proc.stdout.close()
    except Exception:
        pass
    try:
        proc.stderr.close()
    except Exception:
        pass

    # Wait for threads with timeout to prevent indefinite hangs
    THREAD_JOIN_TIMEOUT = 5  # seconds
    t_out.join(timeout=THREAD_JOIN_TIMEOUT)
    t_err.join(timeout=THREAD_JOIN_TIMEOUT)

    # If threads are still alive after timeout, log it (they're daemon threads so won't block exit)
    if t_out.is_alive() or t_err.is_alive():
        captured_stderr.append(b"\n[Thread join timeout - some output may be lost]\n")

    stdout_str = b"".join(captured_stdout).decode('utf-8', errors='replace')
    stderr_str = b"".join(captured_stderr).decode('utf-8', errors='replace')

    return proc.returncode if proc.returncode is not None else -1, stdout_str, stderr_str


def fix_code_loop(
    code_file: str,
    prompt: str,
    verification_program: str,
    strength: float,
    temperature: float,
    max_attempts: int,
    budget: float,
    error_log_file: str,
    verbose: bool = False,
    time: float = DEFAULT_TIME,
    prompt_file: str = "",
    agentic_fallback: bool = True,
) -> Tuple[bool, str, str, int, float, Optional[str]]:
    """
    Attempts to fix errors in a code module through multiple iterations.

    Args:
        code_file: Path to the code file being tested.
        prompt: The prompt that generated the code under test.
        verification_program: Path to the Python program that verifies the code.
        strength: LLM model strength (0.0 to 1.0).
        temperature: LLM temperature (0.0 to 1.0).
        max_attempts: Maximum number of fix attempts.
        budget: Maximum cost allowed for the fixing process.
        error_log_file: Path to the error log file.
        verbose: Enable detailed logging (default: False).
        time: Time limit for the LLM calls (default: DEFAULT_TIME).
        prompt_file: Path to the prompt file.
        agentic_fallback: Enable agentic fallback if the primary fix mechanism fails.

    Returns:
        Tuple containing the following in order:
        - success (bool): Whether the errors were successfully fixed.
        - final_program (str): Contents of the final verification program file (empty string if unsuccessful).
        - final_code (str): Contents of the final code file (empty string if unsuccessful).
        - total_attempts (int): Number of fix attempts made.
        - total_cost (float): Total cost of all fix attempts.
        - model_name (str | None): Name of the LLM model used (or None if no LLM calls were made).
    """
    # Handle default time if passed as None (though signature defaults to DEFAULT_TIME)
    if time is None:
        time = DEFAULT_TIME
    
    # --- Start: File Checks ---
    if not Path(code_file).is_file():
        raise FileNotFoundError(f"Code file not found: {code_file}")
    if not Path(verification_program).is_file():
        rprint(f"[bold red]Error: Verification program not found: {verification_program}[/bold red]")
        return False, "", "", 0, 0.0, None
    # --- End: File Checks ---

    is_python = str(code_file).lower().endswith(".py")
    if not is_python:
        # For non-Python files, run the verification program to get an initial error state
        rprint(f"[cyan]Non-Python target detected. Running verification program to get initial state...[/cyan]")
        lang = get_language(os.path.splitext(code_file)[1])
        verify_cmd = default_verify_cmd_for(lang, verification_program)
        if not verify_cmd:
            # No verify command available (e.g., Java without maven/gradle).
            # Trigger agentic fallback directly using any existing error log.
            rprint(f"[cyan]No verification command for {lang}. Triggering agentic fallback directly...[/cyan]")
            error_log_path = Path(error_log_file)
            error_log_path.parent.mkdir(parents=True, exist_ok=True)
            # Read existing error content or create minimal log
            if not error_log_path.exists() or error_log_path.stat().st_size == 0:
                with open(error_log_path, "w") as f:
                    f.write(f"No verification command available for language: {lang}\n")
                    f.write("Agentic fix will attempt to resolve the issue.\n")

            success, _msg, agent_cost, agent_model, agent_changed_files = _safe_run_agentic_crash(
                prompt_file=prompt_file,
                code_file=code_file,
                program_file=verification_program,
                crash_log_file=error_log_file,
                cwd=Path(prompt_file).parent if prompt_file else None
            )
            final_program = ""
            final_code = ""
            try:
                with open(verification_program, "r") as f:
                    final_program = f.read()
            except Exception:
                pass
            try:
                with open(code_file, "r") as f:
                    final_code = f.read()
            except Exception:
                pass
            return success, final_program, final_code, 1, agent_cost, agent_model
        
        verify_result = subprocess.run(verify_cmd, capture_output=True, text=True, shell=True)
        pytest_output = (verify_result.stdout or "") + "\n" + (verify_result.stderr or "")
        if verify_result.returncode != 0:
            rprint("[cyan]Non-Python target failed initial verification. Triggering agentic fallback...[/cyan]")
            error_log_path = Path(error_log_file)
            error_log_path.parent.mkdir(parents=True, exist_ok=True)
            with open(error_log_path, "w") as f:
                f.write(pytest_output)
            
            success, _msg, agent_cost, agent_model, agent_changed_files = _safe_run_agentic_crash(
                prompt_file=prompt_file,
                code_file=code_file,
                program_file=verification_program,
                crash_log_file=error_log_file,
                cwd=Path(prompt_file).parent if prompt_file else None
            )
            final_program = ""
            final_code = ""
            try:
                with open(verification_program, "r") as f:
                    final_program = f.read()
            except Exception:
                pass
            try:
                with open(code_file, "r") as f:
                    final_code = f.read()
            except Exception:
                pass
            return success, final_program, final_code, 1, agent_cost, agent_model
        else:
            rprint("[green]Non-Python tests passed. No fix needed.[/green]")
            try:
                final_program = ""
                final_code = ""
                with open(verification_program, "r") as f:
                    final_program = f.read()
                with open(code_file, "r") as f:
                    final_code = f.read()
            except Exception as e:
                rprint(f"[yellow]Warning: Could not read final files: {e}[/yellow]")
            return True, final_program, final_code, 0, 0.0, "N/A"

    # Step 1: Remove existing error log file
    try:
        os.remove(error_log_file)
        if verbose:
            rprint(f"Removed existing error log file: {error_log_file}")
    except FileNotFoundError:
        if verbose:
            rprint(f"Error log file not found, no need to remove: {error_log_file}")
    except OSError as e:
        rprint(f"[bold red]Error removing log file {error_log_file}: {e}[/bold red]")

    # Step 2: Initialize variables
    attempts = 0
    total_cost = 0.0
    success = False
    model_name = None
    history_log = "<history>\n"

    # Create initial backups before any modifications
    # Store in .pdd/backups/ to avoid polluting code/test directories
    from datetime import datetime
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    code_file_path = Path(code_file)
    verification_program_path = Path(verification_program)

    backup_dir = Path.cwd() / '.pdd' / 'backups' / code_file_path.stem / timestamp
    backup_dir.mkdir(parents=True, exist_ok=True)

    original_code_backup = str(backup_dir / f"code_original{code_file_path.suffix}")
    original_program_backup = str(backup_dir / f"program_original{verification_program_path.suffix}")

    try:
        shutil.copy2(code_file, original_code_backup)
        shutil.copy2(verification_program, original_program_backup)
        if verbose:
            rprint(f"Created initial backups: {original_code_backup}, {original_program_backup}")
    except Exception as e:
        rprint(f"[bold red]Error creating initial backups: {e}[/bold red]")
        return False, "", "", 0, 0.0, None

    # Initialize process for scope
    process = None

    # Step 3: Enter the fixing loop
    while attempts < max_attempts and total_cost <= budget:
        # current_attempt is used for logging the current iteration number
        current_iteration_number = attempts + 1
        rprint(f"\n[bold cyan]Attempt {current_iteration_number}/{max_attempts}...[/bold cyan]")
        attempt_log_entry = f'  <attempt number="{current_iteration_number}">\n'

        # b. Run the verification program
        if verbose:
            rprint(f"Running verification: {sys.executable} {verification_program}")

        try:
            returncode, stdout, stderr = run_process_with_output(
                [sys.executable, verification_program],
                timeout=300
            )
            process = ProcessResult(returncode, stdout, stderr)

            verification_status = f"Success (Return Code: {process.returncode})" if process.returncode == 0 else f"Failure (Return Code: {process.returncode})"
            verification_output = process.stdout or "[No standard output]"
            verification_error = process.stderr or "[No standard error]"
        except Exception as e:
            verification_status = f"Failure (Exception: {e})"
            verification_output = "[Exception occurred]"
            verification_error = str(e)
            process = ProcessResult(-1, "", str(e))


        # Add verification results to the attempt log entry
        attempt_log_entry += f"""
    <verification>
      <status>{verification_status}</status>
      <output><![CDATA[
{verification_output}
]]></output>
      <error><![CDATA[
{verification_error}
]]></error>
    </verification>
"""

        # c. If the program runs without errors, break the loop
        if process.returncode == 0:
            rprint("[bold green]Verification successful![/bold green]")
            success = True
            history_log += attempt_log_entry + "  </attempt>\n" # Close the final successful attempt
            break

        # d. If the program fails
        rprint(f"[bold red]Verification failed with return code {process.returncode}.[/bold red]")
        current_error_message = verification_error # Use stderr as the primary error source

        # Add current error to the attempt log entry
        attempt_log_entry += f"""
    <current_error><![CDATA[
{current_error_message}
]]></current_error>
"""

        # Check budget *before* making the potentially expensive LLM call for the next attempt
        # (Only check if cost > 0 to avoid breaking before first attempt if budget is 0)
        if total_cost > budget and attempts > 0: # Check after first attempt cost is added
             rprint(f"[bold yellow]Budget exceeded (${total_cost:.4f} > ${budget:.4f}) before attempt {current_iteration_number}. Stopping.[/bold yellow]")
             history_log += attempt_log_entry + "    <error>Budget exceeded before LLM call</error>\n  </attempt>\n"
             break

        # Check max attempts *before* the LLM call for this attempt
        if attempts >= max_attempts:
             rprint(f"[bold red]Maximum attempts ({max_attempts}) reached before attempt {current_iteration_number}. Stopping.[/bold red]")
             # No need to add to history here, loop condition handles it
             break


        # Create backup copies for this iteration BEFORE calling LLM
        # Store in .pdd/backups/ (backup_dir already created above)
        code_backup_path = str(backup_dir / f"code_{current_iteration_number}{code_file_path.suffix}")
        program_backup_path = str(backup_dir / f"program_{current_iteration_number}{verification_program_path.suffix}")

        try:
            shutil.copy2(code_file, code_backup_path)
            shutil.copy2(verification_program, program_backup_path)
            if verbose:
                rprint(f"Created backups for attempt {current_iteration_number}: {code_backup_path}, {program_backup_path}")
        except Exception as e:
            rprint(f"[bold red]Error creating backups for attempt {current_iteration_number}: {e}[/bold red]")
            history_log += attempt_log_entry + f"    <error>Failed to create backups: {e}</error>\n  </attempt>\n"
            break # Cannot proceed reliably without backups

        # Read current file contents
        try:
            current_code = Path(code_file).read_text(encoding='utf-8')
            current_program = Path(verification_program).read_text(encoding='utf-8')
        except Exception as e:
            rprint(f"[bold red]Error reading source files: {e}[/bold red]")
            history_log += attempt_log_entry + "    <error>Failed to read source files</error>\n  </attempt>\n"
            break # Cannot proceed without file contents

        # Prepare the full history context for the LLM
        # Temporarily close the XML structure for the LLM call
        error_context_for_llm = history_log + attempt_log_entry + "  </attempt>\n</history>\n"

        # Call fix_code_module_errors
        rprint("Attempting to fix errors using LLM...")
        update_program, update_code, fixed_program, fixed_code = False, False, "", ""
        program_code_fix, cost, model_name_iter = "", 0.0, None

        # Capture Rich output from the internal function if needed, though it prints directly
        # Using a temporary console or redirect might be complex if it uses the global console
        # For simplicity, we assume fix_code_module_errors prints directly using `rprint`

        try:
            # Note: The example signature for fix_code_module_errors returns 7 values
            (update_program, update_code, fixed_program, fixed_code,
             program_code_fix, cost, model_name_iter) = fix_code_module_errors(
                program=current_program,
                prompt=prompt,
                code=current_code,
                errors=error_context_for_llm, # Pass the structured history
                strength=strength,
                temperature=temperature,
                time=time, # Pass time
                verbose=verbose,
            )
            if model_name_iter:
                 model_name = model_name_iter # Update model name if returned

        except Exception as e:
            rprint(f"[bold red]Error calling fix_code_module_errors: {e}[/bold red]")
            cost = 0.0 # Assume no cost if the call failed
            # Add error to the attempt log entry
            attempt_log_entry += f"""
    <fixing>
      <error>LLM call failed: {e}</error>
    </fixing>
"""
            history_log += attempt_log_entry + "  </attempt>\n" # Log the attempt with the LLM error
            attempts += 1 # Increment attempts even if LLM call failed
            break # Stop if the fixing mechanism itself fails

        # Add fixing results to the attempt log entry
        attempt_log_entry += f"""
    <fixing>
      <llm_analysis><![CDATA[
{program_code_fix or "[No analysis provided]"}
]]></llm_analysis>
      <decision>
        update_program: {str(update_program).lower()}
        update_code: {str(update_code).lower()}
      </decision>
      <cost>{cost:.4f}</cost>
      <model>{model_name_iter or 'N/A'}</model>
    </fixing>
"""
        # Close the XML tag for this attempt
        attempt_log_entry += "  </attempt>\n"
        # Append this attempt's full log to the main history
        history_log += attempt_log_entry

        # Write the cumulative history log to the file *after* each attempt
        try:
            with open(error_log_file, "w", encoding="utf-8") as f:
                f.write(history_log + "</history>\n") # Write complete history including root close tag
        except IOError as e:
            rprint(f"[bold red]Error writing to log file {error_log_file}: {e}[/bold red]")


        # Add cost and increment attempt counter (as per fix report) *before* checking budget
        total_cost += cost
        attempts += 1 # Moved this line here as per fix report
        rprint(f"Attempt Cost: ${cost:.4f}, Total Cost: ${total_cost:.4f}, Budget: ${budget:.4f}")

        if total_cost > budget:
            rprint(f"[bold yellow]Budget exceeded (${total_cost:.4f} > ${budget:.4f}) after attempt {attempts}. Stopping.[/bold yellow]")
            break # Stop loop

        # If LLM suggested no changes but verification failed, stop to prevent loops
        if not update_program and not update_code and process.returncode != 0:
             rprint("[bold yellow]LLM indicated no changes needed, but verification still fails. Stopping.[/bold yellow]")
             success = False # Ensure success is False
             break # Stop loop

        # Apply fixes if suggested
        try:
            if update_code:
                Path(code_file).write_text(fixed_code, encoding='utf-8')
                rprint(f"[green]Updated code file: {code_file}[/green]")
            if update_program:
                Path(verification_program).write_text(fixed_program, encoding='utf-8')
                rprint(f"[green]Updated verification program: {verification_program}[/green]")
        except IOError as e:
            rprint(f"[bold red]Error writing updated files: {e}[/bold red]")
            success = False # Mark as failed if we can't write updates
            break # Stop if we cannot apply fixes

        # The original 'attempts += 1' was here. It has been moved earlier.

        # Check if max attempts reached after incrementing (for the next loop iteration check)
        if attempts >= max_attempts:
             rprint(f"[bold red]Maximum attempts ({max_attempts}) reached. Final verification pending.[/bold red]")
             # Loop will terminate naturally on the next iteration's check


    # Step 4: Restore original files if the process failed overall
    if not success:
        rprint("[bold yellow]Attempting to restore original files as the process did not succeed.[/bold yellow]")
        try:
            # Check if backup files exist before attempting to restore
            if Path(original_code_backup).exists() and Path(original_program_backup).exists():
                shutil.copy2(original_code_backup, code_file)
                shutil.copy2(original_program_backup, verification_program)
                rprint(f"Restored {code_file} and {verification_program} from initial backups.")
            else:
                rprint(f"[bold red]Error: Initial backup files not found. Cannot restore original state.[/bold red]")
        except Exception as e:
            rprint(f"[bold red]Error restoring original files: {e}. Final files might be in a failed state.[/bold red]")

    # Clean up initial backup files regardless of success/failure
    try:
        if Path(original_code_backup).exists():
             os.remove(original_code_backup)
        if Path(original_program_backup).exists():
             os.remove(original_program_backup)
        if verbose:
            rprint(f"Removed initial backup files (if they existed).")
    except OSError as e:
        rprint(f"[bold yellow]Warning: Could not remove initial backup files: {e}[/bold yellow]")


    # Step 5: Read final file contents and determine return values
    final_code_content = ""
    final_program_content = ""
    # --- Start: Modified Final Content Reading ---
    if success:
        try:
            final_code_content = Path(code_file).read_text(encoding='utf-8')
            final_program_content = Path(verification_program).read_text(encoding='utf-8')
        except Exception as e:
            rprint(f"[bold red]Error reading final file contents even after success: {e}[/bold red]")
            # If we succeeded but can't read files, something is wrong. Mark as failure.
            success = False
            final_code_content = ""
            final_program_content = ""
    else:
        # If not successful, return empty strings as per test expectations
        final_code_content = ""
        final_program_content = ""
    # --- End: Modified Final Content Reading ---

    # Ensure the final history log file is complete
    try:
        with open(error_log_file, "w", encoding="utf-8") as f:
             f.write(history_log + "</history>\n")
    except IOError as e:
        rprint(f"[bold red]Final write to log file {error_log_file} failed: {e}[/bold red]")

    # Determine final number of attempts for reporting
    # The 'attempts' variable correctly counts the number of LLM fix cycles that were initiated.
    final_attempts_reported = attempts

    if not success and agentic_fallback:
        # Ensure error_log_file exists before calling agentic fix
        try:
            if not os.path.exists(error_log_file) or os.path.getsize(error_log_file) == 0:
                # Write minimal error log for agentic fix
                error_log_path = Path(error_log_file)
                error_log_path.parent.mkdir(parents=True, exist_ok=True)
                with open(error_log_path, "w") as elog:
                    if process:
                        elog.write(f"Verification failed with return code: {process.returncode}\n")
                        if process.stdout:
                            elog.write(f"\nStdout:\n{process.stdout}\n")
                        if process.stderr:
                            elog.write(f"\nStderr:\n{process.stderr}\n")
                    else:
                        elog.write("No error information available\n")
        except Exception as e:
            rprint(f"[yellow]Warning: Could not write error log before agentic fallback: {e}[/yellow]")

        rprint(f"[cyan]Attempting agentic fallback (prompt_file={prompt_file!r})...[/cyan]")
        agent_success, agent_msg, agent_cost, agent_model, agent_changed_files = _safe_run_agentic_crash(
            prompt_file=prompt_file,
            code_file=code_file,
            program_file=verification_program,
            crash_log_file=error_log_file,
            cwd=Path(prompt_file).parent if prompt_file else None
        )
        total_cost += agent_cost
        if not agent_success:
            rprint(f"[bold red]Agentic fallback failed: {agent_msg}[/bold red]")
        if agent_changed_files:
            rprint(f"[cyan]Agent modified {len(agent_changed_files)} file(s):[/cyan]")
            for f in agent_changed_files:
                rprint(f"  • {f}")
        if agent_success:
            model_name = agent_model or model_name
            try:
                final_code_content = Path(code_file).read_text(encoding='utf-8')
                final_program_content = Path(verification_program).read_text(encoding='utf-8')
            except Exception as e:
                rprint(f"[yellow]Warning: Could not read files after successful agentic fix: {e}[/yellow]")
            success = True

    return (
        success,
        final_program_content,
        final_code_content,
        final_attempts_reported,
        total_cost,
        model_name,
    )

# Example usage (requires a dummy fix_code_module_errors and verification script)
# (Keep the example usage block as is for demonstration/manual testing)
if __name__ == "__main__":
    # Create dummy files for demonstration
    DUMMY_CODE_FILE = "dummy_code.py"
    DUMMY_VERIFICATION_FILE = "dummy_verify.py"
    DUMMY_ERROR_LOG = "dummy_error.log"

    # Dummy code with an error
    Path(DUMMY_CODE_FILE).write_text(
        "def my_func(a, b):\n    return a + b # Potential type error if strings used\n",
        encoding='utf-8'
    )

    # Dummy verification script that will fail initially
    Path(DUMMY_VERIFICATION_FILE).write_text(
        f"""
import sys
# Import the function from the code file
try:
    # Assume dummy_code.py is in the same directory
    from dummy_code import my_func
except ImportError as e:
    print(f"Import Error: {{e}}", file=sys.stderr)
    sys.exit(1)

# This will cause a TypeError initially
try:
    result = my_func(5, "a") # Intentionally cause error
    print(f"Result: {{result}}")
    # Check if result is as expected (it won't be initially)
    # Add more checks if needed
    # if result != expected_value:
    #    print(f"Assertion failed: Result {{result}} != expected_value", file=sys.stderr)
    #    sys.exit(1)
except Exception as e:
    print(f"Runtime Error: {{e}}", file=sys.stderr)
    sys.exit(1) # Exit with non-zero code on error

# If we reach here, it means no exceptions occurred
print("Verification passed.")
sys.exit(0) # Exit with zero code for success
""",
        encoding='utf-8'
    )

    # Dummy fix_code_module_errors function (replace with actual import)
    # This dummy version simulates fixing the code on the second attempt
    _fix_attempt_counter = 0
    def dummy_fix_code_module_errors(program, prompt, code, errors, strength, temperature, verbose):
        global _fix_attempt_counter
        _fix_attempt_counter += 1
        cost = 0.05 # Simulate API cost
        model = "dummy-fixer-model-v1"
        analysis = f"Analysis based on errors (attempt {_fix_attempt_counter}):\n{errors[-200:]}" # Show recent history

        if _fix_attempt_counter >= 2:
             # Simulate fixing the code file on the second try
             fixed_code = "def my_func(a, b):\n    # Fixed: Ensure inputs are numbers or handle types\n    try:\n        return float(a) + float(b)\n    except (ValueError, TypeError):\n        return 'Error: Invalid input types'\n"
             # Simulate fixing the verification program to use valid inputs
             fixed_program = program.replace('my_func(5, "a")', 'my_func(5, 10)') # Fix the call
             return True, True, fixed_program, fixed_code, analysis, cost, model # update_program, update_code
        else:
             # Simulate no changes needed on the first try, but still return cost
             return False, False, program, code, analysis + "\nNo changes suggested this time.", cost, model

    # Replace the actual import with the dummy for this example run
    original_fix_func = fix_code_module_errors
    fix_code_module_errors = dummy_fix_code_module_errors

    rprint("[bold yellow]Running example fix_code_loop...[/bold yellow]")

    results = fix_code_loop(
        code_file=DUMMY_CODE_FILE,
        prompt="Create a function that adds two numbers.",
        verification_program=DUMMY_VERIFICATION_FILE,
        strength=0.5,
        temperature=0.1,
        max_attempts=3,
        budget=1.0,
        error_log_file=DUMMY_ERROR_LOG,
        verbose=True,
    )

    rprint("\n[bold blue]----- Fix Loop Results -----[/bold blue]")
    rprint(f"Success: {results[0]}")
    rprint(f"Total Attempts Reported: {results[3]}") # Updated label
    rprint(f"Total Cost: ${results[4]:.4f}")
    rprint(f"Model Name: {results[5]}")
    if results[0]: # Only print final code/program if successful
        rprint("\nFinal Code:")
        rprint(f"[code]{results[2]}[/code]")
        rprint("\nFinal Verification Program:")
        rprint(f"[code]{results[1]}[/code]")
    else:
        rprint("\nFinal Code: [Not successful, code not returned]")
        rprint("Final Verification Program: [Not successful, program not returned]")


    rprint(f"\nCheck the error log file: {DUMMY_ERROR_LOG}")
    if Path(DUMMY_ERROR_LOG).exists():
        rprint("\n[bold blue]----- Error Log Content ----- [/bold blue]")
        log_content = Path(DUMMY_ERROR_LOG).read_text(encoding='utf-8')
        # Use Rich Panel or just print for log content display
        from rich.panel import Panel
        rprint(Panel(log_content, title=DUMMY_ERROR_LOG, border_style="dim blue"))


    # Restore original function if needed elsewhere
    fix_code_module_errors = original_fix_func

    # Clean up dummy files
    # try:
    #     os.remove(DUMMY_CODE_FILE)
    #     os.remove(DUMMY_VERIFICATION_FILE)
    #     # Keep the log file for inspection
    #     # os.remove(DUMMY_ERROR_LOG)
    #     # Remove backups if they exist
    #     for f in Path(".").glob("dummy_*_original_backup.py"): os.remove(f)
    #     for f in Path(".").glob("dummy_code_*.py"): # Remove attempt backups like dummy_code_1.py
    #          if "_original_backup" not in f.name: os.remove(f)
    #     for f in Path(".").glob("dummy_verify_*.py"): # Remove attempt backups like dummy_verify_1.py
    #          if "_original_backup" not in f.name: os.remove(f)
    # except OSError as e:
    #     print(f"Error cleaning up dummy files: {e}")
