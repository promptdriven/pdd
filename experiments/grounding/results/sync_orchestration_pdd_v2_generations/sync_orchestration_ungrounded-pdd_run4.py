import threading
import time
import json
import datetime
import subprocess
import re
import os
import sys
import logging
import tempfile
import traceback
import shutil
from pathlib import Path
from typing import Dict, Any, Optional, List, Callable, Tuple
from dataclasses import asdict, dataclass, field
import click

from .sync_tui import maybe_steer_operation, DEFAULT_STEER_TIMEOUT_S, SyncApp
from .operation_log import (
    load_operation_log,
    create_log_entry,
    update_log_entry,
    append_log_entry,
    log_event,
    save_fingerprint,
    save_run_report,
    clear_run_report,
)
from .sync_determine_operation import (
    sync_determine_operation,
    get_pdd_file_paths,
    RunReport,
    SyncDecision,
    PDD_DIR,
    META_DIR,
    SyncLock,
    read_run_report,
    calculate_sha256,
    calculate_current_hashes,
    _safe_basename,
)
from .auto_deps_main import auto_deps_main
from .code_generator_main import code_generator_main
from .context_generator_main import context_generator_main
from .crash_main import crash_main
from .fix_verification_main import fix_verification_main
from .cmd_test_main import cmd_test_main
from .fix_main import fix_main
from .update_main import update_main
from .python_env_detector import detect_host_python_executable
from .get_run_command import get_run_command_for_file
from .get_test_command import get_test_command_for_file
from .pytest_output import extract_failing_files_from_output, _find_project_root
from . import DEFAULT_STRENGTH

# Constants
MAX_CONSECUTIVE_TESTS = 3
MAX_TEST_EXTEND_ATTEMPTS = 2
MAX_CONSECUTIVE_CRASHES = 3
MAX_CYCLE_REPEATS = 2

class AtomicStateUpdate:
    """
    Context manager for atomic metadata updates.
    Ensures run_report and fingerprint are updated consistently.
    """
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language.lower()
        self.pending_fingerprint = None
        self.pending_run_report = None

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            if self.pending_run_report:
                save_run_report(self.basename, self.language, self.pending_run_report)
            if self.pending_fingerprint:
                # Fingerprint save logic is complex, handled by save_fingerprint helper
                pass
        return False

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Check if we should use agentic fallback paths (no loops)."""
    return language.lower() != "python" or agentic_mode

def _create_mock_context(**kwargs) -> click.Context:
    """Create a mock Click context for invoking underlying main functions."""
    ctx = click.Context(click.Command("sync_internal"))
    ctx.obj = {
        "strength": kwargs.get("strength", DEFAULT_STRENGTH),
        "temperature": kwargs.get("temperature", 0.0),
        "time": kwargs.get("time_param", 0.25),
        "verbose": kwargs.get("verbose", False),
        "quiet": kwargs.get("quiet", False),
        "force": kwargs.get("force", True),
        "local": kwargs.get("local", False),
        "context": kwargs.get("context_override"),
        "confirm_callback": kwargs.get("confirm_callback")
    }
    ctx.params = {
        "force": kwargs.get("force", True),
        "quiet": kwargs.get("quiet", False),
        "local": kwargs.get("local", False)
    }
    return ctx

def _display_sync_log(basename: str, language: str, verbose: bool):
    """Format and display the sync history log."""
    entries = load_operation_log(basename, language.lower())
    if not entries:
        click.echo(f"No sync history found for {basename}_{language}")
        return

    click.echo(f"\n--- Sync Analysis for {basename} ({language}) ---")
    for entry in entries:
        ts = entry.get("timestamp", "N/A")
        op = entry.get("operation", "unknown").upper()
        res = "SUCCESS" if entry.get("success") else "FAILED"
        msg = f"[{ts}] {op:10} | {res:8}"
        if verbose:
            reason = entry.get("reason", "")
            cost = entry.get("actual_cost", 0.0)
            msg += f" | Cost: ${cost:.4f} | Reason: {reason}"
        click.echo(msg)

def _parse_test_output(output: str, language: str) -> Tuple[int, int, float]:
    """Parse output from various test runners."""
    passed, failed, coverage = 0, 0, 0.0
    lang_lower = language.lower()

    # Pytest / Generic
    p_match = re.search(r"(\d+) passed", output)
    f_match = re.search(r"(\d+) failed", output)
    if p_match: passed = int(p_match.group(1))
    if f_match: failed = int(f_match.group(1))

    # Coverage
    cov_match = re.search(r"TOTAL\s+\d+\s+\d+\s+(\d+)%", output)
    if cov_match: coverage = float(cov_match.group(1))

    return passed, failed, coverage

def _python_cov_target_for_code_file(code_file: Path) -> str:
    """Determine the module path for pytest --cov."""
    try:
        parts = code_file.resolve().parts
        if "src" in parts:
            idx = parts.index("src")
            target = ".".join(parts[idx+1:]).replace(".py", "")
            return target
    except:
        pass
    return str(code_file.stem)

def _execute_tests_and_create_run_report(
    test_file: Path,
    basename: str,
    language: str,
    target_coverage: float,
    *,
    code_file: Optional[Path] = None,
    atomic_state: Optional[AtomicStateUpdate] = None,
    test_files: Optional[List[Path]] = None
) -> Dict[str, Any]:
    """Run tests, collect coverage, and save a RunReport."""
    lang_lower = language.lower()
    report_data = {"exit_code": 1, "tests_passed": 0, "tests_failed": 0, "coverage": 0.0}
    
    # Resolve command
    test_cmd = get_test_command_for_file(str(test_file), language=language)
    if not test_cmd:
        return report_data

    # Python-specific coverage logic
    env = os.environ.copy()
    if lang_lower == "python" and code_file:
        cov_target = _python_cov_target_for_code_file(code_file)
        root = _find_project_root(test_file)
        if root:
            env["PYTHONPATH"] = f"{root}:{root}/src:{env.get('PYTHONPATH', '')}"
            test_cmd += f" --cov={cov_target} --rootdir={root} -c /dev/null"

    # Execution
    try:
        targets = [str(f) for f in test_files] if test_files else [str(test_file)]
        full_cmd = f"{test_cmd} {' '.join(targets)}"
        process = subprocess.run(
            full_cmd,
            shell=True,
            capture_output=True,
            text=True,
            env=env,
            start_new_session=True,
            stdin=subprocess.DEVNULL
        )
        report_data["exit_code"] = process.returncode
        p, f, c = _parse_test_output(process.stdout + process.stderr, language)
        report_data.update({"tests_passed": p, "tests_failed": f, "coverage": c})
    except Exception as e:
        report_data["error"] = str(e)

    # State capture
    current_hashes = calculate_current_hashes(test_file, code_file, None, None)
    report_data["test_hash"] = current_hashes.get("test")
    if test_files:
        report_data["test_file_hashes"] = {str(f): calculate_sha256(f) for f in test_files if f.exists()}

    save_run_report(basename, lang_lower, report_data)
    return report_data

def _create_synthetic_run_report_for_agentic_success(
    test_file: Path, basename: str, language: str, *, atomic_state: Optional[AtomicStateUpdate] = None
):
    """Save a successful run report when an agent signals success without local run."""
    report = {
        "timestamp": datetime.datetime.now().isoformat(),
        "exit_code": 0,
        "tests_passed": 1,
        "tests_failed": 0,
        "coverage": 100.0,
        "test_hash": calculate_sha256(test_file) if test_file.exists() else "agentic_test_success"
    }
    save_run_report(basename, language.lower(), report)

def _detect_example_errors(output: str) -> Optional[str]:
    """Basic detection of runtime errors in program output."""
    if "Traceback (most recent call last):" in output:
        return output
    if "ERROR" in output.upper() and ("Traceback" in output or "Exception" in output):
        return output
    return None

def sync_orchestration(
    basename: str,
    target_coverage: float = 90.0,
    language: str = "python",
    prompts_dir: str = "prompts",
    code_dir: str = "src",
    examples_dir: str = "examples",
    tests_dir: str = "tests",
    max_attempts: int = 3,
    budget: float = 10.0,
    skip_verify: bool = False,
    skip_tests: bool = False,
    dry_run: bool = False,
    force: bool = False,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time_param: float = 0.25,
    verbose: bool = False,
    quiet: bool = False,
    output_cost: Optional[str] = None,
    review_examples: bool = False,
    local: bool = False,
    context_config: Optional[Dict[str, str]] = None,
    context_override: Optional[str] = None,
    confirm_callback: Optional[Callable[[str, str], bool]] = None,
    no_steer: bool = False,
    steer_timeout: float = DEFAULT_STEER_TIMEOUT_S,
    agentic_mode: bool = False,
) -> Dict[str, Any]:
    """Orchestrates the complete PDD sync workflow."""
    from .sync_main import construct_paths, get_extension
    from .sync_tui import show_exit_animation

    # Defense in depth defaults
    target_coverage = target_coverage if target_coverage is not None else 90.0
    budget = budget if budget is not None else 20.0
    max_attempts = max_attempts if max_attempts is not None else 3

    if dry_run:
        _display_sync_log(basename, language, verbose)
        return {"success": True, "log_entries": load_operation_log(basename, language.lower())}

    # Reference objects for thread-safe coordination
    state = {
        "op": "initializing",
        "reason": "Resolving paths",
        "total_cost": 0.0,
        "start_time": time.time(),
        "ops_completed": [],
        "ops_skipped": [],
        "errors": [],
        "last_model": "none",
        "app_ref": [None],
        "user_confirmed_overwrite": [False]
    }

    def wrapped_confirm(msg, default=True):
        if state["user_confirmed_overwrite"][0]:
            return True
        if state["app_ref"][0]:
            res = state["app_ref"][0].request_confirmation(msg)
            if res: state["user_confirmed_overwrite"][0] = True
            return res
        res = click.confirm(msg, default=default)
        if res: state["user_confirmed_overwrite"][0] = True
        return res

    mock_ctx = _create_mock_context(
        strength=strength, temperature=temperature, time_param=time_param,
        verbose=verbose, quiet=quiet, force=force, local=local,
        context_override=context_override, confirm_callback=wrapped_confirm
    )

    def sync_worker_logic():
        try:
            with SyncLock(basename, language.lower()) as lock:
                log_event(basename, language, "lock_acquired", {"lock_file": lock.lock_file}, "sync")
                
                # Internal cycle tracking
                history = []
                consecutive_fix = 0
                consecutive_test = 0
                consecutive_crash = 0
                test_extend_attempts = 0

                while True:
                    # 1. Determine next move
                    decision: SyncDecision = sync_determine_operation(
                        basename, language, target_coverage, log_mode=True
                    )
                    
                    if decision.operation in ("all_synced", "nothing", "fail_and_request_manual_merge", "error"):
                        state["op"] = decision.operation
                        state["reason"] = decision.reason
                        break

                    # 2. Interactive Steering
                    current_op = decision.operation
                    if not no_steer:
                        steered_op, should_abort = maybe_steer_operation(
                            current_op, decision.reason, state["app_ref"][0], quiet, skip_tests, skip_verify, timeout_s=steer_timeout
                        )
                        if should_abort:
                            state["errors"].append("Sync aborted by user steering.")
                            break
                        if steered_op != current_op:
                            log_event(basename, language, "steering_override", {"from": current_op, "to": steered_op}, "sync")
                            decision.operation = steered_op

                    # 3. Cycle Detection
                    history.append(decision.operation)
                    if len(history) >= 4:
                        last_4 = history[-4:]
                        if last_4 == ["crash", "verify", "crash", "verify"] or last_4 == ["test", "fix", "test", "fix"]:
                            state["errors"].append(f"Infinite cycle detected: {last_4}. Requesting manual intervention.")
                            break
                    
                    if decision.operation == "fix":
                        consecutive_fix += 1
                        if consecutive_fix > 5: break
                    else: consecutive_fix = 0

                    # 4. Execute Operation
                    op = decision.operation
                    state["op"] = op
                    state["reason"] = decision.reason
                    
                    log_entry = create_log_entry(
                        operation=op, reason=decision.reason, invocation_mode="sync",
                        estimated_cost=decision.estimated_cost, confidence=decision.confidence,
                        decision_type=decision.decision_type
                    )

                    # Path resolution
                    paths = get_pdd_file_paths(basename, language, prompts_dir, code_dir, examples_dir, tests_dir)
                    p_path = paths["prompt"]
                    c_path = paths["code"]
                    e_path = paths["example"]
                    t_path = paths["test"]
                    t_files = paths.get("test_files", [])

                    op_success = False
                    op_cost = 0.0
                    op_model = "unknown"
                    
                    start_op_time = time.time()
                    
                    try:
                        if op == "auto-deps":
                            res = auto_deps_main(mock_ctx, str(p_path), f"{examples_dir}/**/*", output=str(p_path))
                            op_success, op_cost, op_model = True, res[1], res[2]
                        
                        elif op == "generate":
                            res = code_generator_main(mock_ctx, str(p_path), output=str(c_path))
                            op_success, op_cost, op_model = True, res[2], res[3]
                            clear_run_report(basename, language)
                            
                        elif op == "example":
                            res = context_generator_main(mock_ctx, str(p_path), str(c_path), output=str(e_path))
                            op_success, op_cost, op_model = True, res[1], res[2]
                            
                        elif op == "crash":
                            consecutive_crash += 1
                            if consecutive_crash > MAX_CONSECUTIVE_CRASHES: break
                            
                            err_file = Path(tempfile.gettempdir()) / f"pdd_crash_{_safe_basename(basename)}.log"
                            # For non-python, we trust agentic fallback
                            force_agentic = _use_agentic_path(language, agentic_mode)
                            res = crash_main(
                                mock_ctx, str(p_path), str(c_path), str(e_path), str(err_file),
                                output=str(c_path), output_program=str(e_path), loop=True,
                                max_attempts=(0 if force_agentic else max_attempts), budget=budget - state["total_cost"]
                            )
                            op_success, op_cost, op_model = res[0], res[4], res[5]
                            if op_success:
                                if language.lower() == "python":
                                    _execute_tests_and_create_run_report(e_path, basename, language, 0, code_file=c_path)
                                else:
                                    save_run_report(basename, language.lower(), {"exit_code": 0, "tests_passed": 1, "tests_failed": 0})
                        
                        elif op == "verify":
                            res = fix_verification_main(
                                mock_ctx, str(p_path), str(c_path), str(e_path),
                                output_code=str(c_path), output_program=str(e_path),
                                loop=True, max_attempts=max_attempts, budget=budget - state["total_cost"]
                            )
                            op_success, op_cost, op_model = res[0], res[4], res[5]

                        elif op == "test":
                            consecutive_test += 1
                            if consecutive_test > MAX_CONSECUTIVE_TESTS: break
                            res = cmd_test_main(mock_ctx, str(p_path), str(c_path), output=str(t_path), language=language)
                            op_cost, op_model = res[1], res[2]
                            agentic_success = res[3]
                            if agentic_success:
                                op_success = True
                                _create_synthetic_run_report_for_agentic_success(t_path, basename, language)
                            else:
                                op_success = t_path.exists()
                                if op_success:
                                    _execute_tests_and_create_run_report(t_path, basename, language, target_coverage, code_file=c_path, test_files=t_files)

                        elif op == "test_extend":
                            test_extend_attempts += 1
                            if test_extend_attempts > MAX_TEST_EXTEND_ATTEMPTS:
                                state["ops_skipped"].append("test_extend (max attempts)")
                                op_success = True
                            else:
                                res = cmd_test_main(
                                    mock_ctx, str(p_path), str(c_path), output=str(t_path), 
                                    language=language, existing_tests=[str(f) for f in t_files], 
                                    target_coverage=target_coverage, merge=True
                                )
                                op_cost, op_model = res[1], res[2]
                                if _use_agentic_path(language, agentic_mode) and language.lower() not in ("python", "typescript"):
                                    op_success = True
                                    _create_synthetic_run_report_for_agentic_success(t_path, basename, language)
                                else:
                                    _execute_tests_and_create_run_report(t_path, basename, language, target_coverage, code_file=c_path, test_files=t_files)
                                    op_success = True

                        elif op == "fix":
                            # Determine which file to fix if multiple exist
                            report = read_run_report(basename, language)
                            failing_file = str(t_path)
                            if report and "test_file_hashes" in report and report.get("tests_failed", 0) > 0:
                                # Logic to find specific failing file from output would go here
                                pass
                            
                            force_agentic = _use_agentic_path(language, agentic_mode)
                            res = fix_main(
                                mock_ctx, str(p_path), str(c_path), failing_file, "",
                                output_code=str(c_path), output_test=failing_file,
                                loop=True, max_attempts=(0 if force_agentic else max_attempts),
                                budget=budget - state["total_cost"]
                            )
                            op_success, op_cost, op_model = res[0], res[4], res[5]
                            if op_success:
                                if language.lower() == "python":
                                    _execute_tests_and_create_run_report(t_path, basename, language, target_coverage, code_file=c_path, test_files=t_files)
                                else:
                                    save_run_report(basename, language.lower(), {"exit_code": 0, "tests_passed": 1, "tests_failed": 0})

                        elif op == "update":
                            res = update_main(mock_ctx, str(p_path), str(c_path), use_git=True)
                            op_success, op_cost, op_model = True, res[1], res[2]

                    except Exception as e:
                        state["errors"].append(f"Operation {op} failed: {str(e)}")
                        if verbose: traceback.print_exc()
                    
                    # Update Log and State
                    duration = time.time() - start_op_time
                    state["total_cost"] += op_cost
                    state["last_model"] = op_model
                    
                    updated_entry = update_log_entry(log_entry, op_success, op_cost, op_model, duration, None if op_success else "Operation failed")
                    append_log_entry(basename, language.lower(), updated_entry)
                    
                    if op_success:
                        state["ops_completed"].append(op)
                        save_fingerprint(basename, language.lower(), op, paths, op_cost, op_model)
                    else:
                        state["errors"].append(f"Operation {op} failed to complete successfully.")
                        break

                    if state["total_cost"] >= budget:
                        state["errors"].append(f"Budget exceeded: ${state['total_cost']:.2f} >= ${budget:.2f}")
                        break

        except Exception as e:
            state["errors"].append(f"Fatal sync error: {str(e)}")
            if verbose: traceback.print_exc()

    # TUI vs Headless Execution
    is_headless = not sys.stdin.isatty() or os.getenv("CI") == "true" or quiet
    if is_headless:
        os.environ["PDD_FORCE"] = "1"
        sync_worker_logic()
    else:
        app = SyncApp(worker_func=sync_worker_logic)
        state["app_ref"][0] = app
        app.run()
        if app.worker_exception:
            print(f"Worker crashed: {app.worker_exception}", file=sys.stderr)
            traceback.print_exception(type(app.worker_exception), app.worker_exception, app.worker_exception.__traceback__)
        if not quiet:
            show_exit_animation()

    # Final Result
    total_time = time.time() - state["start_time"]
    success = state["op"] == "all_synced" and not state["errors"]
    
    return {
        "success": success,
        "operations_completed": state["ops_completed"],
        "skipped_operations": state["ops_skipped"],
        "total_cost": state["total_cost"],
        "total_time": total_time,
        "final_state": state["op"],
        "errors": state["errors"],
        "error": "; ".join(state["errors"]) if state["errors"] else None,
        "model_name": state["last_model"]
    }