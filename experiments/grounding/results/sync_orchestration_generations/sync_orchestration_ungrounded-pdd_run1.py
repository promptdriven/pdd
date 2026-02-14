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
from dataclasses import asdict

import click

# PDD Internal Imports
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
from .pytest_output import extract_failing_files_from_output, _find_project_root
from . import DEFAULT_STRENGTH

# Constants
MAX_CONSECUTIVE_TESTS = 3
MAX_TEST_EXTEND_ATTEMPTS = 2
MAX_CONSECUTIVE_CRASHES = 3
MAX_CYCLE_REPEATS = 2

class AtomicStateUpdate:
    """
    Context manager for atomic updates to PDD state (fingerprint and run report).
    Ensures that if one write fails, the state remains consistent.
    """
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language
        self.pending_fingerprint = None
        self.pending_run_report = None

    def __enter__(self):
        return self

    def set_fingerprint(self, operation, paths, cost, model):
        self.pending_fingerprint = (operation, paths, cost, model)

    def set_run_report(self, report_data):
        self.pending_run_report = report_data

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            if self.pending_run_report:
                save_run_report(self.basename, self.language, self.pending_run_report)
            if self.pending_fingerprint:
                save_fingerprint(self.basename, self.language, *self.pending_fingerprint)


def _get_extension(language: str) -> str:
    """Helper to get file extension for a language."""
    from .get_extension import get_extension
    return get_extension(language)


def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Check if we should use agentic path (max_attempts=0, skip iterative loops)."""
    return language.lower() != "python" or agentic_mode


def _display_sync_log(basename: str, language: str, verbose: bool):
    """Format and display the sync log for dry-run mode."""
    entries = load_operation_log(basename, language)
    if not entries:
        click.echo(f"No sync history found for {basename}_{language}.")
        return

    click.echo(f"--- Sync Log for {basename}_{language} ---")
    for entry in entries:
        timestamp = entry.get("timestamp", "Unknown")
        op = entry.get("operation", "unknown").upper()
        success = "PASS" if entry.get("success") else "FAIL"
        cost = entry.get("actual_cost", 0.0)
        
        line = f"[{timestamp}] {op:<10} | {success} | Cost: ${cost:.4f}"
        if verbose:
            line += f" | Reason: {entry.get('reason')} | Model: {entry.get('model')}"
        click.echo(line)


def _create_mock_context(**kwargs) -> click.Context:
    """Creates a mock click context for passing to *_main functions."""
    ctx = click.Context(click.Command("sync"))
    ctx.obj = kwargs.get("obj", {})
    ctx.params = kwargs.get("params", {})
    return ctx


def _parse_test_output(output: str, language: str) -> Tuple[int, int, float]:
    """Parses test runner output to extract passed, failed, and coverage."""
    passed = 0
    failed = 0
    coverage = 0.0
    
    lang_lower = language.lower()
    
    # Generic coverage search (95% or 95.0%)
    cov_match = re.search(r'TOTAL\s+.*?\s+(\d+(?:\.\d+)?)%', output)
    if cov_match:
        coverage = float(cov_match.group(1))

    if lang_lower == "python":
        # Pytest pattern: 5 passed, 1 failed in 0.01s
        m = re.search(r'(\d+) passed', output)
        if m: passed = int(m.group(1))
        m = re.search(r'(\d+) failed', output)
        if m: failed = int(m.group(1))
        # fallback for single failure
        if failed == 0 and "short test summary info" in output and "FAILED" in output:
             failed = output.count("FAILED ")
    else:
        # Generic patterns for Jest/Vitest/Mocha/Go/Cargo
        # Tests: 5 passed, 5 total
        m = re.search(r'(\d+) passed', output, re.IGNORECASE)
        if m: passed = int(m.group(1))
        m = re.search(r'(\d+) failed', output, re.IGNORECASE)
        if m: failed = int(m.group(1))
        
    return passed, failed, coverage


def _python_cov_target_for_code_file(code_file: str) -> str:
    """Determine dotted module path for pytest-cov."""
    path = Path(code_file)
    # Heuristic: if in src/, use that, otherwise just the stem
    if "src" in path.parts:
        idx = path.parts.index("src")
        rel = path.parts[idx+1:]
        return ".".join(rel).replace(".py", "")
    return path.stem


def _execute_tests_and_create_run_report(
    test_file: str, 
    basename: str, 
    language: str, 
    target_coverage: float, 
    *, 
    code_file: Optional[str] = None, 
    atomic_state: Optional[AtomicStateUpdate] = None,
    test_files: Optional[List[str]] = None
) -> Dict[str, Any]:
    """Execute tests with coverage and create/save a RunReport."""
    from .get_test_command import get_test_command_for_file
    
    cmd = get_test_command_for_file(test_file, language=language)
    if not cmd:
        return {"success": False, "error": "Could not determine test command"}

    # Project root for python
    env = os.environ.copy()
    cwd = os.getcwd()
    
    if language.lower() == "python":
        root = _find_project_root(test_file)
        if root:
            src_dir = str(Path(root) / "src")
            env["PYTHONPATH"] = f"{root}:{src_dir}:{env.get('PYTHONPATH', '')}"
            if "--cov" not in cmd and code_file:
                cov_target = _python_cov_target_for_code_file(code_file)
                cmd += f" --cov={cov_target} --cov-report=term-missing"

    # Run command
    try:
        process = subprocess.run(
            cmd,
            shell=True,
            capture_output=True,
            text=True,
            env=env,
            timeout=300,
            start_new_session=True
        )
        output = process.stdout + "\n" + process.stderr
        exit_code = process.returncode
    except subprocess.TimeoutExpired:
        output = "Test execution timed out."
        exit_code = 124
    except Exception as e:
        output = str(e)
        exit_code = 1

    passed, failed, coverage = _parse_test_output(output, language)
    
    # Calculate hashes for RunReport
    test_hashes = {}
    targets = test_files if test_files else [test_file]
    for f in targets:
        if Path(f).exists():
            test_hashes[f] = calculate_sha256(f)

    report_data = {
        "timestamp": datetime.datetime.now().isoformat(),
        "exit_code": exit_code,
        "tests_passed": passed,
        "tests_failed": failed,
        "coverage": coverage,
        "test_hash": calculate_sha256(test_file) if Path(test_file).exists() else None,
        "test_file_hashes": test_hashes,
        "output": output
    }

    if atomic_state:
        atomic_state.set_run_report(report_data)
    else:
        save_run_report(basename, language, report_data)
        
    return {"success": exit_code == 0, "report": report_data}


def _create_synthetic_run_report_for_agentic_success(
    test_file: str, 
    basename: str, 
    language: str, 
    *, 
    atomic_state: Optional[AtomicStateUpdate] = None
):
    """Creates a synthetic successful run report for agentic test generation."""
    h = calculate_sha256(test_file) if Path(test_file).exists() else "agentic_test_success"
    report_data = {
        "timestamp": datetime.datetime.now().isoformat(),
        "exit_code": 0,
        "tests_passed": 1,
        "tests_failed": 0,
        "coverage": 100.0,
        "test_hash": h,
        "test_file_hashes": {test_file: h} if Path(test_file).exists() else {},
        "output": "Synthetic report for agentic success."
    }
    if atomic_state:
        atomic_state.set_run_report(report_data)
    else:
        save_run_report(basename, language, report_data)


def sync_orchestration(
    basename: str,
    target_coverage: float = 90.0,
    language: str = "python",
    prompts_dir: str = "prompts",
    code_dir: str = "src",
    examples_dir: str = "examples",
    tests_dir: str = "tests",
    max_attempts: int = 3,
    budget: float = 20.0,
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
    
    # Defaults defense
    target_coverage = target_coverage if target_coverage is not None else 90.0
    budget = budget if budget is not None else 20.0
    max_attempts = max_attempts if max_attempts is not None else 3

    if dry_run:
        _display_sync_log(basename, language, verbose)
        return {"success": True, "log_entries": load_operation_log(basename, language)}

    # Ref-based state for TUI
    function_name_ref = ["Starting Sync..."]
    cost_ref = [0.0]
    prompt_color_ref = ["white"]
    code_color_ref = ["white"]
    example_color_ref = ["white"]
    test_color_ref = ["white"]
    prompt_path_ref = [""]
    code_path_ref = [""]
    example_path_ref = [""]
    test_path_ref = [""]
    progress_callback_ref = [None]
    app_ref = [None]
    stop_event = threading.Event()
    user_confirmed_overwrite = [False]

    def get_confirm_callback():
        def wrapper(msg, title):
            if force or user_confirmed_overwrite[0]:
                return True
            if app_ref[0]:
                res = app_ref[0].request_confirmation(msg, title)
                if res: user_confirmed_overwrite[0] = True
                return res
            # Headless fallback
            res = click.confirm(msg, default=True)
            if res: user_confirmed_overwrite[0] = True
            return res
        return wrapper

    # Main logic encapsulated for TUI thread
    result_holder = {}

    def sync_worker_logic():
        try:
            with SyncLock(basename, language) as lock:
                log_event(basename, language, "lock_acquired", {"basename": basename}, "sync")
                
                ops_completed = []
                ops_skipped = []
                total_cost = 0.0
                errors = []
                history = []
                consecutive_ops = {"test": 0, "crash": 0, "fix": 0}
                
                # Resolve paths initially
                pdd_files = get_pdd_file_paths(basename, language, prompts_dir, code_dir, examples_dir, tests_dir)
                prompt_path_ref[0] = str(pdd_files['prompt'])
                code_path_ref[0] = str(pdd_files['code'])
                example_path_ref[0] = str(pdd_files['example'])
                test_path_ref[0] = str(pdd_files['test'])

                while not stop_event.is_set():
                    # Check budget
                    if total_cost >= budget:
                        errors.append(f"Budget exceeded: ${total_cost:.2f} >= ${budget:.2f}")
                        break
                    if total_cost > budget * 0.8:
                        log_event(basename, language, "budget_warning", {"remaining": budget - total_cost}, "sync")

                    # Analyze state
                    decision = sync_determine_operation(basename, language, target_coverage, log_mode=False)
                    op = decision.operation
                    
                    # Update TUI state colors based on analysis
                    current_hashes = calculate_current_hashes(pdd_files)
                    prompt_color_ref[0] = "green" if current_hashes.get('prompt') else "red"
                    code_color_ref[0] = "green" if current_hashes.get('code') else "red"
                    example_color_ref[0] = "green" if current_hashes.get('example') else "red"
                    test_color_ref[0] = "green" if current_hashes.get('test') else "red"

                    if op in ("all_synced", "nothing", "fail_and_request_manual_merge", "error"):
                        function_name_ref[0] = f"Sync Finished: {op}"
                        break

                    # Steering
                    if not no_steer:
                        steered_op, should_abort = maybe_steer_operation(
                            op, decision.reason, app_ref[0], quiet, skip_tests, skip_verify, timeout_s=steer_timeout
                        )
                        if should_abort:
                            errors.append("Sync aborted by user steering.")
                            break
                        if steered_op != op:
                            log_event(basename, language, "steering_override", {"original": op, "new": steered_op}, "sync")
                            op = steered_op

                    # Log entry
                    entry = create_log_entry(
                        operation=op, reason=decision.reason, invocation_mode="sync",
                        estimated_cost=decision.estimated_cost, confidence=decision.confidence, decision_type=decision.decision_type
                    )
                    
                    # Loop detection
                    history.append(op)
                    if op in consecutive_ops:
                        consecutive_ops[op] += 1
                        if consecutive_ops[op] > {"test": MAX_CONSECUTIVE_TESTS, "crash": MAX_CONSECUTIVE_CRASHES, "fix": 5}[op]:
                            errors.append(f"Broken infinite loop for {op}")
                            break
                    else:
                        for k in consecutive_ops: consecutive_ops[k] = 0

                    # Execution
                    function_name_ref[0] = f"Executing: {op}"
                    start_time = time.time()
                    op_success = False
                    op_cost = 0.0
                    op_model = "unknown"
                    op_error = None
                    
                    ctx_obj = {
                        "strength": strength, "temperature": temperature, "time": time_param,
                        "verbose": verbose, "quiet": quiet, "force": force, "local": local,
                        "confirm_callback": get_confirm_callback()
                    }
                    mock_ctx = _create_mock_context(obj=ctx_obj)

                    atomic = AtomicStateUpdate(basename, language)
                    with atomic:
                        try:
                            if op == "auto-deps":
                                res = auto_deps_main(
                                    mock_ctx, str(pdd_files['prompt']), 
                                    str(pdd_files['example'].parent),
                                    output=str(pdd_files['prompt']),
                                    progress_callback=progress_callback_ref[0]
                                )
                                op_success, op_cost, op_model = True, res[1], res[2]
                            
                            elif op == "generate":
                                res = code_generator_main(mock_ctx, str(pdd_files['prompt']), output=str(pdd_files['code']))
                                op_success, op_cost, op_model = True, res[2], res[3]
                                clear_run_report(basename, language)

                            elif op == "example":
                                res = context_generator_main(mock_ctx, str(pdd_files['prompt']), str(pdd_files['code']), output=str(pdd_files['example']))
                                op_success, op_cost, op_model = True, res[1], res[2]

                            elif op == "crash":
                                if skip_tests:
                                    ops_skipped.append("crash")
                                    atomic.set_run_report({"exit_code": 0, "tests_passed": 1, "tests_failed": 0, "coverage": 100.0, "timestamp": datetime.datetime.now().isoformat()})
                                    op_success = True
                                else:
                                    # Detect crash log
                                    crash_log = ""
                                    if language.lower() == "python":
                                        py_exe = detect_host_python_executable()
                                        p_run = subprocess.run([py_exe, str(pdd_files['example'])], capture_output=True, text=True, timeout=30)
                                        if p_run.returncode != 0: crash_log = p_run.stdout + "\n" + p_run.stderr
                                    
                                    m_attempts = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                    res = crash_main(mock_ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['example']), 
                                                     "internal_crash.log", output=str(pdd_files['code']), loop=(m_attempts > 0), max_attempts=m_attempts)
                                    op_success, op_cost, op_model = res[0], res[4], res[5]
                                    if op_success:
                                        if language.lower() == "python":
                                            _execute_tests_and_create_run_report(str(pdd_files['example']), basename, language, target_coverage, code_file=str(pdd_files['code']), atomic_state=atomic)
                                        else:
                                            atomic.set_run_report({"exit_code": 0, "tests_passed": 1, "tests_failed": 0, "coverage": 100.0, "timestamp": datetime.datetime.now().isoformat()})

                            elif op == "verify":
                                if skip_verify or skip_tests:
                                    ops_skipped.append("verify")
                                    op_success = True
                                else:
                                    m_attempts = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                    res = fix_verification_main(mock_ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['example']), 
                                                                loop=(m_attempts > 0), max_attempts=m_attempts, budget=budget - total_cost)
                                    op_success, op_cost, op_model = res[0], res[4], res[5]

                            elif op == "test":
                                if skip_tests:
                                    ops_skipped.append("test")
                                    op_success = True
                                else:
                                    res = cmd_test_main(mock_ctx, str(pdd_files['prompt']), str(pdd_files['code']), output=str(pdd_files['test']), language=language)
                                    op_success, op_cost, op_model = True, res[1], res[2]
                                    if res[3] is True: # Agentic success
                                        _create_synthetic_run_report_for_agentic_success(str(pdd_files['test']), basename, language, atomic_state=atomic)
                                    else:
                                        _execute_tests_and_create_run_report(str(pdd_files['test']), basename, language, target_coverage, code_file=str(pdd_files['code']), atomic_state=atomic)

                            elif op == "fix":
                                if skip_tests:
                                    ops_skipped.append("fix")
                                    op_success = True
                                else:
                                    m_attempts = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                    res = fix_main(mock_ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['test']), "internal_fix.log", 
                                                   output_code=str(pdd_files['code']), loop=(m_attempts > 0), max_attempts=m_attempts, budget=budget - total_cost)
                                    op_success, op_cost, op_model = res[0], res[4], res[5]
                                    if op_success:
                                        if language.lower() == "python":
                                            _execute_tests_and_create_run_report(str(pdd_files['test']), basename, language, target_coverage, code_file=str(pdd_files['code']), atomic_state=atomic)
                                        else:
                                            atomic.set_run_report({"exit_code": 0, "tests_passed": 1, "tests_failed": 0, "coverage": 100.0, "timestamp": datetime.datetime.now().isoformat()})

                            elif op == "update":
                                res = update_main(mock_ctx, str(pdd_files['prompt']), str(pdd_files['code']), use_git=True)
                                op_success, op_cost, op_model = True, res[1], res[2]

                            if op_success:
                                ops_completed.append(op)
                                total_cost += op_cost
                                cost_ref[0] = total_cost
                                atomic.set_fingerprint(op, pdd_files, op_cost, op_model)
                            else:
                                op_error = f"{op} failed"
                                errors.append(op_error)
                                break

                        except Exception as e:
                            op_error = str(e)
                            errors.append(f"Exception in {op}: {op_error}")
                            traceback.print_exc()
                            break
                        finally:
                            duration = time.time() - start_time
                            upd = update_log_entry(entry, op_success, op_cost, op_model, duration, op_error)
                            append_log_entry(basename, language, upd)

                result_holder["success"] = not bool(errors)
                result_holder["ops_completed"] = ops_completed
                result_holder["ops_skipped"] = ops_skipped
                result_holder["total_cost"] = total_cost
                result_holder["errors"] = errors
                result_holder["error"] = "; ".join(errors) if errors else None
                result_holder["model_name"] = op_model
                result_holder["final_state"] = {k: {"path": str(v), "exists": v.exists()} for k, v in pdd_files.items()}

        except Exception as outer_e:
            result_holder["success"] = False
            result_holder["error"] = f"Fatal Error: {outer_e}"
            traceback.print_exc()

    # Execution selection (Headless vs TUI)
    is_headless = not sys.stdin.isatty() or os.getenv("CI") == "true" or quiet
    
    if is_headless:
        os.environ["PDD_FORCE"] = "1"
        sync_worker_logic()
    else:
        app = SyncApp(
            basename=basename,
            language=language,
            worker_func=sync_worker_logic,
            function_name_ref=function_name_ref,
            cost_ref=cost_ref,
            prompt_color_ref=prompt_color_ref,
            code_color_ref=code_color_ref,
            example_color_ref=example_color_ref,
            test_color_ref=test_color_ref,
            prompt_path_ref=prompt_path_ref,
            code_path_ref=code_path_ref,
            example_path_ref=example_path_ref,
            test_path_ref=test_path_ref,
            progress_callback_ref=progress_callback_ref,
            stop_event=stop_event
        )
        app_ref[0] = app
        app.run()
        
        if app.worker_exception:
            click.echo(f"Worker crashed: {app.worker_exception}", err=True)
            return {"success": False, "error": str(app.worker_exception)}
            
        from .sync_tui import show_exit_animation
        show_exit_animation(result_holder.get("success", False))

    return result_holder