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

# PDD Module Imports
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
    """Context manager for consistent state writes using temp files."""
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language.lower()
        self.pending_report = None
        self.pending_fingerprint = None

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            if self.pending_report:
                save_run_report(self.basename, self.language, self.pending_report)
            if self.pending_fingerprint:
                # fingerprint saving is usually handled by save_fingerprint which is atomic-ish
                pass

def _safe_get_ext(language: str) -> str:
    from .get_extension import get_extension
    return get_extension(language)

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    return language.lower() != "python" or agentic_mode

def _create_mock_context(**kwargs) -> click.Context:
    ctx = click.Context(click.Command("sync"))
    ctx.obj = kwargs
    ctx.params = kwargs
    return ctx

def _display_sync_log(basename: str, language: str, verbose: bool):
    entries = load_operation_log(basename, language)
    if not entries:
        click.echo("No sync history found.")
        return
    
    click.echo(f"--- Sync Analysis for {basename} ({language}) ---")
    for entry in entries:
        timestamp = entry.get("timestamp", "N/A")
        op = entry.get("operation", "unknown")
        success = "✓" if entry.get("success") else "✗"
        cost = entry.get("actual_cost", 0.0)
        
        if verbose:
            click.echo(f"[{timestamp}] {op} {success} Cost: ${cost:.4f} Reason: {entry.get('reason')}")
            if entry.get("decision_type"):
                click.echo(f"  Decision: {entry.get('decision_type')} (Conf: {entry.get('confidence')})")
        else:
            click.echo(f"{timestamp[:19]} | {op:10} | {success} | ${cost:.4f}")

def _parse_test_output(output: str, language: str) -> Tuple[int, int, float]:
    passed, failed, coverage = 0, 0, 0.0
    lang = language.lower()
    
    if lang == "python":
        m_passed = re.search(r"(\d+) passed", output)
        m_failed = re.search(r"(\d+) failed", output)
        m_cov = re.search(r"TOTAL\s+\d+\s+\d+\s+(\d+)%", output)
        passed = int(m_passed.group(1)) if m_passed else 0
        failed = int(m_failed.group(1)) if m_failed else 0
        coverage = float(m_cov.group(1)) if m_cov else 0.0
    elif lang in ("javascript", "typescript"):
        m_passed = re.search(r"Tests:\s+(\d+) passed", output)
        m_failed = re.search(r"Tests:\s+(\d+) failed", output)
        m_cov = re.search(r"All files\s+\|\s+([\d.]+)", output)
        passed = int(m_passed.group(1)) if m_passed else 0
        failed = int(m_failed.group(1)) if m_failed else 0
        coverage = float(m_cov.group(1)) if m_cov else 0.0
    
    return passed, failed, coverage

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
    from .get_test_command import get_test_command_for_file
    
    lang_lower = language.lower()
    files_to_run = test_files if test_files else [test_file]
    
    # Python-specific path logic
    env = os.environ.copy()
    cmd = []
    
    if lang_lower == "python":
        py_exe = detect_host_python_executable()
        proj_root = _find_project_root(test_file)
        if proj_root:
            src_path = str(Path(proj_root) / "src")
            env["PYTHONPATH"] = os.pathsep.join(filter(None, [str(proj_root), src_path, env.get("PYTHONPATH", "")]))
        
        cmd = [py_exe, "-m", "pytest"] + files_to_run + ["--cov", "--cov-report=term-missing", "-c", "/dev/null"]
    else:
        # Use helper for non-python
        base_cmd = get_test_command_for_file(test_file, language=language)
        if base_cmd:
            cmd = base_cmd.split() + files_to_run
        else:
            # Fallback
            cmd = ["echo", "No test command found"]

    start_time = time.time()
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            env=env,
            timeout=120,
            start_new_session=True,
            stdin=subprocess.DEVNULL
        )
        output = proc.stdout + proc.stderr
        exit_code = proc.returncode
    except subprocess.TimeoutExpired:
        output = "Test execution timed out"
        exit_code = 1
    except Exception as e:
        output = str(e)
        exit_code = 1

    passed, failed, coverage = _parse_test_output(output, language)
    
    report = RunReport(
        timestamp=datetime.datetime.now().isoformat(),
        exit_code=exit_code,
        tests_passed=passed,
        tests_failed=failed,
        coverage=coverage,
        test_hash=calculate_sha256(test_file) if os.path.exists(test_file) else None,
        output=output
    )
    
    if atomic_state:
        atomic_state.pending_report = report.__dict__
    else:
        save_run_report(basename, lang_lower, report.__dict__)
        
    return report.__dict__

def _create_synthetic_run_report_for_agentic_success(test_file, basename, language, *, atomic_state=None):
    report = RunReport(
        timestamp=datetime.datetime.now().isoformat(),
        exit_code=0,
        tests_passed=1,
        tests_failed=0,
        coverage=100.0,
        test_hash=calculate_sha256(test_file) if os.path.exists(test_file) else "agentic_test_success"
    )
    if atomic_state:
        atomic_state.pending_report = report.__dict__
    else:
        save_run_report(basename, language.lower(), report.__dict__)
    return report.__dict__

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
    
    # Defense in depth
    target_coverage = target_coverage if target_coverage is not None else 90.0
    budget = budget if budget is not None else 20.0
    max_attempts = max_attempts if max_attempts is not None else 3

    if dry_run:
        _display_sync_log(basename, language, verbose)
        return {"success": True, "log_entries": load_operation_log(basename, language)}

    # TUI State References
    op_ref = [None]
    reason_ref = ["Initializing..."]
    cost_ref = [0.0]
    app_ref = [None]
    stop_event = threading.Event()
    
    # TUI Color and Path refs
    colors = {"prompt": "green", "code": "blue", "example": "blue", "test": "blue"}
    paths_status = {"prompt": "", "code": "", "example": "", "test": ""}
    
    worker_results = {"success": False, "error": None, "ops": [], "skipped": [], "cost": 0.0}

    def sync_worker_logic():
        start_time = time.time()
        consecutive_ops = {"fix": 0, "test": 0, "crash": 0, "test_extend": 0}
        last_ops = []
        user_confirmed_overwrite = [False]

        # Headless confirmation logic
        def get_internal_confirm(msg: str, default: bool = False) -> bool:
            if force or user_confirmed_overwrite[0]:
                return True
            if confirm_callback:
                res = confirm_callback(msg, "confirm")
                if res: user_confirmed_overwrite[0] = True
                return res
            res = click.confirm(msg, default=default)
            if res: user_confirmed_overwrite[0] = True
            return res

        try:
            with SyncLock(basename, language):
                log_event(basename, language, "lock_acquired", {"pid": os.getpid()}, "sync")
                
                while not stop_event.is_set():
                    # 1. Determine operation
                    decision = sync_determine_operation(basename, language, target_coverage, log_mode=True)
                    op, reason = decision.operation, decision.reason
                    
                    if op in ("all_synced", "nothing", "error"):
                        worker_results["success"] = (op != "error")
                        break

                    # 2. Interactive Steering
                    if not no_steer:
                        steered_op, should_abort = maybe_steer_operation(
                            op, reason, app_ref, quiet, skip_tests, skip_verify, timeout_s=steer_timeout
                        )
                        if should_abort:
                            worker_results["error"] = "Sync aborted by user steering."
                            break
                        if steered_op != op:
                            log_event(basename, language, "steering_override", {"from": op, "to": steered_op}, "sync")
                            op = steered_op

                    # Update TUI
                    op_ref[0] = op
                    reason_ref[0] = reason

                    # 3. Cycle and Budget Detection
                    if worker_results["cost"] >= budget:
                        worker_results["error"] = f"Budget of ${budget} exceeded."
                        break
                    
                    # Track repeats to break infinite loops
                    last_ops.append(op)
                    if len(last_ops) > 10: last_ops.pop(0)
                    
                    if op in consecutive_ops:
                        consecutive_ops[op] += 1
                        if op == "fix" and consecutive_ops[op] > 5: break
                        if op == "test" and consecutive_ops[op] > MAX_CONSECUTIVE_TESTS: break
                        if op == "crash" and consecutive_ops[op] > MAX_CONSECUTIVE_CRASHES: break
                    else:
                        for k in consecutive_ops: consecutive_ops[k] = 0

                    # 4. Resolve paths
                    pdd_paths = get_pdd_file_paths(basename, language, prompts_dir, code_dir, examples_dir, tests_dir)
                    
                    # 5. Execute Operation
                    ctx = _create_mock_context(
                        force=force or user_confirmed_overwrite[0],
                        strength=strength, temperature=temperature, time=time_param,
                        verbose=verbose, quiet=quiet, local=local,
                        confirm_callback=get_internal_confirm
                    )
                    
                    op_entry = create_log_entry(op, reason, "sync", decision.estimated_cost, decision.confidence, decision.decision_type)
                    op_start = time.time()
                    op_success = False
                    op_cost = 0.0
                    op_model = "unknown"
                    
                    try:
                        if op == "auto-deps":
                            # Handle auto-deps
                            modified, cost, model = auto_deps_main(ctx, str(pdd_paths["prompt"]), examples_dir)
                            op_success, op_cost, op_model = True, cost, model
                        
                        elif op == "generate":
                            code, inc, cost, model = code_generator_main(ctx, str(pdd_paths["prompt"]), str(pdd_paths["code"]))
                            op_success, op_cost, op_model = True, cost, model
                            clear_run_report(basename, language)
                            
                        elif op == "example":
                            code, cost, model = context_generator_main(ctx, str(pdd_paths["prompt"]), str(pdd_paths["code"]), str(pdd_paths["example"]))
                            op_success, op_cost, op_model = True, cost, model
                            
                        elif op == "crash":
                            if skip_tests:
                                op_success, op_cost, op_model = True, 0.0, "skipped"
                            else:
                                run_cmd = get_run_command_for_file(str(pdd_paths["example"]))
                                is_agentic = _use_agentic_path(language, agentic_mode)
                                res = crash_main(
                                    ctx, str(pdd_paths["prompt"]), str(pdd_paths["code"]), str(pdd_paths["example"]),
                                    "crash_errors.log", loop=True, max_attempts=0 if is_agentic else max_attempts, budget=budget
                                )
                                op_success, op_cost, op_model = res[0], res[4], res[5]
                                if op_success:
                                    if lang_lower == "python":
                                        _execute_tests_and_create_run_report(str(pdd_paths["example"]), basename, language, target_coverage)
                                    else:
                                        save_run_report(basename, lang_lower, {"exit_code": 0, "tests_passed": 1, "tests_failed": 0})

                        elif op == "verify":
                            if skip_verify or skip_tests:
                                op_success = True
                            else:
                                is_agentic = _use_agentic_path(language, agentic_mode)
                                res = fix_verification_main(
                                    ctx, str(pdd_paths["prompt"]), str(pdd_paths["code"]), str(pdd_paths["example"]),
                                    loop=True, max_attempts=0 if is_agentic else max_attempts, budget=budget
                                )
                                op_success, op_cost, op_model = res[0], res[4], res[5]

                        elif op == "test":
                            if skip_tests:
                                op_success = True
                            else:
                                res = cmd_test_main(ctx, str(pdd_paths["prompt"]), str(pdd_paths["code"]), str(pdd_paths["test"]), language=language)
                                op_success, op_cost, op_model = True, res[1], res[2]
                                if res[3] is True: # agentic success
                                    _create_synthetic_run_report_for_agentic_success(str(pdd_paths["test"]), basename, language)
                                else:
                                    _execute_tests_and_create_run_report(str(pdd_paths["test"]), basename, language, target_coverage)

                        elif op == "fix":
                            report = read_run_report(basename, language)
                            err_file = "test_errors.log"
                            if report and report.get("output"):
                                Path(err_file).write_text(report["output"])
                            
                            is_agentic = _use_agentic_path(language, agentic_mode)
                            res = fix_main(
                                ctx, str(pdd_paths["prompt"]), str(pdd_paths["code"]), str(pdd_paths["test"]), err_file,
                                loop=True, max_attempts=0 if is_agentic else max_attempts, budget=budget
                                )
                            op_success, op_cost, op_model = res[0], res[4], res[5]
                            if op_success:
                                if lang_lower == "python":
                                    _execute_tests_and_create_run_report(str(pdd_paths["test"]), basename, language, target_coverage)
                                else:
                                    save_run_report(basename, lang_lower, {"exit_code": 0, "tests_passed": 1, "tests_failed": 0})

                        elif op == "update":
                            res = update_main(ctx, str(pdd_paths["prompt"]), str(pdd_paths["code"]), use_git=True)
                            op_success, op_cost, op_model = True, res[1], res[2]

                        if op_success:
                            worker_results["ops"].append(op)
                            worker_results["cost"] += op_cost
                            cost_ref[0] = worker_results["cost"]
                            save_fingerprint(basename, language, op, pdd_paths, op_cost, op_model)
                        
                        entry = update_log_entry(op_entry, op_success, op_cost, op_model, time.time() - op_start)
                        append_log_entry(basename, language, entry)

                    except Exception as e:
                        worker_results["error"] = str(e)
                        entry = update_log_entry(op_entry, False, 0.0, "error", 0.0, str(e))
                        append_log_entry(basename, language, entry)
                        break

                log_event(basename, language, "lock_released", {}, "sync")

        except Exception as e:
            worker_results["error"] = f"Worker loop error: {str(e)}"
            if verbose: traceback.print_exc()

    # Determine execution mode (TUI or Headless)
    is_headless = not sys.stdin.isatty() or os.getenv("CI") == "true" or quiet
    
    if is_headless:
        os.environ["PDD_FORCE"] = "1"
        sync_worker_logic()
    else:
        app = SyncApp(worker_func=sync_worker_logic)
        # Link refs to TUI app
        app.op_ref = op_ref
        app.reason_ref = reason_ref
        app.cost_ref = cost_ref
        app.basename = basename
        app.language = language
        app_ref[0] = app
        
        try:
            app.run()
        except Exception as e:
            click.echo(f"TUI Crash: {e}", err=True)
            if verbose: traceback.print_exc()
        
        from .sync_tui import show_exit_animation
        if not quiet:
            show_exit_animation(worker_results["success"], worker_results["ops"], worker_results["cost"])

    # Final cleanup and return
    return {
        "success": worker_results["success"],
        "operations_completed": worker_results["ops"],
        "total_cost": worker_results["cost"],
        "error": worker_results["error"],
        "final_state": {} # Populate if needed for caller
    }

def _find_project_root(start_path: str) -> Optional[Path]:
    """Helper to find the root directory containing .pdd or .git."""
    curr = Path(start_path).resolve()
    if curr.is_file(): curr = curr.parent
    for parent in [curr] + list(curr.parents):
        if (parent / ".pdd").exists() or (parent / ".git").exists():
            return parent
    return None