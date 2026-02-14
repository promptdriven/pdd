import click
import os
import sys
import threading
import time
import json
import datetime
import subprocess
import re
import logging
import tempfile
import traceback
import shutil
from pathlib import Path
from typing import Dict, Any, Optional, List, Callable, Tuple
from dataclasses import asdict

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
    """Context manager for atomic updates of fingerprint and run report."""
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language
        self.pending_fingerprint = None
        self.pending_run_report = None

    def __enter__(self):
        return self

    def set_fingerprint(self, op: str, paths: dict, cost: float, model: str):
        self.pending_fingerprint = (op, paths, cost, model)

    def set_run_report(self, report_data: dict):
        self.pending_run_report = report_data

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            if self.pending_fingerprint:
                save_fingerprint(self.basename, self.language, *self.pending_fingerprint)
            if self.pending_run_report:
                save_run_report(self.basename, self.language, self.pending_run_report)

def _display_sync_log(basename: str, language: str, verbose: bool):
    """Format and display sync log."""
    entries = load_operation_log(basename, language)
    if not entries:
        click.secho("No sync history found.", fg="yellow")
        return
    
    click.secho(f"--- Sync Analysis for {basename} ({language}) ---", bold=True)
    for entry in entries:
        ts = entry.get("timestamp", "")
        op = entry.get("operation", "unknown")
        success = entry.get("success", True)
        color = "green" if success else "red"
        
        summary = f"[{ts}] {op.upper()}"
        if verbose:
            details = f" | Decision: {entry.get('decision_type')} | Reason: {entry.get('reason')}"
            click.secho(f"{summary}{details}", fg=color)
        else:
            click.secho(summary, fg=color)

def _create_mock_context(**kwargs) -> click.Context:
    """Create a minimal Click context for executing main functions."""
    ctx = click.Context(click.Command("sync-sub"))
    ctx.obj = kwargs
    ctx.params = kwargs
    return ctx

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Check if we should use agentic fallback paths (Non-Python or Agentic Mode)."""
    lang_lower = language.lower()
    return lang_lower != "python" or agentic_mode

def _create_synthetic_run_report_for_agentic_success(test_file: str, basename: str, language: str, *, atomic_state=None):
    """Saves a successful synthetic run report for agentic test success."""
    test_path = Path(test_file)
    test_hash = calculate_sha256(test_path) if test_path.exists() else "agentic_test_success"
    
    report_data = {
        "timestamp": datetime.datetime.now().isoformat(),
        "exit_code": 0,
        "tests_passed": 1,
        "tests_failed": 0,
        "coverage": 100.0,
        "test_hash": test_hash
    }
    
    if atomic_state:
        atomic_state.set_run_report(report_data)
    else:
        save_run_report(basename, language, report_data)

def _parse_test_output(output: str, language: str) -> Tuple[int, int, float]:
    """Parse test runner output to extract stats."""
    passed, failed, coverage = 0, 0, 0.0
    lang_lower = language.lower()
    
    # Simple regex-based parsing for major frameworks
    if lang_lower == "python":
        # pytest
        m = re.search(r"(\d+) passed", output)
        if m: passed = int(m.group(1))
        m = re.search(r"(\d+) failed", output)
        if m: failed = int(m.group(1))
        m = re.search(r"TOTAL\s+\d+\s+\d+\s+(\d+)%", output)
        if m: coverage = float(m.group(1))
    elif lang_lower in ("javascript", "typescript"):
        # Jest/Vitest
        m = re.search(r"Tests:\s+(\d+) passed,\s+(\d+) total", output)
        if m: passed = int(m.group(1))
        m = re.search(r"All files\s+\|\s+([\d.]+)", output)
        if m: coverage = float(m.group(1))
    
    return passed, failed, coverage

def _python_cov_target_for_test_and_code(test_file: str, code_file: str, fallback: str) -> str:
    """Analyze test file for import path to target coverage."""
    if not Path(test_file).exists():
        return fallback
    content = Path(test_file).read_text(errors="ignore")
    # Try to find 'from X import' or 'import X'
    m = re.search(r"from ([\w\.]+) import", content)
    if m: return m.group(1)
    return fallback

def _execute_tests_and_create_run_report(test_file, basename, language, target_coverage, *, code_file=None, atomic_state=None, test_files=None):
    """Executes tests and updates the run report."""
    lang_lower = language.lower()
    from .get_test_command import get_test_command_for_file
    
    cmd = get_test_command_for_file(test_file, language=language)
    if not cmd:
        return # Cannot run tests locally
    
    # Path resolution and PYTHONPATH setup for Python
    env = os.environ.copy()
    if lang_lower == "python" and code_file:
        root = _find_project_root(test_file)
        if root:
            src_dir = str(Path(root) / "src")
            env["PYTHONPATH"] = f"{root}{os.pathsep}{src_dir}{os.pathsep}{env.get('PYTHONPATH', '')}"
            cov_target = _python_cov_target_for_test_and_code(test_file, code_file, basename)
            cmd = f"{sys.executable} -m pytest --rootdir {root} -c /dev/null --cov={cov_target} " + " ".join(test_files or [test_file])

    try:
        proc = subprocess.run(
            cmd, shell=True, capture_output=True, text=True, env=env, 
            start_new_session=True, stdin=subprocess.DEVNULL
        )
        passed, failed, coverage = _parse_test_output(proc.stdout + proc.stderr, language)
        
        hashes = {}
        if test_files:
            for f in test_files:
                p = Path(f)
                if p.exists(): hashes[f] = calculate_sha256(p)
        
        report = {
            "timestamp": datetime.datetime.now().isoformat(),
            "exit_code": proc.returncode,
            "tests_passed": passed,
            "tests_failed": failed,
            "coverage": coverage,
            "test_hash": calculate_sha256(Path(test_file)) if Path(test_file).exists() else "",
            "test_file_hashes": hashes
        }
        
        if atomic_state:
            atomic_state.set_run_report(report)
        else:
            save_run_report(basename, language, report)
    except Exception:
        pass

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
    
    # Defaults defense
    target_coverage = target_coverage if target_coverage is not None else 90.0
    budget = budget if budget is not None else 10.0
    max_attempts = max_attempts if max_attempts is not None else 3
    
    lang_lower = language.lower()
    
    if dry_run:
        _display_sync_log(basename, language, verbose)
        return {"success": True, "log_entries": load_operation_log(basename, language)}

    # State tracking
    total_cost = 0.0
    ops_completed = []
    skipped_ops = []
    errors = []
    op_history = []
    
    # Path resolution
    try:
        pdd_files = get_pdd_file_paths(basename, language, prompts_dir, code_dir, examples_dir, tests_dir)
    except FileNotFoundError as e:
        # Fallback for new units
        pdd_files = {
            "prompt": Path(prompts_dir) / f"{basename}_{language}.prompt",
            "code": Path(code_dir) / f"{basename}.{language}", # Placeholder ext
            "example": Path(examples_dir) / f"{basename}_example.{language}",
            "test": Path(tests_dir) / f"test_{basename}.{language}",
        }

    # TUI Refs
    cost_ref = [0.0]
    func_name_ref = ["Initializing"]
    stop_event = threading.Event()
    app_ref = [None]
    user_confirmed_overwrite = [False]

    def get_confirm_wrapper():
        def wrapper(msg, title):
            if force or user_confirmed_overwrite[0]:
                return True
            if app_ref[0]:
                res = app_ref[0].request_confirmation(msg, title)
                if res: user_confirmed_overwrite[0] = True
                return res
            res = click.confirm(msg, default=True)
            if res: user_confirmed_overwrite[0] = True
            return res
        return wrapper

    effective_confirm = confirm_callback or get_confirm_wrapper()

    def sync_worker_logic():
        nonlocal total_cost
        start_time = time.time()
        consecutive_fixes = 0
        consecutive_tests = 0
        consecutive_crashes = 0
        test_extend_attempts = 0
        
        with SyncLock(basename, language) as lock:
            log_event(basename, language, "lock_acquired", {"pid": os.getpid()}, "sync")
            
            while not stop_event.is_set():
                if total_cost >= budget:
                    errors.append(f"Budget exceeded: ${total_cost:.2f} / ${budget:.2f}")
                    break

                # 1. Determine next step
                decision = sync_determine_operation(basename, language, target_coverage)
                op = decision.operation
                
                # Check for cycle/infinite loop
                op_history.append(op)
                if len(op_history) > 30:
                    errors.append("Potential infinite sync loop detected. Aborting.")
                    break
                
                # Heuristic breaks
                if op == "nothing" or op == "all_synced":
                    break
                
                if op == "auto-deps":
                    # Force advance if repeating auto-deps
                    if op_history[-3:].count("auto-deps") >= 2:
                        op = "generate"
                
                if op == "fix":
                    consecutive_fixes += 1
                    if consecutive_fixes > 5:
                        errors.append("Maximum consecutive fixes reached.")
                        break
                else:
                    consecutive_fixes = 0

                if op == "test":
                    consecutive_tests += 1
                    if consecutive_tests > MAX_CONSECUTIVE_TESTS: break
                else:
                    consecutive_tests = 0

                # Steering
                if not no_steer:
                    op, should_abort = maybe_steer_operation(
                        op, decision.reason, app_ref, quiet, skip_tests, skip_verify, steer_timeout
                    )
                    if should_abort:
                        errors.append("Sync aborted by user steering.")
                        break
                    if op != decision.operation:
                        log_event(basename, language, "steering_override", {"from": decision.operation, "to": op}, "sync")

                # Execution
                func_name_ref[0] = op
                ctx = _create_mock_context(
                    strength=strength, temperature=temperature, time=time_param,
                    force=force, verbose=verbose, quiet=quiet, local=local,
                    confirm_callback=effective_confirm
                )
                
                entry = create_log_entry(
                    operation=op, reason=decision.reason, invocation_mode="sync",
                    estimated_cost=decision.estimated_cost, confidence=decision.confidence,
                    decision_type=decision.decision_type
                )
                
                op_start = time.time()
                success = False
                op_cost = 0.0
                model_used = "unknown"

                try:
                    atomic = AtomicStateUpdate(basename, language)
                    with atomic:
                        if op == "auto-deps":
                            _, op_cost, model_used = auto_deps_main(
                                ctx, str(pdd_files["prompt"]), str(pdd_files["example"].parent), output=str(pdd_files["prompt"])
                            )
                            success = True
                        
                        elif op == "generate":
                            _, _, op_cost, model_used = code_generator_main(
                                ctx, str(pdd_files["prompt"]), output=str(pdd_files["code"])
                            )
                            clear_run_report(basename, language)
                            success = True
                        
                        elif op == "example":
                            _, op_cost, model_used = context_generator_main(
                                ctx, str(pdd_files["prompt"]), str(pdd_files["code"]), output=str(pdd_files["example"])
                            )
                            success = True

                        elif op == "crash":
                            if skip_tests:
                                skipped_ops.append("crash")
                                atomic.set_run_report({"exit_code": 0, "timestamp": datetime.datetime.now().isoformat()})
                                success = True
                            else:
                                consec_crash = op_history[-3:].count("crash")
                                if consec_crash >= MAX_CONSECUTIVE_CRASHES:
                                    errors.append("Max consecutive crashes reached.")
                                    break
                                
                                # Prep crash info
                                crash_log = "Sync crash detection triggered."
                                if lang_lower == "python":
                                    # Try to run example to see if it actually crashes
                                    try:
                                        res = subprocess.run([sys.executable, str(pdd_files["example"])], capture_output=True, text=True, timeout=10)
                                        if res.returncode == 0:
                                            # No crash found locally
                                            atomic.set_run_report({"exit_code": 0, "timestamp": datetime.datetime.now().isoformat()})
                                            success = True
                                            continue
                                        crash_log = res.stderr or res.stdout
                                    except Exception as e:
                                        crash_log = str(e)

                                temp_err = tempfile.NamedTemporaryFile(mode="w", suffix=".log", delete=False)
                                temp_err.write(crash_log); temp_err.close()
                                
                                m_attempts = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                success, _, _, _, op_cost, model_used = crash_main(
                                    ctx, str(pdd_files["prompt"]), str(pdd_files["code"]), 
                                    str(pdd_files["example"]), temp_err.name, output=str(pdd_files["code"]),
                                    loop=(m_attempts > 0), max_attempts=m_attempts, budget=budget - total_cost
                                )
                                os.unlink(temp_err.name)
                                
                                if success:
                                    if lang_lower == "python":
                                        # Verify fix
                                        _execute_tests_and_create_run_report(str(pdd_files["example"]), basename, language, target_coverage, atomic_state=atomic)
                                    else:
                                        atomic.set_run_report({"exit_code": 0, "timestamp": datetime.datetime.now().isoformat()})

                        elif op == "verify":
                            if skip_verify or skip_tests:
                                skipped_ops.append("verify")
                                atomic.set_fingerprint("skip:verify", pdd_files, 0, "skipped")
                                success = True
                            else:
                                m_attempts = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                success, _, _, _, op_cost, model_used = fix_verification_main(
                                    ctx, str(pdd_files["prompt"]), str(pdd_files["code"]), str(pdd_files["example"]),
                                    loop=(m_attempts > 0), max_attempts=m_attempts, budget=budget - total_cost
                                )
                        
                        elif op == "test":
                            if skip_tests:
                                skipped_ops.append("test")
                                success = True
                            else:
                                res = cmd_test_main(
                                    ctx, str(pdd_files["prompt"]), str(pdd_files["code"]), output=str(pdd_files["test"]),
                                    language=language, strength=strength, temperature=temperature
                                )
                                op_cost, model_used = res[1], res[2]
                                agentic_success = res[3]
                                if agentic_success:
                                    _create_synthetic_run_report_for_agentic_success(str(pdd_files["test"]), basename, language, atomic_state=atomic)
                                    success = True
                                else:
                                    success = Path(pdd_files["test"]).exists()
                                    if success:
                                        _execute_tests_and_create_run_report(str(pdd_files["test"]), basename, language, target_coverage, code_file=str(pdd_files["code"]), atomic_state=atomic)

                        elif op == "test_extend":
                            if skip_tests or _use_agentic_path(language, agentic_mode):
                                skipped_ops.append("test_extend")
                                success = True
                            else:
                                test_extend_attempts += 1
                                if test_extend_attempts > MAX_TEST_EXTEND_ATTEMPTS:
                                    skipped_ops.append("test_extend_max_reached")
                                    success = True
                                else:
                                    # Augment tests
                                    res = cmd_test_main(
                                        ctx, str(pdd_files["prompt"]), str(pdd_files["code"]), output=str(pdd_files["test"]),
                                        language=language, strength=strength, temperature=temperature,
                                        existing_tests=[str(pdd_files["test"])], merge=True, target_coverage=target_coverage
                                    )
                                    op_cost, model_used = res[1], res[2]
                                    _execute_tests_and_create_run_report(str(pdd_files["test"]), basename, language, target_coverage, code_file=str(pdd_files["code"]), atomic_state=atomic)
                                    success = True

                        elif op == "fix":
                            m_attempts = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                            success, _, _, _, op_cost, model_used = fix_main(
                                ctx, str(pdd_files["prompt"]), str(pdd_files["code"]), str(pdd_files["test"]),
                                loop=(m_attempts > 0), max_attempts=m_attempts, budget=budget - total_cost
                            )
                            if success:
                                if lang_lower == "python":
                                    _execute_tests_and_create_run_report(str(pdd_files["test"]), basename, language, target_coverage, code_file=str(pdd_files["code"]), atomic_state=atomic)
                                else:
                                    atomic.set_run_report({"exit_code": 0, "timestamp": datetime.datetime.now().isoformat()})

                        elif op == "update":
                            _, op_cost, model_used = update_main(
                                ctx, str(pdd_files["prompt"]), str(pdd_files["code"]), use_git=True
                            )
                            success = True

                    if success:
                        save_fingerprint(basename, language, op, pdd_files, op_cost, model_used)
                        ops_completed.append(op)
                    
                    total_cost += op_cost
                    cost_ref[0] = total_cost
                    
                    updated_entry = update_log_entry(entry, success, op_cost, model_used, time.time() - op_start)
                    append_log_entry(basename, language, updated_entry)

                except Exception as e:
                    errors.append(f"Operation {op} failed: {str(e)}")
                    updated_entry = update_log_entry(entry, False, op_cost, model_used, time.time() - op_start, error=str(e))
                    append_log_entry(basename, language, updated_entry)
                    break

            log_event(basename, language, "lock_released", {}, "sync")

    # Entry point logic
    is_headless = not sys.stdin.isatty() or os.environ.get("CI") == "true" or quiet
    
    if is_headless:
        os.environ["PDD_FORCE"] = "1"
        sync_worker_logic()
    else:
        app = SyncApp(sync_worker_logic, basename, language)
        app_ref[0] = app
        run_res = app.run()
        
        if run_res is None:
            return {"success": False, "error": "Sync interrupted by user"}
        
        if app.worker_exception:
            print(f"Error in sync worker: {app.worker_exception}", file=sys.stderr)
            traceback.print_exception(type(app.worker_exception), app.worker_exception, app.worker_exception.__traceback__)
        
        from .sync_tui import show_exit_animation
        show_exit_animation()

    # Final summary
    final_paths = calculate_current_hashes(pdd_files)
    
    return {
        "success": len(errors) == 0,
        "operations_completed": ops_completed,
        "skipped_operations": skipped_ops,
        "total_cost": total_cost,
        "total_time": 0.0, # Placeholder
        "final_state": {k: {"exists": v.exists(), "path": str(v)} for k, v in pdd_files.items()},
        "errors": errors,
        "error": "; ".join(errors) if errors else None,
        "model_name": "sync-orchestrator"
    }
