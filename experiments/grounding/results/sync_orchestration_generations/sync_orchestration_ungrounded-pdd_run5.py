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
from .get_test_command import get_test_command_for_file
from .pytest_output import extract_failing_files_from_output, _find_project_root
from . import DEFAULT_STRENGTH

# Constants
MAX_CONSECUTIVE_TESTS = 3
MAX_TEST_EXTEND_ATTEMPTS = 2
MAX_CONSECUTIVE_CRASHES = 3
MAX_CYCLE_REPEATS = 2

class AtomicStateUpdate:
    """Context manager for consistent state writes (Fingerprint + RunReport)."""
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
                # We expect dict format for internal logic or dataclass
                data = self.pending_fingerprint
                save_fingerprint(
                    self.basename, self.language, 
                    data['operation'], data['paths'], 
                    data['cost'], data['model']
                )

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Returns True if we should bypass iterative loops for agentic handling."""
    return language.lower() != "python" or agentic_mode

def _create_synthetic_run_report_for_agentic_success(test_file, basename, language, *, atomic_state=None):
    """Creates a successful RunReport for agentic operations that verify themselves."""
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
        atomic_state.pending_run_report = report_data
    else:
        save_run_report(basename, language.lower(), report_data)

def _parse_test_output(output: str, language: str) -> Tuple[int, int, float]:
    """Parses output from various test runners."""
    passed, failed, coverage = 0, 0, 0.0
    lang = language.lower()
    
    if lang == "python":
        # Pytest logic
        m = re.search(r"(\d+) passed", output)
        if m: passed = int(m.group(1))
        m = re.search(r"(\d+) failed", output)
        if m: failed = int(m.group(1))
        m = re.search(r"TOTAL\s+\d+\s+\d+\s+(\d+)%", output)
        if m: coverage = float(m.group(1))
    elif lang in ("javascript", "typescript"):
        # Jest/Vitest
        m = re.search(r"Tests:\s+(\d+) passed,\s+(\d+) total", output)
        if m: 
            passed = int(m.group(1))
            total = int(m.group(2))
            failed = total - passed
        m = re.search(r"All files\s+\|\s+([\d.]+)", output)
        if m: coverage = float(m.group(1))
    
    return passed, failed, coverage

def _execute_tests_and_create_run_report(test_file, basename, language, target_coverage, *, code_file=None, atomic_state=None, test_files=None):
    """Executes tests and saves a RunReport."""
    lang_lower = language.lower()
    cmd = get_test_command_for_file(test_file, language=lang_lower)
    if not cmd:
        return False
    
    # Python specific coverage logic
    env = os.environ.copy()
    if lang_lower == "python":
        root = _find_project_root(test_file)
        if root:
            src = str(Path(root) / "src")
            env["PYTHONPATH"] = f"{root}:{src}:{env.get('PYTHONPATH', '')}"
            cmd += f" --rootdir {root} -c /dev/null"
        
        if code_file:
            module_path = Path(code_file).stem
            cmd += f" --cov={module_path} --cov-report=term-missing"

    try:
        proc = subprocess.run(
            cmd, shell=True, capture_output=True, text=True, env=env, 
            start_new_session=True, stdin=subprocess.DEVNULL
        )
        passed, failed, coverage = _parse_test_output(proc.stdout + proc.stderr, language)
        
        test_hashes = {}
        target_files = test_files if test_files else [test_file]
        for tf in target_files:
            p = Path(tf)
            if p.exists():
                test_hashes[str(p)] = calculate_sha256(p)

        report = {
            "timestamp": datetime.datetime.now().isoformat(),
            "exit_code": proc.returncode,
            "tests_passed": passed,
            "tests_failed": failed,
            "coverage": coverage,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
            "test_file_hashes": test_hashes
        }
        
        if atomic_state:
            atomic_state.pending_run_report = report
        else:
            save_run_report(basename, lang_lower, report)
        return True
    except Exception:
        return False

def _display_sync_log(basename: str, language: str, verbose: bool):
    """Formats and displays the sync history log."""
    entries = load_operation_log(basename, language)
    if not entries:
        click.echo("No sync history found.")
        return

    click.echo(f"--- Sync History for {basename} ({language}) ---")
    for e in entries:
        ts = e.get('timestamp', 'N/A')[:19]
        op = e.get('operation', 'unknown')
        success = "✓" if e.get('success') else "✗"
        cost = e.get('actual_cost', 0.0)
        
        msg = f"[{ts}] {op:10} {success} ${cost:.4f}"
        if verbose:
            msg += f" | Model: {e.get('model')} | Reason: {e.get('reason')}"
        click.echo(msg)

def _create_mock_context(**kwargs):
    """Creates a mock Click context."""
    class MockCtx:
        def __init__(self, params):
            self.obj = params
            self.params = params
        def ensure_object(self, _): return self.obj
    return MockCtx(kwargs)

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
    """Orchestrates the complete PDD sync workflow with TUI and state management."""
    
    # Defense in depth for None values from CLI
    target_coverage = target_coverage if target_coverage is not None else 90.0
    budget = budget if budget is not None else 20.0
    max_attempts = max_attempts if max_attempts is not None else 3
    
    lang_lower = language.lower()

    if dry_run:
        _display_sync_log(basename, lang_lower, verbose)
        return {"success": True, "log_entries": load_operation_log(basename, lang_lower)}

    # Headless detection
    is_headless = not sys.stdin.isatty() or os.environ.get("CI") == "true" or quiet
    if is_headless:
        os.environ["PDD_FORCE"] = "1"

    # Orchestration State
    state = {
        "success": False,
        "operations_completed": [],
        "skipped_operations": [],
        "total_cost": 0.0,
        "total_time": 0.0,
        "errors": [],
        "model_name": "None",
    }
    
    # TUI Refs
    op_ref = ["init"]
    cost_ref = [0.0]
    app_ref = [None]
    progress_ref = [0.0]
    paths_ref = [{}]
    
    start_time = time.time()
    stop_event = threading.Event()

    def sync_worker_logic():
        consecutive_ops = {"fix": 0, "test": 0, "crash": 0, "test_extend": 0}
        last_ops = []
        user_confirmed_overwrite = [False]

        def get_confirm_wrapper():
            def wrapper(msg, default):
                if user_confirmed_overwrite[0]: return True
                res = confirm_callback(msg, default) if confirm_callback else click.confirm(msg, default=default)
                if res: user_confirmed_overwrite[0] = True
                return res
            return wrapper

        try:
            with SyncLock(basename, lang_lower) as lock:
                log_event(basename, lang_lower, "lock_acquired", {"basename": basename}, "sync")
                
                while not stop_event.is_set():
                    # Check Budget
                    if state["total_cost"] >= budget:
                        state["errors"].append(f"Budget exceeded: ${state['total_cost']:.2f} >= ${budget:.2f}")
                        break
                    
                    # Determine next step
                    decision = sync_determine_operation(basename, lang_lower, target_coverage, log_mode=False)
                    op = decision.operation
                    
                    # Cycle Detection
                    last_ops.append(op)
                    if len(last_ops) > 10: last_ops.pop(0)
                    
                    # Logic to break infinite loops
                    if op == "all_synced" or op == "nothing":
                        state["success"] = True
                        break
                    
                    # Steering
                    if not no_steer and not is_headless:
                        steered_op, should_abort = maybe_steer_operation(
                            op, decision.reason, app_ref[0], quiet, skip_tests, skip_verify, timeout_s=steer_timeout
                        )
                        if should_abort:
                            state["errors"].append("User aborted via steering.")
                            break
                        if steered_op != op:
                            log_event(basename, lang_lower, "steering_override", {"from": op, "to": steered_op}, "sync")
                            op = steered_op

                    op_ref[0] = op
                    paths = get_pdd_file_paths(basename, lang_lower)
                    paths_ref[0] = paths
                    
                    # Setup Click Context
                    ctx = _create_mock_context(
                        verbose=verbose, quiet=quiet, local=local, 
                        force=force or user_confirmed_overwrite[0],
                        strength=strength, temperature=temperature, time=time_param,
                        confirm_callback=get_confirm_wrapper()
                    )

                    log_entry = create_log_entry(op, decision.reason, "sync", decision.estimated_cost, decision.confidence, decision.decision_type)
                    op_start = time.time()
                    
                    op_result = None
                    try:
                        # Execution Router
                        if op == "auto-deps":
                            # Auto-deps logic
                            op_result = auto_deps_main(ctx, str(paths['prompt']), str(Path(examples_dir)), output=str(paths['prompt']), force_scan=False)
                        
                        elif op == "generate":
                            clear_run_report(basename, lang_lower)
                            op_result = code_generator_main(ctx, str(paths['prompt']), output=str(paths['code']))

                        elif op == "example":
                            op_result = context_generator_main(ctx, str(paths['prompt']), str(paths['code']), output=str(paths['example']))

                        elif op == "crash":
                            if skip_tests or skip_verify:
                                state["skipped_operations"].append(op)
                                _create_synthetic_run_report_for_agentic_success(paths['example'], basename, lang_lower)
                                continue

                            # Agentic mode logic
                            cur_max = 0 if _use_agentic_path(lang_lower, agentic_mode) else max_attempts
                            op_result = crash_main(ctx, str(paths['prompt']), str(paths['code']), str(paths['example']), "crash.log", loop=True, max_attempts=cur_max, budget=budget-state["total_cost"])
                            if op_result[0]:
                                _execute_tests_and_create_run_report(paths['example'], basename, lang_lower, target_coverage, code_file=paths['code'])

                        elif op == "verify":
                            if skip_verify:
                                state["skipped_operations"].append(op)
                                continue
                            cur_max = 0 if _use_agentic_path(lang_lower, agentic_mode) else max_attempts
                            op_result = fix_verification_main(ctx, str(paths['prompt']), str(paths['code']), str(paths['example']), loop=True, max_attempts=cur_max, budget=budget-state["total_cost"])
                            if op_result[0]:
                                _execute_tests_and_create_run_report(paths['example'], basename, lang_lower, target_coverage, code_file=paths['code'])

                        elif op == "test":
                            if skip_tests:
                                state["skipped_operations"].append(op)
                                continue
                            # test returns (content, cost, model, agentic_success)
                            res = cmd_test_main(ctx, str(paths['prompt']), str(paths['code']), output=str(paths['test']), language=lang_lower)
                            op_result = res
                            if res[3] is True: # agentic success
                                _create_synthetic_run_report_for_agentic_success(paths['test'], basename, lang_lower)
                            else:
                                _execute_tests_and_create_run_report(paths['test'], basename, lang_lower, target_coverage, code_file=paths['code'])

                        elif op == "fix":
                            cur_max = 0 if _use_agentic_path(lang_lower, agentic_mode) else max_attempts
                            op_result = fix_main(ctx, str(paths['prompt']), str(paths['code']), str(paths['test']), "fix_errors.log", loop=True, max_attempts=cur_max, budget=budget-state["total_cost"])
                            if op_result[0]:
                                _execute_tests_and_create_run_report(paths['test'], basename, lang_lower, target_coverage, code_file=paths['code'])

                        elif op == "update":
                            op_result = update_main(ctx, str(paths['prompt']), str(paths['code']), use_git=True)

                        # Handle Results
                        if op_result:
                            res_success = op_result[0] if isinstance(op_result, (tuple, list)) else True
                            # Extract cost/model from varying tuple lengths
                            res_cost = op_result[1] if op == "test" else op_result[-2]
                            res_model = op_result[2] if op == "test" else op_result[-1]
                            
                            state["total_cost"] += res_cost
                            cost_ref[0] = state["total_cost"]
                            state["model_name"] = res_model
                            
                            updated_log = update_log_entry(log_entry, res_success, res_cost, res_model, time.time()-op_start)
                            append_log_entry(basename, lang_lower, updated_log)
                            
                            if res_success:
                                save_fingerprint(basename, lang_lower, op, paths, res_cost, res_model)
                                state["operations_completed"].append(op)
                            else:
                                state["errors"].append(f"Operation {op} failed.")
                                break
                    except Exception as e:
                        state["errors"].append(f"Error in {op}: {str(e)}")
                        break

        except Exception as e:
            state["errors"].append(f"Sync failed: {str(e)}")
            if verbose: traceback.print_exc()

    # Execution Entry
    if is_headless:
        sync_worker_logic()
    else:
        app = SyncApp(basename=basename, language=lang_lower, worker_func=sync_worker_logic)
        app_ref[0] = app
        app.run()
        if app.worker_exception:
            state["errors"].append(f"Worker crashed: {app.worker_exception}")
        if not state["success"] and not state["errors"]:
            return {"success": False, "error": "Interrupted by user"}

    state["total_time"] = time.time() - start_time
    state["error"] = "; ".join(state["errors"]) if state["errors"] else None
    
    if not quiet and not is_headless:
        from .sync_tui import show_exit_animation
        show_exit_animation(state["success"], state["total_cost"], state["total_time"])

    return state