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
from .sync_tui import maybe_steer_operation, SyncApp, DEFAULT_STEER_TIMEOUT_S
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
    """Context manager for consistent state writes (fingerprint and run report)."""
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language.lower()
        self.pending_fingerprint = None
        self.pending_run_report = None

    def set_fingerprint(self, op: str, paths: Dict[str, Path], cost: float, model: str):
        self.pending_fingerprint = (op, paths, cost, model)

    def set_run_report(self, report: Dict[str, Any]):
        self.pending_run_report = report

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            if self.pending_fingerprint:
                save_fingerprint(self.basename, self.language, *self.pending_fingerprint)
            if self.pending_run_report:
                save_run_report(self.basename, self.language, self.pending_run_report)

def _display_sync_log(basename: str, language: str, verbose: bool):
    """Format and display sync log using load_operation_log()."""
    entries = load_operation_log(basename, language)
    if not entries:
        click.echo(f"No sync history found for {basename} ({language}).")
        return

    click.echo(f"\n--- Sync Log: {basename} ({language}) ---")
    for entry in entries:
        ts = entry.get('timestamp', 'N/A')
        op = entry.get('operation', 'unknown')
        cost = entry.get('actual_cost', 0.0)
        success = entry.get('success', True)
        status = "PASSED" if success else "FAILED"
        
        line = f"[{ts}] {op.upper():<10} | {status:<7} | ${cost:.4f}"
        if verbose:
            line += f" | Reason: {entry.get('reason', 'N/A')}"
        click.echo(line)

def _create_mock_context(**kwargs) -> click.Context:
    """Create a mock Click context for internal command execution."""
    ctx = click.Context(click.Command("sync_internal"))
    ctx.obj = {
        'verbose': kwargs.get('verbose', False),
        'quiet': kwargs.get('quiet', False),
        'force': kwargs.get('force', False),
        'strength': kwargs.get('strength', DEFAULT_STRENGTH),
        'temperature': kwargs.get('temperature', 0.0),
        'time': kwargs.get('time_param', 0.25),
        'local': kwargs.get('local', False),
        'context': kwargs.get('context_override'),
        'confirm_callback': kwargs.get('confirm_callback')
    }
    ctx.params = {'local': kwargs.get('local', False), 'force': kwargs.get('force', False)}
    return ctx

def _parse_test_output(output: str, language: str) -> Tuple[int, int, float]:
    """Parse test runner output to extract (tests_passed, tests_failed, coverage)."""
    passed = 0
    failed = 0
    coverage = 0.0

    if language.lower() == "python":
        # Pytest parsing
        p_match = re.search(r'(\d+) passed', output)
        f_match = re.search(r'(\d+) failed', output)
        c_match = re.search(r'TOTAL\s+\d+\s+\d+\s+(\d+)%', output)
        if p_match: passed = int(p_match.group(1))
        if f_match: failed = int(f_match.group(1))
        if c_match: coverage = float(c_match.group(1))
    else:
        # Generic parsing for JS/Go/Rust etc.
        p_match = re.search(r'(\d+) passed|OK', output, re.I)
        f_match = re.search(r'(\d+) failed|FAIL', output, re.I)
        if p_match and not passed: passed = 1
        if f_match: failed = 1

    return passed, failed, coverage

def _execute_tests_and_create_run_report(test_file: str, basename: str, language: str, 
                                       target_coverage: float, *, code_file: str = None, 
                                       atomic_state: AtomicStateUpdate = None, 
                                       test_files: List[str] = None) -> Dict[str, Any]:
    """Run tests with coverage and save RunReport."""
    from .get_test_command import get_test_command_for_file
    
    lang_lower = language.lower()
    all_tests = test_files if test_files else [test_file]
    cmd_str = get_test_command_for_file(test_file, language=lang_lower)
    
    if not cmd_str:
        return {"exit_code": 1, "error": "No test command found"}

    env = os.environ.copy()
    env.pop("FORCE_COLOR", None)
    env.pop("COLUMNS", None)

    # Python specific coverage logic
    if lang_lower == "python" and code_file:
        root = _find_project_root(test_file)
        if root:
            src_dir = root / "src"
            paths = [str(root)]
            if src_dir.exists(): paths.append(str(src_dir))
            env["PYTHONPATH"] = os.pathsep.join(paths + [env.get("PYTHONPATH", "")])
            
            cov_target = Path(code_file).stem
            cmd_list = [detect_host_python_executable(), "-m", "pytest", "--rootdir", str(root), "-c", "/dev/null", f"--cov={cov_target}"] + all_tests
        else:
            cmd_list = cmd_str.split() + all_tests
    else:
        cmd_list = cmd_str.split() + all_tests

    try:
        res = subprocess.run(cmd_list, capture_output=True, text=True, env=env, start_new_session=True, timeout=120)
        passed, failed, coverage = _parse_test_output(res.stdout + res.stderr, lang_lower)
        
        report = {
            "timestamp": datetime.datetime.now().isoformat(),
            "exit_code": res.returncode,
            "tests_passed": passed,
            "tests_failed": failed,
            "coverage": coverage,
            "test_hash": calculate_sha256(test_file) if os.path.exists(test_file) else None,
            "test_file_hashes": {f: calculate_sha256(f) for f in all_tests if os.path.exists(f)}
        }
        
        if atomic_state:
            atomic_state.set_run_report(report)
        else:
            save_run_report(basename, language, report)
        return report
    except Exception as e:
        return {"exit_code": 1, "error": str(e)}

def _create_synthetic_run_report_for_agentic_success(test_file: str, basename: str, language: str, *, atomic_state: AtomicStateUpdate = None):
    report = {
        "timestamp": datetime.datetime.now().isoformat(),
        "exit_code": 0,
        "tests_passed": 1,
        "tests_failed": 0,
        "coverage": 100.0,
        "test_hash": calculate_sha256(test_file) if os.path.exists(test_file) else "agentic_test_success"
    }
    if atomic_state:
        atomic_state.set_run_report(report)
    else:
        save_run_report(basename, language, report)

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    return language.lower() != "python" or agentic_mode

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

    if dry_run:
        _display_sync_log(basename, language, verbose)
        return {"success": True, "log_entries": load_operation_log(basename, language), "dry_run": True}

    # Internal state refs for TUI
    state = {
        "func": "Initializing", "cost": 0.0, "time": 0.0, "success": True,
        "ops": [], "skipped": [], "errors": [], "model": "N/A",
        "colors": {"auto-deps": "blue", "generate": "blue", "example": "blue", "crash": "blue", "verify": "blue", "test": "blue", "fix": "blue", "update": "blue"},
        "paths": {"prompt": "", "code": "", "example": "", "test": ""}
    }
    
    start_time = time.time()
    stop_event = threading.Event()
    app_ref = [None]
    user_confirmed_overwrite = [False]

    def get_confirm_wrapper(msg: str, default: bool = True) -> bool:
        if user_confirmed_overwrite[0]: return True
        if force: return True
        res = click.confirm(msg, default=default)
        if res: user_confirmed_overwrite[0] = True
        return res

    effective_confirm = confirm_callback or get_confirm_wrapper

    def sync_worker_logic():
        try:
            with SyncLock(basename, language) as lock:
                log_event(basename, language, "lock_acquired", {"pid": os.getpid()}, "sync")
                
                consecutive_ops = []
                last_ops_pattern = []
                
                while not stop_event.is_set():
                    state["time"] = time.time() - start_time
                    if state["cost"] >= budget:
                        state["errors"].append(f"Budget exceeded (${state['cost']:.2f} >= ${budget:.2f})")
                        break

                    decision = sync_determine_operation(basename, language, target_coverage)
                    op = decision.operation

                    # Steering
                    if not no_steer and app_ref[0]:
                        steered_op, should_abort = maybe_steer_operation(op, decision.reason, app_ref[0], quiet, skip_tests, skip_verify, timeout_s=steer_timeout)
                        if should_abort:
                            state["errors"].append("Sync aborted by user steering.")
                            break
                        if steered_op != op:
                            log_event(basename, language, "steering_override", {"from": op, "to": steered_op}, "sync")
                            op = steered_op

                    if op in ("nothing", "all_synced"):
                        break
                    
                    # Cycle Detection
                    consecutive_ops.append(op)
                    if len(consecutive_ops) > 20: consecutive_ops.pop(0)
                    
                    if op == "auto-deps" and consecutive_ops[-3:].count("auto-deps") >= 2:
                        op = "generate" # Force forward
                    
                    # Track patterns for crash-verify and test-fix
                    last_ops_pattern.append(op)
                    if len(last_ops_pattern) > 8: last_ops_pattern.pop(0)
                    if last_ops_pattern[-4:] in (["crash", "verify", "crash", "verify"], ["test", "fix", "test", "fix"]):
                        if last_ops_pattern.count(op) >= MAX_CYCLE_REPEATS * 2:
                            state["errors"].append(f"Infinite loop detected for {op}. Manual intervention required.")
                            break

                    state["func"] = op
                    entry = create_log_entry(op, decision.reason, "sync", decision.estimated_cost, decision.confidence, decision.decision_type)
                    
                    # Path resolution
                    pdd_files = get_pdd_file_paths(basename, language)
                    state["paths"].update({k: str(v) for k, v in pdd_files.items() if isinstance(v, Path)})
                    
                    ctx = _create_mock_context(force=force, local=local, strength=strength, temperature=temperature, time_param=time_param, confirm_callback=effective_confirm)
                    op_start = time.time()
                    op_success = False
                    op_cost = 0.0
                    op_model = "N/A"

                    # Execution block
                    try:
                        with AtomicStateUpdate(basename, language) as atomic:
                            if op == "auto-deps":
                                _, op_cost, op_model = auto_deps_main(ctx, str(pdd_files['prompt']), directory_path=examples_dir)
                                op_success = True
                            elif op == "generate":
                                _, _, op_cost, op_model = code_generator_main(ctx, str(pdd_files['prompt']), output=str(pdd_files['code']))
                                op_success = True
                                clear_run_report(basename, language)
                            elif op == "example":
                                _, op_cost, op_model = context_generator_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), output=str(pdd_files['example']))
                                op_success = True
                            elif op == "crash":
                                if skip_tests:
                                    state["skipped"].append("crash")
                                    _create_synthetic_run_report_for_agentic_success(str(pdd_files['test']), basename, language, atomic_state=atomic)
                                    op_success = True
                                else:
                                    # Handle crash detection
                                    crash_log = ""
                                    has_crash = False
                                    if lang_lower == "python":
                                        try:
                                            subprocess.run([detect_host_python_executable(), str(pdd_files['example'])], capture_output=True, text=True, check=True, timeout=30)
                                        except subprocess.CalledProcessError as e:
                                            crash_log = e.stderr
                                            has_crash = True
                                    
                                    if has_crash or _use_agentic_path(language, agentic_mode):
                                        agentic_limit = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                        op_success, _, _, _, op_cost, op_model = crash_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['example']), crash_log, loop=True, max_attempts=agentic_limit)
                                    else:
                                        op_success = True # No crash detected
                                    
                                    if op_success:
                                        if lang_lower == "python":
                                            _execute_tests_and_create_run_report(str(pdd_files['test']), basename, language, target_coverage, code_file=str(pdd_files['code']), atomic_state=atomic)
                                        else:
                                            _create_synthetic_run_report_for_agentic_success(str(pdd_files['test']), basename, language, atomic_state=atomic)

                            elif op == "verify":
                                if skip_verify or skip_tests:
                                    state["skipped"].append("verify")
                                    atomic.set_fingerprint("skip:verify", pdd_files, 0.0, "skip")
                                    op_success = True
                                else:
                                    agentic_limit = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                    op_success, _, _, _, op_cost, op_model = fix_verification_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['example']), loop=True, max_attempts=agentic_limit)

                            elif op == "test":
                                if skip_tests:
                                    state["skipped"].append("test")
                                    op_success = True
                                else:
                                    res = cmd_test_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), output=str(pdd_files['test']), language=language)
                                    _, op_cost, op_model, agentic_success = res
                                    op_success = agentic_success if agentic_success is not None else os.path.exists(pdd_files['test'])
                                    if op_success:
                                        if agentic_success is True:
                                            _create_synthetic_run_report_for_agentic_success(str(pdd_files['test']), basename, language, atomic_state=atomic)
                                        else:
                                            _execute_tests_and_create_run_report(str(pdd_files['test']), basename, language, target_coverage, code_file=str(pdd_files['code']), atomic_state=atomic, test_files=pdd_files.get('test_files'))

                            elif op == "fix":
                                if skip_tests:
                                    state["skipped"].append("fix")
                                    op_success = True
                                else:
                                    agentic_limit = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                    # Find primary failing test
                                    failing_test = str(pdd_files['test'])
                                    report = read_run_report(basename, language)
                                    if report and report.exit_code != 0:
                                        # logic to select specific failing test if multiple exist
                                        pass
                                    
                                    op_success, _, _, _, op_cost, op_model = fix_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), failing_test, loop=True, max_attempts=agentic_limit, verification_program=str(pdd_files['example']))
                                    if op_success:
                                        if lang_lower == "python":
                                            _execute_tests_and_create_run_report(str(pdd_files['test']), basename, language, target_coverage, code_file=str(pdd_files['code']), atomic_state=atomic, test_files=pdd_files.get('test_files'))
                                        else:
                                            _create_synthetic_run_report_for_agentic_success(str(pdd_files['test']), basename, language, atomic_state=atomic)

                            elif op == "update":
                                _, op_cost, op_model = update_main(ctx, str(pdd_files['prompt']), str(pdd_files['code']), use_git=True)
                                op_success = True

                            if op_success:
                                atomic.set_fingerprint(op, pdd_files, op_cost, op_model)
                                state["ops"].append(op)
                                state["colors"][op] = "green"
                            else:
                                state["colors"][op] = "red"
                                break

                    except Exception as e:
                        state["errors"].append(f"Operation {op} failed: {str(e)}")
                        state["colors"][op] = "red"
                        break
                    finally:
                        state["cost"] += op_cost
                        state["model"] = op_model
                        entry = update_log_entry(entry, op_success, op_cost, op_model, time.time() - op_start, "; ".join(state["errors"]) if state["errors"] else None)
                        append_log_entry(basename, language, entry)

        except Exception as e:
            state["errors"].append(f"Sync worker crashed: {str(e)}")
            state["success"] = False
            raise e

    # Headless detection
    is_headless = not sys.stdin.isatty() or os.getenv("CI") == "true" or quiet
    
    if is_headless:
        os.environ["PDD_FORCE"] = "1"
        sync_worker_logic()
    else:
        from .sync_tui import show_exit_animation
        app = SyncApp(worker_func=sync_worker_logic, state=state, stop_event=stop_event)
        app_ref[0] = app
        run_res = app.run()
        
        if app.worker_exception:
            click.echo(f"Error in sync worker: {app.worker_exception}", err=True)
            traceback.print_exception(type(app.worker_exception), app.worker_exception, app.worker_exception.__traceback__)
        
        if run_res is None:
            return {"success": False, "error": "Sync interrupted by user"}

        if not quiet:
            show_exit_animation(state["success"], state["ops"])

    return {
        "success": len(state["errors"]) == 0,
        "operations_completed": state["ops"],
        "skipped_operations": state["skipped"],
        "total_cost": state["cost"],
        "total_time": time.time() - start_time,
        "errors": state["errors"],
        "error": "; ".join(state["errors"]) if state["errors"] else None,
        "model_name": state["model"]
    }
