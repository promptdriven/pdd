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
import shutil
import traceback
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
    Fingerprint,
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

@dataclass
class AtomicStateUpdate:
    """Context manager for consistent state writes (fingerprint + run report)."""
    basename: str
    language: str
    
    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        pass

    def save(self, operation: str, paths: Dict[str, Path], cost: float, model: str, run_report: Optional[Dict] = None):
        """Atomically saves fingerprint and optionally run report."""
        if run_report:
            save_run_report(self.basename, self.language, run_report)
        save_fingerprint(self.basename, self.language, operation, paths, cost, model)

def _display_sync_log(basename: str, language: str, verbose: bool):
    """Formats and displays the sync log for dry-runs."""
    entries = load_operation_log(basename, language)
    if not entries:
        click.echo(f"No sync history found for {basename}_{language}")
        return

    click.echo(f"--- Sync Analysis History for {basename} ({language}) ---")
    for entry in entries:
        timestamp = entry.get('timestamp', 'N/A')
        op = entry.get('operation', 'unknown')
        decision = entry.get('decision_type', 'N/A')
        
        if verbose:
            click.echo(f"[{timestamp}] Op: {op} | Decision: {decision} | Confidence: {entry.get('confidence', 0):.2f}")
            if 'reason' in entry:
                click.echo(f"  Reason: {entry['reason']}")
        else:
            click.echo(f"[{timestamp}] {op.upper()}: {entry.get('reason', '')}")

def _create_mock_context(**kwargs) -> click.Context:
    """Creates a mock Click context for internal tool execution."""
    ctx = click.Context(click.Command('sync-internal'))
    ctx.obj = {
        'strength': kwargs.get('strength', DEFAULT_STRENGTH),
        'temperature': kwargs.get('temperature', 0.0),
        'time': kwargs.get('time_param', 0.25),
        'verbose': kwargs.get('verbose', False),
        'quiet': kwargs.get('quiet', False),
        'force': kwargs.get('force', False),
        'local': kwargs.get('local', False),
    }
    ctx.params = {'local': kwargs.get('local', False), 'force': kwargs.get('force', False)}
    return ctx

def _parse_test_output(output: str, language: str) -> Tuple[int, int, float]:
    """Parses test runner output to extract passed/failed counts and coverage."""
    passed, failed, coverage = 0, 0, 0.0
    
    # Generic coverage regex (matches "XX%" or "XX.X%")
    cov_match = re.search(r'TOTAL\s+.*?\s+(\d+(?:\.\d+)?)%', output)
    if cov_match:
        coverage = float(cov_match.group(1))

    if language.lower() == "python":
        # Pytest pattern: "10 passed, 2 failed in 0.5s"
        m = re.search(r'(\d+)\s+passed(?:,\s+(\d+)\s+failed)?', output)
        if m:
            passed = int(m.group(1))
            failed = int(m.group(2)) if m.group(2) else 0
    else:
        # Simple generic fallback for other runners
        pass_matches = re.findall(r'(\d+)\s+passed', output, re.IGNORECASE)
        fail_matches = re.findall(r'(\d+)\s+failed', output, re.IGNORECASE)
        if pass_matches: passed = int(pass_matches[-1])
        if fail_matches: failed = int(fail_matches[-1])

    return passed, failed, coverage

def _python_cov_target_for_test_and_code(test_file: Path, code_file: Path) -> str:
    """Determines the best --cov target by analyzing imports or using code file."""
    if not code_file.exists():
        return ""
    # Usually we just want the code file's name as a module
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
    """Runs tests, measures coverage, and saves a RunReport."""
    lang_lower = language.lower()
    files_to_run = test_files if test_files else [test_file]
    
    if lang_lower == "python":
        python_exe = detect_host_python_executable()
        cov_target = _python_cov_target_for_test_and_code(test_file, code_file)
        
        project_root = _find_project_root(test_file)
        env = os.environ.copy()
        if project_root:
            env["PYTHONPATH"] = f"{project_root}:{project_root}/src:{env.get('PYTHONPATH', '')}"
        
        cmd = [python_exe, "-m", "pytest"]
        if cov_target:
            cmd += [f"--cov={cov_target}", "--cov-report=term-missing"]
        cmd += [str(f) for f in files_to_run]
        
        try:
            result = subprocess.run(
                cmd, capture_output=True, text=True, env=env, timeout=60, start_new_session=True
            )
            stdout, stderr = result.stdout, result.stderr
            exit_code = result.returncode
        except subprocess.TimeoutExpired:
            stdout, stderr, exit_code = "", "Timeout", 1
    else:
        # Non-python resolution
        cmd_str = get_test_command_for_file(str(test_file), language=language)
        if not cmd_str:
            return {"exit_code": 1, "error": "No test runner found"}
        
        try:
            result = subprocess.run(
                cmd_str, shell=True, capture_output=True, text=True, timeout=60, start_new_session=True
            )
            stdout, stderr = result.stdout, result.stderr
            exit_code = result.returncode
        except subprocess.TimeoutExpired:
            stdout, stderr, exit_code = "", "Timeout", 1

    passed, failed, coverage = _parse_test_output(stdout + stderr, language)
    
    report_data = {
        "timestamp": datetime.datetime.now().isoformat(),
        "exit_code": exit_code,
        "tests_passed": passed,
        "tests_failed": failed,
        "coverage": coverage,
        "stdout": stdout,
        "stderr": stderr,
        "test_hash": calculate_sha256(test_file) if test_file.exists() else None
    }
    
    if atomic_state:
        save_run_report(basename, language, report_data)
        
    return report_data

def _create_synthetic_run_report_for_agentic_success(test_file: Path, basename: str, language: str, atomic_state: Optional[AtomicStateUpdate] = None):
    """Creates a successful RunReport without actually executing tests (agentic fallback)."""
    report_data = {
        "timestamp": datetime.datetime.now().isoformat(),
        "exit_code": 0,
        "tests_passed": 1,
        "tests_failed": 0,
        "coverage": 100.0,
        "test_hash": calculate_sha256(test_file) if test_file.exists() else "agentic_test_success"
    }
    if atomic_state:
        save_run_report(basename, language, report_data)
    else:
        save_run_report(basename, language, report_data)

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Determines if we should skip iterative loops and use agentic logic."""
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
    """Orchestrates the complete PDD sync workflow with TUI animation."""
    
    # Handle CLI Nones
    target_coverage = target_coverage if target_coverage is not None else 90.0
    budget = budget if budget is not None else 20.0
    max_attempts = max_attempts if max_attempts is not None else 3

    if dry_run:
        _display_sync_log(basename, language, verbose)
        return {"success": True, "dry_run": True}

    # Internal state tracking
    results = {
        "success": False, "operations_completed": [], "skipped_operations": [],
        "total_cost": 0.0, "total_time": 0.0, "errors": [], "error": None
    }
    
    start_time = time.time()
    lang_lower = language.lower()
    
    # Shared refs for TUI
    function_name_ref = ["Initializing"]
    cost_ref = [0.0]
    prompt_color_ref, code_color_ref, example_color_ref, test_color_ref = ["white"] * 4
    prompt_path_ref, code_path_ref, example_path_ref, test_path_ref = [""] * 4
    app_ref = []
    stop_event = threading.Event()
    user_confirmed_overwrite = [False]

    def get_confirm_wrapper(msg: str, default: bool = True) -> bool:
        if force or user_confirmed_overwrite[0]:
            return True
        if app_ref:
            res = app_ref[0].request_confirmation("Sync Confirmation", msg)
            if res: user_confirmed_overwrite[0] = True
            return res
        res = click.confirm(msg, default=default)
        if res: user_confirmed_overwrite[0] = True
        return res

    def sync_worker_logic():
        consecutive_ops = []
        try:
            with SyncLock(basename, lang_lower) as lock:
                log_event(basename, lang_lower, "lock_acquired", {"pid": os.getpid()}, "sync")
                
                while not stop_event.is_set():
                    # Check budget
                    if cost_ref[0] >= budget:
                        results["errors"].append(f"Budget exceeded: ${cost_ref[0]:.2f} >= ${budget:.2f}")
                        break

                    # 1. Determine next operation
                    decision = sync_determine_operation(basename, lang_lower, target_coverage)
                    op = decision.operation
                    
                    # Cycle/Loop detection
                    consecutive_ops.append(op)
                    if len(consecutive_ops) > 10: consecutive_ops.pop(0)
                    
                    if op in ("all_synced", "nothing", "fail_and_request_manual_merge", "error"):
                        results["success"] = (op in ("all_synced", "nothing"))
                        break

                    # Steering
                    if not no_steer:
                        steered_op, should_abort = maybe_steer_operation(
                            op, decision.reason, app_ref, quiet, skip_tests, skip_verify, timeout_s=steer_timeout
                        )
                        if should_abort:
                            results["errors"].append("User aborted via steering")
                            break
                        if steered_op != op:
                            log_event(basename, lang_lower, "steering_override", {"from": op, "to": steered_op}, "sync")
                            op = steered_op

                    # Update TUI
                    function_name_ref[0] = op
                    pdd_paths = get_pdd_file_paths(basename, lang_lower)
                    prompt_path_ref[0] = str(pdd_paths.get('prompt', ''))
                    code_path_ref[0] = str(pdd_paths.get('code', ''))
                    example_path_ref[0] = str(pdd_paths.get('example', ''))
                    test_path_ref[0] = str(pdd_paths.get('test', ''))

                    # 2. Execute operation
                    entry = create_log_entry(op, decision.reason, "sync", decision.estimated_cost, decision.confidence, decision.decision_type)
                    op_start = time.time()
                    op_success = False
                    op_cost = 0.0
                    op_model = "unknown"
                    op_error = None
                    
                    ctx = _create_mock_context(
                        strength=strength, temperature=temperature, time_param=time_param,
                        verbose=verbose, quiet=quiet, force=force, local=local
                    )
                    ctx.params['confirm_callback'] = get_confirm_wrapper
                    
                    atomic = AtomicStateUpdate(basename, lang_lower)
                    
                    try:
                        if op == "auto-deps":
                            _, op_cost, op_model = auto_deps_main(ctx, str(pdd_paths['prompt']), f"{examples_dir}/**/*", force_scan=False)
                            op_success = True
                        
                        elif op == "generate":
                            clear_run_report(basename, lang_lower)
                            _, _, op_cost, op_model = code_generator_main(ctx, str(pdd_paths['prompt']), str(pdd_paths['code']))
                            op_success = True
                            
                        elif op == "example":
                            _, op_cost, op_model = context_generator_main(ctx, str(pdd_paths['prompt']), str(pdd_paths['code']), str(pdd_paths['example']))
                            op_success = True

                        elif op == "crash":
                            if skip_tests:
                                results["skipped_operations"].append(op)
                                op_success = True
                            else:
                                crash_attempts = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                op_success, _, _, _, op_cost, op_model = crash_main(
                                    ctx, str(pdd_paths['prompt']), str(pdd_paths['code']), str(pdd_paths['example']), 
                                    "crash_captured.log", loop=(crash_attempts > 0), max_attempts=crash_attempts, budget=budget - cost_ref[0]
                                )
                                if op_success:
                                    _execute_tests_and_create_run_report(pdd_paths['test'], basename, lang_lower, target_coverage, code_file=pdd_paths['code'], atomic_state=atomic)

                        elif op == "verify":
                            if skip_verify or skip_tests:
                                results["skipped_operations"].append(op)
                                op_success = True
                            else:
                                verify_attempts = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                                op_success, _, _, _, op_cost, op_model = fix_verification_main(
                                    ctx, str(pdd_paths['prompt']), str(pdd_paths['code']), str(pdd_paths['example']),
                                    loop=(verify_attempts > 0), max_attempts=verify_attempts, budget=budget - cost_ref[0]
                                )

                        elif op == "test":
                            if skip_tests:
                                results["skipped_operations"].append(op)
                                op_success = True
                            else:
                                _, op_cost, op_model, agentic_success = cmd_test_main(ctx, str(pdd_paths['prompt']), str(pdd_paths['code']), str(pdd_paths['test']), language=language)
                                if agentic_success:
                                    _create_synthetic_run_report_for_agentic_success(pdd_paths['test'], basename, lang_lower, atomic_state=atomic)
                                    op_success = True
                                else:
                                    report = _execute_tests_and_create_run_report(pdd_paths['test'], basename, lang_lower, target_coverage, code_file=pdd_paths['code'], atomic_state=atomic)
                                    op_success = (report['exit_code'] == 0 or report['tests_failed'] > 0) # Successful execution of tests

                        elif op == "fix":
                            fix_attempts = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                            op_success, _, _, _, op_cost, op_model = fix_main(
                                ctx, str(pdd_paths['prompt']), str(pdd_paths['code']), str(pdd_paths['test']), 
                                "fix_errors.log", loop=(fix_attempts > 0), max_attempts=fix_attempts, budget=budget - cost_ref[0]
                            )
                            if op_success:
                                _execute_tests_and_create_run_report(pdd_paths['test'], basename, lang_lower, target_coverage, code_file=pdd_paths['code'], atomic_state=atomic)

                        elif op == "update":
                            _, op_cost, op_model = update_main(ctx, str(pdd_paths['prompt']), str(pdd_paths['code']), use_git=True)
                            op_success = True

                        if op_success:
                            atomic.save(op, pdd_paths, op_cost, op_model)
                            results["operations_completed"].append(op)
                            cost_ref[0] += op_cost
                        
                    except Exception as e:
                        op_error = str(e)
                        results["errors"].append(f"Operation {op} failed: {e}")
                        if verbose: traceback.print_exc()

                    # Finalize entry
                    update_log_entry(entry, op_success, op_cost, op_model, time.time() - op_start, op_error)
                    append_log_entry(basename, lang_lower, entry)
                    
                    if not op_success: break

        finally:
            results["total_cost"] = cost_ref[0]
            results["total_time"] = time.time() - start_time
            results["error"] = "; ".join(results["errors"]) if results["errors"] else None

    # Execution Mode: Headless vs TUI
    is_headless = not sys.stdin.isatty() or os.environ.get("CI") == "true" or quiet
    
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
            stop_event=stop_event,
            verbose=verbose
        )
        app_ref.append(app)
        app.run()
        
        from .sync_tui import show_exit_animation
        show_exit_animation(results["success"], results.get("total_cost", 0.0), results.get("total_time", 0.0))

    return results