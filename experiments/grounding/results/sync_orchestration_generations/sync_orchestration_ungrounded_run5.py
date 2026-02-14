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
from .pytest_output import extract_failing_files_from_output, _find_project_root
from . import DEFAULT_STRENGTH

# Constants
MAX_CONSECUTIVE_TESTS = 3
MAX_TEST_EXTEND_ATTEMPTS = 2
MAX_CONSECUTIVE_CRASHES = 3
MAX_CYCLE_REPEATS = 2

class AtomicStateUpdate:
    """Context manager for consistent state updates (Fingerprint + RunReport)."""
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language
        self.fingerprint_data = None
        self.run_report_data = None

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            if self.fingerprint_data:
                save_fingerprint(self.basename, self.language, **self.fingerprint_data)
            if self.run_report_data:
                save_run_report(self.basename, self.language, self.run_report_data)

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Determine if the operation should use the agentic/non-Python path."""
    return agentic_mode or language.lower() != "python"

def _display_sync_log(basename: str, language: str, verbose: bool):
    """Format and display the historical sync log."""
    entries = load_operation_log(basename, language)
    if not entries:
        click.echo(f"No sync history found for {basename} ({language}).")
        return

    click.echo(click.style(f"--- Sync Analysis Log: {basename} ---", bold=True))
    for entry in entries:
        ts = entry.get("timestamp", "")
        op = entry.get("operation", "unknown")
        reason = entry.get("reason", "")
        cost = entry.get("actual_cost", 0.0)
        
        color = "green" if entry.get("success") else "yellow"
        if entry.get("invocation_mode") == "manual":
            op = f"[manual] {op}"
            color = "cyan"

        line = f"[{ts}] {op:10} | {reason}"
        if verbose:
            line += f" | Cost: ${cost:.4f} | Model: {entry.get('model')}"
        
        click.echo(click.style(line, fg=color))

def _create_mock_context(**kwargs) -> click.Context:
    """Create a mock Click context for internal command calls."""
    ctx = click.Context(click.Command("sync_internal"))
    ctx.obj = kwargs
    ctx.params = kwargs
    return ctx

def _parse_test_output(output: str, language: str) -> Tuple[int, int, float]:
    """Parse test runner output to extract passing/failing counts and coverage."""
    passed = 0
    failed = 0
    coverage = 0.0
    
    lang_lower = language.lower()
    
    # Python/Pytest parsing
    if lang_lower == "python":
        m_pass = re.search(r"(\d+) passed", output)
        m_fail = re.search(r"(\d+) failed", output)
        m_cov = re.search(r"TOTAL\s+\d+\s+\d+\s+(\d+)%", output)
        passed = int(m_pass.group(1)) if m_pass else 0
        failed = int(m_fail.group(1)) if m_fail else 0
        coverage = float(m_cov.group(1)) if m_cov else 0.0
    
    # Generic parsing for JS/TS (Jest/Vitest), Go, Cargo
    else:
        # Simple heuristic for non-Python runners
        m_pass = re.search(r"Tests?:\s+(\d+)\s+passed", output, re.I)
        m_fail = re.search(r"Tests?:\s+(\d+)\s+failed", output, re.I)
        m_cov = re.search(r"All files\s+\|\s+([\d.]+)", output)
        passed = int(m_pass.group(1)) if m_pass else (1 if "SUCCESS" in output.upper() else 0)
        failed = int(m_fail.group(1)) if m_fail else (1 if "FAIL" in output.upper() else 0)
        coverage = float(m_cov.group(1)) if m_cov else 0.0
        
    return passed, failed, coverage

def _python_cov_target_for_code_file(code_file: str) -> str:
    """Resolve the coverage module target."""
    p = Path(code_file)
    if "src" in p.parts:
        idx = p.parts.index("src")
        return ".".join(p.parts[idx+1:]).replace(".py", "")
    return p.stem

def _execute_tests_and_create_run_report(
    test_file: str, 
    basename: str, 
    language: str, 
    target_coverage: float, 
    *, 
    code_file: Optional[str] = None, 
    atomic_state: Optional[AtomicStateUpdate] = None, 
    test_files: Optional[List[str]] = None
) -> RunReport:
    """Run tests, capture output, and generate a RunReport."""
    lang_lower = language.lower()
    from .get_test_command import get_test_command_for_file
    
    cmd_str = get_test_command_for_file(test_file, language=language)
    if not cmd_str:
        return RunReport(datetime.datetime.now().isoformat(), 1, 0, 1, 0.0)

    # Project root and path isolation logic
    env = os.environ.copy()
    env.pop("FORCE_COLOR", None)
    env.pop("COLUMNS", None)
    
    cwd = Path.cwd()
    root = _find_project_root(test_file) or cwd
    
    # Python specific pathing
    if lang_lower == "python":
        py_path = f"{root}:{root}/src:{env.get('PYTHONPATH', '')}"
        env["PYTHONPATH"] = py_path
        
        # Add coverage args if we have a code file
        if code_file and "pytest" in cmd_str:
            target = _python_cov_target_for_code_file(code_file)
            cmd_str += f" --cov={target} --cov-report=term-missing --rootdir={root} -c /dev/null"

    target_files = test_files if test_files else [test_file]
    full_cmd = f"{cmd_str} {' '.join(target_files)}"
    
    try:
        proc = subprocess.run(
            full_cmd,
            shell=True,
            capture_output=True,
            text=True,
            env=env,
            start_new_session=True,
            stdin=subprocess.DEVNULL
        )
        output = proc.stdout + proc.stderr
        passed, failed, coverage = _parse_test_output(output, language)
        
        hashes = {}
        for f in target_files:
            if Path(f).exists():
                hashes[f] = calculate_sha256(Path(f))

        report = RunReport(
            timestamp=datetime.datetime.now().isoformat(),
            exit_code=proc.returncode,
            tests_passed=passed,
            tests_failed=failed,
            coverage=coverage,
            test_hash=calculate_sha256(Path(test_file)) if Path(test_file).exists() else None,
            test_file_hashes=hashes
        )
        
        if atomic_state:
            atomic_state.run_report_data = report.__dict__
        else:
            save_run_report(basename, language, report.__dict__)
            
        return report
    except Exception as e:
        return RunReport(datetime.datetime.now().isoformat(), 1, 0, 1, 0.0)

def _create_synthetic_run_report_for_agentic_success(
    test_file: str, 
    basename: str, 
    language: str, 
    *, 
    atomic_state: Optional[AtomicStateUpdate] = None
) -> RunReport:
    """Create a success report for agentic runs that verify themselves."""
    test_path = Path(test_file)
    h = calculate_sha256(test_path) if test_path.exists() else "agentic_test_success"
    
    report = RunReport(
        timestamp=datetime.datetime.now().isoformat(),
        exit_code=0,
        tests_passed=1,
        tests_failed=0,
        coverage=100.0,
        test_hash=h
    )
    
    if atomic_state:
        atomic_state.run_report_data = report.__dict__
    else:
        save_run_report(basename, language, report.__dict__)
    return report

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
    
    # Defaults defense
    target_coverage = target_coverage if target_coverage is not None else 90.0
    budget = budget if budget is not None else 20.0
    max_attempts = max_attempts if max_attempts is not None else 3

    from .get_extension import get_extension
    
    # Result object
    res = {
        "success": False,
        "operations_completed": [],
        "skipped_operations": [],
        "total_cost": 0.0,
        "total_time": 0.0,
        "final_state": {},
        "errors": [],
        "error": None,
        "model_name": None,
        "log_entries": []
    }

    if dry_run:
        _display_sync_log(basename, language, verbose)
        res["success"] = True
        return res

    start_time = time.time()
    
    # Path Resolution
    try:
        pdd_files = get_pdd_file_paths(basename, language, prompts_dir, code_dir, examples_dir, tests_dir)
    except FileNotFoundError as e:
        # Fallback for missing test files
        pdd_files = get_pdd_file_paths(basename, language, prompts_dir, code_dir, examples_dir, tests_dir)
    except Exception as e:
        res["error"] = str(e)
        return res

    # TUI State
    func_name_ref = ["Initializing"]
    cost_ref = [0.0]
    app_ref = [None]
    stop_event = threading.Event()
    user_confirmed_overwrite = [force]
    progress_callback_ref = [None]

    def get_confirm_wrapper():
        def wrapper(msg, default=True):
            if user_confirmed_overwrite[0]: return True
            if app_ref[0]:
                confirmed = app_ref[0].request_confirmation("File Overwrite", msg)
            else:
                confirmed = click.confirm(msg, default=default)
            if confirmed: user_confirmed_overwrite[0] = True
            return confirmed
        return wrapper

    def sync_worker_logic():
        consecutive_ops = []
        last_op_pair = []
        
        try:
            with SyncLock(basename, language):
                log_event(basename, language, "lock_acquired", {}, "sync")
                
                while not stop_event.is_set():
                    # Check budget
                    if res["total_cost"] >= budget:
                        res["errors"].append("Budget exceeded")
                        break
                    if res["total_cost"] > (budget * 0.8):
                        log_event(basename, language, "budget_warning", {"remaining": budget - res["total_cost"]}, "sync")

                    # Analyze
                    decision = sync_determine_operation(basename, language, target_coverage)
                    op = decision.operation
                    
                    if op in ("all_synced", "nothing", "error"):
                        if op == "error": res["errors"].append(decision.reason)
                        break

                    # Steering
                    if not no_steer:
                        steered_op, should_abort = maybe_steer_operation(
                            op, decision.reason, app_ref[0], quiet, skip_tests, skip_verify, timeout_s=steer_timeout
                        )
                        if should_abort:
                            res["errors"].append("Sync aborted by user steering.")
                            break
                        if steered_op != op:
                            log_event(basename, language, "steering_override", {"from": op, "to": steered_op}, "sync")
                            op = steered_op

                    # Cycle/Infinite Loop Detection
                    consecutive_ops.append(op)
                    if len(consecutive_ops) > 20: break # Safety valve
                    
                    # Logic to break specific cycles
                    if op == "auto-deps" and consecutive_ops.count("auto-deps") >= 2:
                        op = "generate"
                    
                    # Worker logic - Execute Op
                    func_name_ref[0] = f"Executing {op}..."
                    op_start = time.time()
                    
                    entry = create_log_entry(op, decision.reason, "sync", decision.estimated_cost, decision.confidence, decision.decision_type)
                    
                    # Operation Dispatch
                    success, op_cost, model = _execute_op(
                        op, basename, language, pdd_files, res, strength, temperature, time_param, 
                        get_confirm_wrapper(), local, agentic_mode, target_coverage, progress_callback_ref[0]
                    )
                    
                    res["total_cost"] += op_cost
                    cost_ref[0] = res["total_cost"]
                    res["model_name"] = model
                    
                    update_log_entry(entry, success, op_cost, model, time.time() - op_start, None if success else "Op failed")
                    append_log_entry(basename, language, entry)

                    if success:
                        res["operations_completed"].append(op)
                    else:
                        res["errors"].append(f"Operation {op} failed")
                        break

        except Exception as e:
            res["errors"].append(f"Worker crashed: {str(e)}")
            if app_ref[0]: app_ref[0].worker_exception = e
            traceback.print_exc()
        finally:
            log_event(basename, language, "lock_released", {}, "sync")
            stop_event.set()

    # Headless vs TUI
    is_headless = not sys.stdin.isatty() or os.getenv("CI") or quiet
    if is_headless:
        os.environ["PDD_FORCE"] = "1"
        sync_worker_logic()
    else:
        app = SyncApp(worker_func=sync_worker_logic, stop_event=stop_event)
        app_ref[0] = app
        app.run()
        
        from .sync_tui import show_exit_animation
        show_exit_animation()

    res["total_time"] = time.time() - start_time
    res["success"] = len(res["errors"]) == 0
    res["error"] = "; ".join(res["errors"]) if res["errors"] else None
    
    return res

def _execute_op(op, basename, language, paths, res_agg, strength, temp, time_p, confirm_cb, local, agentic, target_cov, progress_cb) -> Tuple[bool, float, str]:
    """Internal router for specific PDD operations."""
    ctx = _create_mock_context(
        strength=strength, temperature=temp, time=time_p, 
        force=True, quiet=True, local=local, confirm_callback=confirm_cb
    )
    
    atomic = AtomicStateUpdate(basename, language)
    is_agentic = _use_agentic_path(language, agentic)
    
    try:
        if op == "auto-deps":
            with atomic:
                mod, cost, model = auto_deps_main(ctx, str(paths["prompt"]), "examples/**/*.py", output=str(paths["prompt"]))
                atomic.fingerprint_data = {"operation": op, "paths": paths, "cost": cost, "model": model}
                return True, cost, model

        elif op == "generate":
            with atomic:
                clear_run_report(basename, language)
                code, inc, cost, model = code_generator_main(ctx, str(paths["prompt"]), output=str(paths["code"]))
                atomic.fingerprint_data = {"operation": op, "paths": paths, "cost": cost, "model": model}
                return True, cost, model

        elif op == "example":
            with atomic:
                code, cost, model = context_generator_main(ctx, str(paths["prompt"]), str(paths["code"]), output=str(paths["example"]))
                atomic.fingerprint_data = {"operation": op, "paths": paths, "cost": cost, "model": model}
                return True, cost, model

        elif op == "crash":
            with atomic:
                # Use example as program if exists
                prog = str(paths.get("example")) if paths.get("example") and Path(paths["example"]).exists() else str(paths["code"])
                success, code, prog_out, att, cost, model = crash_main(
                    ctx, str(paths["prompt"]), str(paths["code"]), prog, None, 
                    output=str(paths["code"]), loop=True, max_attempts=0 if is_agentic else 3
                )
                if success:
                    atomic.fingerprint_data = {"operation": op, "paths": paths, "cost": cost, "model": model}
                    if is_agentic:
                        _create_synthetic_run_report_for_agentic_success(str(paths["code"]), basename, language, atomic_state=atomic)
                return success, cost, model

        elif op == "verify":
            with atomic:
                prog = str(paths.get("example"))
                success, p, c, att, cost, model = fix_verification_main(
                    ctx, str(paths["prompt"]), str(paths["code"]), prog, 
                    output_code=str(paths["code"]), loop=True, max_attempts=0 if is_agentic else 3
                )
                if success:
                    atomic.fingerprint_data = {"operation": op, "paths": paths, "cost": cost, "model": model}
                return success, cost, model

        elif op in ("test", "test_extend"):
            with atomic:
                is_extend = (op == "test_extend")
                # cmd_test_main returns 4-tuple
                result = cmd_test_main(
                    ctx, str(paths["prompt"]), str(paths["code"]), output=str(paths["test"]), 
                    language=language, existing_tests=[str(paths["test"])] if is_extend else None,
                    merge=is_extend, target_coverage=target_cov
                )
                code, cost, model, agentic_success = result
                
                success = False
                if agentic_success is True:
                    _create_synthetic_run_report_for_agentic_success(str(paths["test"]), basename, language, atomic_state=atomic)
                    success = True
                else:
                    report = _execute_tests_and_create_run_report(str(paths["test"]), basename, language, target_cov, code_file=str(paths["code"]), atomic_state=atomic)
                    success = report.exit_code == 0 or is_extend # Extend is "success" even if coverage didn't hit target yet

                if success:
                    atomic.fingerprint_data = {"operation": op, "paths": paths, "cost": cost, "model": model}
                return success, cost, model

        elif op == "fix":
            with atomic:
                success, test, code, att, cost, model = fix_main(
                    ctx, str(paths["prompt"]), str(paths["code"]), str(paths["test"]), None,
                    output_test=str(paths["test"]), output_code=str(paths["code"]),
                    loop=True, max_attempts=0 if is_agentic else 3
                )
                if success:
                    atomic.fingerprint_data = {"operation": op, "paths": paths, "cost": cost, "model": model}
                    if is_agentic:
                        _create_synthetic_run_report_for_agentic_success(str(paths["test"]), basename, language, atomic_state=atomic)
                    else:
                        _execute_tests_and_create_run_report(str(paths["test"]), basename, language, target_cov, code_file=str(paths["code"]), atomic_state=atomic)
                return success, cost, model

        elif op == "update":
            with atomic:
                prompt, cost, model = update_main(ctx, str(paths["prompt"]), str(paths["code"]), use_git=True)
                atomic.fingerprint_data = {"operation": op, "paths": paths, "cost": cost, "model": model}
                return True, cost, model

    except Exception as e:
        traceback.print_exc()
        return False, 0.0, str(e)
    
    return False, 0.0, f"Unknown operation: {op}"
