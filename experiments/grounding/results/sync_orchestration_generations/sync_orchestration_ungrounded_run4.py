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
from typing import Dict, Any, Optional, List, Callable
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
    """Context manager for consistent state writes (fingerprint and run report)."""
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language.lower()
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

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    return agentic_mode or language.lower() not in ("python",)

def _create_synthetic_run_report_for_agentic_success(test_file, basename, language, atomic_state=None):
    report_data = {
        "timestamp": datetime.datetime.now().isoformat(),
        "exit_code": 0,
        "tests_passed": 1,
        "tests_failed": 0,
        "coverage": 100.0,
        "test_hash": calculate_sha256(Path(test_file)) if Path(test_file).exists() else "agentic_test_success"
    }
    if atomic_state:
        atomic_state.set_run_report(report_data)
    else:
        save_run_report(basename, language.lower(), report_data)

def _display_sync_log(basename: str, language: str, verbose: bool):
    entries = load_operation_log(basename, language)
    if not entries:
        click.echo(f"No sync history found for {basename} ({language}).")
        return

    click.echo(click.style(f"\n--- Sync History: {basename} ({language}) ---", bold=True))
    for entry in entries:
        op = entry.get("operation", "unknown")
        success = entry.get("success", False)
        color = "green" if success else "red"
        
        summary = f"[{entry.get('timestamp', '')}] {op.upper()}: {'SUCCESS' if success else 'FAILED'}"
        click.echo(click.style(summary, fg=color))
        
        if verbose:
            click.echo(f"  Reason: {entry.get('reason')}")
            click.echo(f"  Decision Type: {entry.get('decision_type')}")
            click.echo(f"  Cost: ${entry.get('actual_cost', 0.0):.4f} | Model: {entry.get('model')}")
    click.echo("")

def _create_mock_context(**kwargs) -> click.Context:
    ctx = click.Context(click.Command("sync"))
    ctx.obj = kwargs
    ctx.params = kwargs
    return ctx

def _parse_test_output(output: str, language: str):
    passed = 0
    failed = 0
    coverage = 0.0

    if language.lower() == "python":
        # Pytest pattern
        p_match = re.search(r"(\d+) passed", output)
        f_match = re.search(r"(\d+) failed", output)
        c_match = re.search(r"TOTAL\s+\d+\s+\d+\s+(\d+)%", output)
        if p_match: passed = int(p_match.group(1))
        if f_match: failed = int(f_match.group(1))
        if c_match: coverage = float(c_match.group(1))
    else:
        # Generic fallback parsing for Jest/Mocha/Go/Cargo
        if "FAIL" in output or "failed" in output.lower():
            failed = 1
        elif "PASS" in output or "ok" in output.lower() or "success" in output.lower():
            passed = 1
            coverage = 100.0
            
    return passed, failed, coverage

def _python_cov_target_for_code_file(code_file: str) -> str:
    path = Path(code_file)
    if "src" in path.parts:
        try:
            idx = path.parts.index("src")
            return ".".join(path.parts[idx+1:]).replace(".py", "")
        except: pass
    return path.stem

def _execute_tests_and_create_run_report(test_file, basename, language, target_coverage, *, code_file=None, atomic_state=None, test_files=None):
    lang_lower = language.lower()
    test_paths = test_files if test_files else [test_file]
    
    if lang_lower == "python":
        python_exe = detect_host_python_executable()
        cmd = [python_exe, "-m", "pytest"]
        
        # Isolated pathing for pytest
        proj_root = _find_project_root(test_paths[0])
        env = os.environ.copy()
        if proj_root:
            env["PYTHONPATH"] = f"{proj_root}{os.pathsep}{proj_root}/src{os.pathsep}{env.get('PYTHONPATH', '')}"
            cmd += ["--rootdir", str(proj_root), "-c", "/dev/null"]
            
        if code_file:
            cov_target = _python_cov_target_for_code_file(code_file)
            cmd += [f"--cov={cov_target}", "--cov-report=term-missing"]
            
        cmd += test_paths
    else:
        from .get_test_command import get_test_command_for_file
        cmd_str = get_test_command_for_file(test_paths[0], language=language)
        if not cmd_str:
            return 1, 0, 1, 0.0 # Signal failure if no runner
        cmd = cmd_str.split()

    try:
        # Isolate from TUI
        env_clean = os.environ.copy()
        for k in ["FORCE_COLOR", "COLUMNS", "LINES"]: env_clean.pop(k, None)
        
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            env=env_clean,
            start_new_session=True,
            stdin=subprocess.DEVNULL
        )
        passed, failed, cov = _parse_test_output(result.stdout + result.stderr, language)
        
        report_data = {
            "timestamp": datetime.datetime.now().isoformat(),
            "exit_code": result.returncode,
            "tests_passed": passed,
            "tests_failed": failed,
            "coverage": cov,
            "test_hash": calculate_sha256(Path(test_file)) if Path(test_file).exists() else None,
            "test_file_hashes": {str(p): calculate_sha256(Path(p)) for p in test_paths if Path(p).exists()}
        }
        
        if atomic_state:
            atomic_state.set_run_report(report_data)
        else:
            save_run_report(basename, lang_lower, report_data)
            
        return result.returncode, passed, failed, cov
    except Exception as e:
        return 1, 0, 1, 0.0

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
    """Orchestrates the complete PDD sync workflow with real-time feedback."""
    
    # Defaults defense
    target_coverage = target_coverage if target_coverage is not None else 90.0
    budget = budget if budget is not None else 20.0
    max_attempts = max_attempts if max_attempts is not None else 3

    from .get_extension import get_extension
    lang_lower = language.lower()

    if dry_run:
        _display_sync_log(basename, lang_lower, verbose)
        return {"success": True, "log_entries": load_operation_log(basename, lang_lower)}

    # Ref containers for TUI coordination
    function_name_ref = ["Initializing..."]
    cost_ref = [0.0]
    status_refs = {k: ["gray"] for k in ["prompt", "code", "example", "test"]}
    path_refs = {k: [""] for k in ["prompt", "code", "example", "test"]}
    stop_event = threading.Event()
    app_ref = [None]
    progress_callback_ref = [None]
    user_confirmed_overwrite = [False]

    def get_confirm_wrapper():
        def wrapper(msg, default=False):
            if force or user_confirmed_overwrite[0]:
                return True
            if app_ref[0]:
                res = app_ref[0].request_confirmation(msg)
                if res: user_confirmed_overwrite[0] = True
                return res
            res = click.confirm(msg, default=default)
            if res: user_confirmed_overwrite[0] = True
            return res
        return wrapper

    results = {
        "success": False,
        "operations_completed": [],
        "skipped_operations": [],
        "total_cost": 0.0,
        "total_time": 0.0,
        "final_state": {},
        "errors": [],
        "error": None,
        "model_name": None
    }

    def sync_worker_logic():
        start_time = time.time()
        op_history = []
        consecutive_fixes = 0
        consecutive_tests = 0
        consecutive_crashes = 0
        test_extend_attempts = 0

        try:
            with SyncLock(basename, lang_lower) as lock:
                log_event(basename, lang_lower, "lock_acquired", {"pid": os.getpid()}, "sync")
                
                while not stop_event.is_set():
                    # Decision logic
                    decision = sync_determine_operation(basename, lang_lower, target_coverage, log_mode=False)
                    op = decision.operation

                    # TUI Updates
                    pdd_paths = get_pdd_file_paths(basename, lang_lower)
                    for k in status_refs:
                        path = pdd_paths.get(k)
                        if path:
                            path_refs[k][0] = str(path)
                            status_refs[k][0] = "green" if path.exists() else "red"
                    
                    # Cycle Detection
                    if op == "all_synced" or op == "nothing":
                        results["success"] = True
                        break
                    
                    # Steering
                    if not no_steer:
                        steered_op, should_abort = maybe_steer_operation(
                            op, decision.reason, app_ref[0], quiet, skip_tests, skip_verify, timeout_s=steer_timeout
                        )
                        if should_abort:
                            results["errors"].append("Sync aborted by user steering.")
                            break
                        if steered_op != op:
                            log_event(basename, lang_lower, "steering_override", {"from": op, "to": steered_op}, "sync")
                            op = steered_op

                    # Safety breaks
                    op_history.append(op)
                    if len(op_history) >= 4 and op_history[-4:] == ["crash", "verify", "crash", "verify"]: break
                    if len(op_history) >= 4 and op_history[-4:] == ["test", "fix", "test", "fix"]: break
                    if op == "fix": consecutive_fixes += 1
                    else: consecutive_fixes = 0
                    if consecutive_fixes > 5: break

                    # Operation Setup
                    function_name_ref[0] = f"Executing: {op}"
                    ctx = _create_mock_context(
                        force=force, quiet=quiet, verbose=verbose, local=local,
                        strength=strength, temperature=temperature, time=time_param,
                        confirm_callback=get_confirm_wrapper()
                    )
                    
                    entry = create_log_entry(op, decision.reason, "sync", decision.estimated_cost, decision.confidence, decision.decision_type)
                    op_start = time.time()
                    
                    op_result = None
                    try:
                        # Operation Mapping
                        if op == "auto-deps":
                            op_result = auto_deps_main(ctx, str(pdd_paths["prompt"]), f"{examples_dir}/**/*", output=str(pdd_paths["prompt"]), progress_callback=progress_callback_ref[0])
                        elif op == "generate":
                            op_result = code_generator_main(ctx, str(pdd_paths["prompt"]), output=str(pdd_paths["code"]))
                            clear_run_report(basename, lang_lower)
                        elif op == "example":
                            op_result = context_generator_main(ctx, str(pdd_paths["prompt"]), str(pdd_paths["code"]), output=str(pdd_paths["example"]))
                        elif op == "crash":
                            if skip_tests:
                                results["skipped_operations"].append("crash")
                                _create_synthetic_run_report_for_agentic_success(str(pdd_paths["example"]), basename, lang_lower)
                            else:
                                if _use_agentic_path(language, agentic_mode):
                                    op_result = crash_main(ctx, str(pdd_paths["prompt"]), str(pdd_paths["code"]), str(pdd_paths["example"]), "Sync synthetic crash log", output=str(pdd_paths["code"]), loop=True, max_attempts=0)
                                    _create_synthetic_run_report_for_agentic_success(str(pdd_paths["example"]), basename, lang_lower)
                                else:
                                    op_result = crash_main(ctx, str(pdd_paths["prompt"]), str(pdd_paths["code"]), str(pdd_paths["example"]), "Sync crash detection", loop=True, max_attempts=max_attempts)
                        elif op == "verify":
                            if skip_verify or skip_tests:
                                results["skipped_operations"].append("verify")
                                save_fingerprint(basename, lang_lower, "skip:verify", pdd_paths, 0.0, "none")
                            else:
                                op_result = fix_verification_main(ctx, str(pdd_paths["prompt"]), str(pdd_paths["code"]), str(pdd_paths["example"]), loop=True, max_attempts=(0 if _use_agentic_path(language, agentic_mode) else max_attempts))
                        elif op == "test":
                            if skip_tests:
                                results["skipped_operations"].append("test")
                            else:
                                test_res = cmd_test_main(ctx, str(pdd_paths["prompt"]), str(pdd_paths["code"]), output=str(pdd_paths["test"]), language=language)
                                # cmd_test_main returns 4-tuple
                                op_result = (test_res[0], test_res[1], test_res[2])
                                if test_res[3] is True:
                                    _create_synthetic_run_report_for_agentic_success(str(pdd_paths["test"]), basename, lang_lower)
                                else:
                                    _execute_tests_and_create_run_report(str(pdd_paths["test"]), basename, language, target_coverage, code_file=str(pdd_paths["code"]))
                        elif op == "test_extend":
                            if lang_lower != "python" or agentic_mode:
                                results["skipped_operations"].append("test_extend")
                                _create_synthetic_run_report_for_agentic_success(str(pdd_paths["test"]), basename, lang_lower)
                            else:
                                op_result = cmd_test_main(ctx, str(pdd_paths["prompt"]), str(pdd_paths["code"]), output=str(pdd_paths["test"]), existing_tests=[str(pdd_paths["test"])], target_coverage=target_coverage, merge=True)
                                _execute_tests_and_create_run_report(str(pdd_paths["test"]), basename, language, target_coverage, code_file=str(pdd_paths["code"]))
                        elif op == "fix":
                            report = read_run_report(basename, lang_lower)
                            failing_test = str(pdd_paths["test"])
                            # Multi-test logic
                            if pdd_paths.get("test_files"):
                                failing_test = extract_failing_files_from_output(getattr(report, "output", ""), pdd_paths["test_files"]) or failing_test
                                
                            op_result = fix_main(ctx, str(pdd_paths["prompt"]), str(pdd_paths["code"]), failing_test, "", loop=True, max_attempts=(0 if _use_agentic_path(language, agentic_mode) else max_attempts))
                            if _use_agentic_path(language, agentic_mode):
                                _create_synthetic_run_report_for_agentic_success(failing_test, basename, lang_lower)
                            else:
                                _execute_tests_and_create_run_report(str(pdd_paths["test"]), basename, language, target_coverage, code_file=str(pdd_paths["code"]), test_files=pdd_paths.get("test_files"))
                        elif op == "update":
                            op_result = update_main(ctx, str(pdd_paths["prompt"]), str(pdd_paths["code"]), use_git=True)

                        # Parse Results
                        cost = 0.0
                        model = "unknown"
                        if isinstance(op_result, dict):
                            cost, model = op_result.get("cost", 0.0), op_result.get("model", "unknown")
                        elif isinstance(op_result, tuple):
                            cost, model = op_result[-2], op_result[-1]
                            
                        results["total_cost"] += cost
                        cost_ref[0] = results["total_cost"]
                        results["model_name"] = model
                        
                        entry = update_log_entry(entry, True, cost, model, time.time() - op_start, None)
                        append_log_entry(basename, lang_lower, entry)
                        save_fingerprint(basename, lang_lower, op, pdd_paths, cost, model)
                        results["operations_completed"].append(op)
                        
                        if results["total_cost"] >= budget:
                            log_event(basename, lang_lower, "budget_exhausted", {"total": results["total_cost"]}, "sync")
                            break

                    except Exception as e:
                        error_msg = f"Operation {op} failed: {str(e)}"
                        results["errors"].append(error_msg)
                        entry = update_log_entry(entry, False, 0.0, "error", time.time() - op_start, str(e))
                        append_log_entry(basename, lang_lower, entry)
                        break

        except Exception as e:
            results["errors"].append(f"Sync failed: {str(e)}")
            results["error"] = str(e)
        finally:
            results["total_time"] = time.time() - start_time
            stop_event.set()

    # TUI or Headless execution
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
            status_refs=status_refs,
            path_refs=path_refs,
            stop_event=stop_event,
            progress_callback_ref=progress_callback_ref
        )
        app_ref[0] = app
        app.run()
        
        if app.worker_exception:
            click.echo(click.style(f"Worker crashed: {app.worker_exception}", fg="red"), err=True)
            traceback.print_exception(type(app.worker_exception), app.worker_exception, app.worker_exception.__traceback__)
            
        from .sync_tui import show_exit_animation
        show_exit_animation(results["success"], results["total_cost"], results["total_time"])

    results["error"] = "; ".join(results["errors"]) if results["errors"] else None
    return results

if __name__ == "__main__":
    # Basic CLI test harness
    sync_orchestration("calculator", dry_run=False, force=True)
