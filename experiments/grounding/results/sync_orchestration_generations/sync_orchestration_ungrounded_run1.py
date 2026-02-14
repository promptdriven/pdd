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
from .sync_tui import maybe_steer_operation, DEFAULT_STEER_TIMEOUT_S, SyncApp, show_exit_animation
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
    """Context manager for consistent state writes (fingerprint + run report)."""
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language.lower()
        self.pending_fingerprint = None
        self.pending_run_report = None

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            if self.pending_fingerprint:
                save_fingerprint(self.basename, self.language, **self.pending_fingerprint)
            if self.pending_run_report:
                save_run_report(self.basename, self.language, self.pending_run_report)

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Returns True if we should use agentic path (non-Python OR agentic_mode)."""
    return (language.lower() != "python") or agentic_mode

def _display_sync_log(basename: str, language: str, verbose: bool):
    """Format and display sync log."""
    entries = load_operation_log(basename, language)
    if not entries:
        click.echo(f"No sync history found for {basename}_{language}")
        return

    click.echo(f"\n--- Sync Log for {basename}_{language} ---")
    for entry in entries:
        timestamp = entry.get("timestamp", "N/A")
        op = entry.get("operation", "N/A")
        success = entry.get("success", "N/A")
        cost = entry.get("actual_cost", 0.0)
        
        line = f"[{timestamp}] {op.upper()}: Success={success}, Cost=${cost:.4f}"
        if verbose:
            reason = entry.get("reason", "")
            model = entry.get("model", "")
            line += f"\n  Reason: {reason}\n  Model: {model}"
        click.echo(line)

def _create_mock_context(**kwargs) -> click.Context:
    """Create a mock Click context for internal command calls."""
    ctx = click.Context(click.Command("sync_internal"))
    ctx.obj = {
        "verbose": kwargs.get("verbose", False),
        "quiet": kwargs.get("quiet", False),
        "force": kwargs.get("force", False),
        "strength": kwargs.get("strength", DEFAULT_STRENGTH),
        "temperature": kwargs.get("temperature", 0.0),
        "time": kwargs.get("time_param", 0.25),
        "local": kwargs.get("local", False),
        "confirm_callback": kwargs.get("confirm_callback"),
    }
    ctx.params = ctx.obj.copy()
    return ctx

def _parse_test_output(output: str, language: str) -> Tuple[int, int, float]:
    """Parse test runner output to extract results."""
    passed = 0
    failed = 0
    coverage = 0.0
    
    # Python / Pytest
    if language.lower() == "python":
        passed_match = re.search(r"(\d+) passed", output)
        failed_match = re.search(r"(\d+) failed", output)
        cov_match = re.search(r"TOTAL\s+\d+\s+\d+\s+(\d+)%", output)
        if passed_match: passed = int(passed_match.group(1))
        if failed_match: failed = int(failed_match.group(1))
        if cov_match: coverage = float(cov_match.group(1))
    
    # JS / TS (Jest/Vitest)
    elif language.lower() in ("javascript", "typescript"):
        passed_match = re.search(r"Tests:\s+(\d+) passed", output)
        failed_match = re.search(r"Tests:\s+(\d+) failed", output)
        if passed_match: passed = int(passed_match.group(1))
        if failed_match: failed = int(failed_match.group(1))
        # Simple coverage heuristic
        cov_match = re.search(r"All files\s+\|\s+([\d.]+)", output)
        if cov_match: coverage = float(cov_match.group(1))

    return passed, failed, coverage

def _python_cov_target_for_code_file(code_file: str) -> str:
    """Determine module path for pytest-cov."""
    path = Path(code_file)
    if "src" in path.parts:
        idx = path.parts.index("src")
        parts = path.parts[idx+1:]
        return ".".join([p.replace(".py", "") for p in parts])
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
    """Runs tests and updates state."""
    from .get_test_command import get_test_command_for_file
    
    lang_lower = language.lower()
    all_tests = test_files or [test_file]
    
    cmd_str = get_test_command_for_file(test_file, language=lang_lower)
    if not cmd_str:
        return {"exit_code": 1, "error": "Could not resolve test command"}

    # Project root and path adjustments for Python
    env = os.environ.copy()
    env.pop("FORCE_COLOR", None)
    
    final_args = cmd_str.split()
    if lang_lower == "python":
        root = _find_project_root(test_file)
        if root:
            env["PYTHONPATH"] = f"{root}:{root}/src:" + env.get("PYTHONPATH", "")
            final_args.extend(["--rootdir", str(root), "-c", "/dev/null"])
        if code_file:
            cov_target = _python_cov_target_for_code_file(code_file)
            final_args.extend([f"--cov={cov_target}", "--cov-report=term-missing"])

    # Run command
    try:
        process = subprocess.run(
            final_args + (all_tests if lang_lower == "python" else []),
            capture_output=True, text=True, env=env, start_new_session=True
        )
        passed, failed, coverage = _parse_test_output(process.stdout + process.stderr, lang_lower)
        
        report = {
            "timestamp": datetime.datetime.now().isoformat(),
            "exit_code": process.returncode,
            "tests_passed": passed,
            "tests_failed": failed,
            "coverage": coverage,
            "test_hash": calculate_sha256(test_file),
            "test_file_hashes": {f: calculate_sha256(f) for f in all_tests}
        }
        
        if atomic_state:
            atomic_state.pending_run_report = report
        else:
            save_run_report(basename, lang_lower, report)
            
        return report
    except Exception as e:
        return {"exit_code": 1, "error": str(e)}

def _create_synthetic_run_report_for_agentic_success(
    test_file: str, basename: str, language: str, *, atomic_state: Optional[AtomicStateUpdate] = None
):
    """Saves a successful run report without execution."""
    lang_lower = language.lower()
    h = calculate_sha256(test_file) if Path(test_file).exists() else "agentic_test_success"
    report = {
        "timestamp": datetime.datetime.now().isoformat(),
        "exit_code": 0,
        "tests_passed": 1,
        "tests_failed": 0,
        "coverage": 100.0,
        "test_hash": h
    }
    if atomic_state:
        atomic_state.pending_run_report = report
    else:
        save_run_report(basename, lang_lower, report)

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
    
    # Defaults for CLI passing None
    target_coverage = target_coverage if target_coverage is not None else 90.0
    budget = budget if budget is not None else 20.0
    max_attempts = max_attempts if max_attempts is not None else 3

    if dry_run:
        _display_sync_log(basename, language, verbose)
        return {"success": True, "log_entries": load_operation_log(basename, language)}

    # Path Resolution
    try:
        pdd_files = get_pdd_file_paths(basename, language, prompts_dir, code_dir, examples_dir, tests_dir)
    except FileNotFoundError as e:
        # Fallback for missing tests
        pdd_files = {
            "prompt": Path(prompts_dir) / f"{basename}_{language}.prompt",
            "code": Path(code_dir) / f"{basename}.{language}", # Placeholder ext
            "example": Path(examples_dir) / f"{basename}_example.{language}",
            "test": Path(tests_dir) / f"test_{basename}.{language}",
        }

    # State Refs for TUI
    state_refs = {
        "function_name": ["initializing"],
        "cost": [0.0],
        "progress": [0.0],
        "app": [None],
        "stop": threading.Event(),
        "colors": {"prompt": "green", "code": "green", "example": "green", "test": "green"},
        "paths": pdd_files,
        "confirmed": [False]
    }

    results = {
        "success": False, "operations_completed": [], "skipped_operations": [],
        "total_cost": 0.0, "total_time": 0.0, "errors": [], "error": None, "model_name": None
    }

    start_time = time.time()

    def sync_worker_logic():
        consecutive_ops = {"test": 0, "crash": 0, "fix": 0}
        last_ops = []
        
        with SyncLock(basename, language.lower()) as lock:
            log_event(basename, language, "lock_acquired", {"lock_file": lock.lock_file})
            
            while not state_refs["stop"].is_set():
                decision = sync_determine_operation(basename, language, target_coverage)
                op = decision.operation

                # Steering
                if not no_steer:
                    op, should_abort = maybe_steer_operation(
                        op, decision.reason, state_refs["app"], quiet, skip_tests, skip_verify, steer_timeout
                    )
                    if should_abort:
                        results["error"] = "Sync aborted by user steering."
                        break
                    if op != decision.operation:
                        log_event(basename, language, "steering_override", {"from": decision.operation, "to": op})

                # Termination / Cycle Detection
                if op in ("all_synced", "nothing"):
                    results["success"] = True
                    break
                if op == "error":
                    results["error"] = decision.reason
                    break

                # Infinite loop protection
                last_ops.append(op)
                if len(last_ops) > 10: last_ops.pop(0)
                
                # Cycle patterns
                if last_ops[-4:] == ["crash", "verify", "crash", "verify"]: break
                if last_ops[-4:] == ["fix", "test", "fix", "test"]: break
                
                # Budget check
                if results["total_cost"] >= budget:
                    results["error"] = "Budget exceeded."
                    break

                # Execute Operation
                try:
                    op_success = _execute_operation(op, pdd_files, basename, language, target_coverage, 
                                                  max_attempts, results, state_refs, force, strength, 
                                                  temperature, time_param, local, agentic_mode, skip_verify, skip_tests)
                    if not op_success:
                        # Non-critical failure might allow retry or loop, but usually stop for safety
                        break
                except Exception as e:
                    results["errors"].append(f"Operation {op} failed: {str(e)}")
                    results["error"] = str(e)
                    break

        results["total_time"] = time.time() - start_time

    # TUI vs Headless
    is_headless = not sys.stdin.isatty() or os.environ.get("CI") == "true" or quiet
    if is_headless:
        os.environ["PDD_FORCE"] = "1"
        sync_worker_logic()
    else:
        app = SyncApp(worker_func=sync_worker_logic, state_refs=state_refs, basename=basename, language=language)
        state_refs["app"][0] = app
        app.run()
        if app.worker_exception:
            print(f"Worker crashed: {app.worker_exception}", file=sys.stderr)
            traceback.print_tb(app.worker_exception.__traceback__)
        show_exit_animation()

    return results

def _execute_operation(op, paths, basename, language, target_coverage, max_attempts, results, state_refs, 
                       force, strength, temperature, time_param, local, agentic_mode, skip_verify, skip_tests):
    """Executes a single sync operation."""
    state_refs["function_name"][0] = op
    ctx = _create_mock_context(force=force, strength=strength, temperature=temperature, 
                               time_param=time_param, local=local, verbose=ctx_verbose := state_refs["app"][0].verbose if state_refs["app"][0] else False)
    
    lang_lower = language.lower()
    atomic = AtomicStateUpdate(basename, language)
    
    # Generic wrapper for operation results
    def apply_res(res):
        if isinstance(res, tuple):
            cost, model = res[1], res[-1]
            if len(res) == 4: # Test result
                agentic_success = res[3]
                return True, cost, model, agentic_success
            return True, cost, model, None
        return res.get("success", False), res.get("cost", 0.0), res.get("model", "unknown"), None

    success = False
    with atomic as state:
        if op == "auto-deps":
            # auto-deps uses progress_callback
            res = auto_deps_main(ctx, str(paths["prompt"]), "examples/**/*.py", output=str(paths["prompt"]))
            success, cost, model, _ = apply_res(res)
            
        elif op == "generate":
            res = code_generator_main(ctx, str(paths["prompt"]), output=str(paths["code"]))
            success, cost, model, _ = apply_res(res)
            if success: clear_run_report(basename, lang_lower)

        elif op == "example":
            res = context_generator_main(ctx, str(paths["prompt"]), str(paths["code"]), output=str(paths["example"]))
            success, cost, model, _ = apply_res(res)

        elif op == "crash":
            if skip_tests:
                _create_synthetic_run_report_for_agentic_success(str(paths["test"]), basename, language, atomic_state=state)
                success, cost, model = True, 0.0, "skip"
            else:
                attempts = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                res = crash_main(ctx, str(paths["prompt"]), str(paths["code"]), str(paths["example"]), 
                                 "crash_log.txt", output=str(paths["code"]), loop=(attempts > 0), max_attempts=attempts)
                success, cost, model, _ = apply_res(res)
                if success:
                    if lang_lower == "python":
                        _execute_tests_and_create_run_report(str(paths["test"]), basename, language, target_coverage, code_file=str(paths["code"]), atomic_state=state)
                    else:
                        _create_synthetic_run_report_for_agentic_success(str(paths["test"]), basename, language, atomic_state=state)

        elif op == "verify":
            if skip_verify or skip_tests:
                success, cost, model = True, 0.0, "skip"
            else:
                attempts = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                res = fix_verification_main(ctx, str(paths["prompt"]), str(paths["code"]), str(paths["example"]),
                                            loop=(attempts > 0), max_attempts=attempts)
                success, cost, model, _ = apply_res(res)

        elif op == "test":
            res = cmd_test_main(ctx, str(paths["prompt"]), str(paths["code"]), output=str(paths["test"]), language=lang_lower)
            success, cost, model, agentic_success = apply_res(res)
            if success:
                if agentic_success is True:
                    _create_synthetic_run_report_for_agentic_success(str(paths["test"]), basename, language, atomic_state=state)
                else:
                    _execute_tests_and_create_run_report(str(paths["test"]), basename, language, target_coverage, code_file=str(paths["code"]), atomic_state=state)

        elif op == "test_extend":
            # Python only test extension
            if lang_lower != "python" or agentic_mode:
                success, cost, model = True, 0.0, "skip"
            else:
                res = cmd_test_main(ctx, str(paths["prompt"]), str(paths["code"]), output=str(paths["test"]), 
                                  existing_tests=[str(paths["test"])], merge=True, target_coverage=target_coverage)
                success, cost, model, _ = apply_res(res)
                if success:
                    _execute_tests_and_create_run_report(str(paths["test"]), basename, language, target_coverage, code_file=str(paths["code"]), atomic_state=state)

        elif op == "fix":
            attempts = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
            res = fix_main(ctx, str(paths["prompt"]), str(paths["code"]), str(paths["test"]), "errors.log", 
                           loop=(attempts > 0), max_attempts=attempts, output_code=str(paths["code"]))
            success, cost, model, _ = apply_res(res)
            if success:
                if lang_lower == "python" and not agentic_mode:
                    _execute_tests_and_create_run_report(str(paths["test"]), basename, language, target_coverage, code_file=str(paths["code"]), atomic_state=state)
                else:
                    _create_synthetic_run_report_for_agentic_success(str(paths["test"]), basename, language, atomic_state=state)

        elif op == "update":
            res = update_main(ctx, str(paths["prompt"]), str(paths["code"]), use_git=True)
            success, cost, model, _ = apply_res(res)

    if success:
        results["total_cost"] += cost
        results["operations_completed"].append(op)
        results["model_name"] = model
        state_refs["cost"][0] = results["total_cost"]
        save_fingerprint(basename, lang_lower, op, paths, cost, model)
    else:
        results["errors"].append(f"{op} failed.")
        
    return success
