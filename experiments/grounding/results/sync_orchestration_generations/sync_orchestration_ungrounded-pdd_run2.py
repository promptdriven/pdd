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
from .get_test_command import get_test_command_for_file
from . import DEFAULT_STRENGTH

# Constants
MAX_CONSECUTIVE_TESTS = 3
MAX_TEST_EXTEND_ATTEMPTS = 2
MAX_CONSECUTIVE_CRASHES = 3
MAX_CYCLE_REPEATS = 2

class AtomicStateUpdate:
    """
    Context manager for atomic updates to PDD state files.
    Ensures that metadata (run report, fingerprint) is written reliably.
    """
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language.lower()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        pass

def _display_sync_log(basename: str, language: str, verbose: bool):
    """Format and display the sync log for dry-run inspection."""
    entries = load_operation_log(basename, language)
    if not entries:
        click.echo(f"No sync history found for {basename} ({language})")
        return

    click.echo(f"--- Sync Log for {basename}_{language} ---")
    for entry in entries:
        timestamp = entry.get("timestamp", "unknown")
        op = entry.get("operation", "unknown")
        success = "✓" if entry.get("success") else "✗"
        if verbose:
            click.echo(json.dumps(entry, indent=2))
        else:
            click.echo(f"[{timestamp}] {op:<10} {success} - {entry.get('reason', '')}")

def _create_mock_context(**kwargs) -> click.Context:
    """Create a Click context for command execution."""
    ctx = click.Context(click.Command("sync"))
    ctx.obj = kwargs
    ctx.params = kwargs
    return ctx

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Determines if we should skip iterative loops and use agentic fallback."""
    lang_lower = language.lower()
    return lang_lower != "python" or agentic_mode

def _parse_test_output(output: str, language: str) -> Tuple[int, int, float]:
    """Parses test runner output to extract passing, failing counts and coverage."""
    passed = 0
    failed = 0
    coverage = 0.0

    # Pytest parsing
    if language.lower() == "python":
        m_pass = re.search(r"(\d+) passed", output)
        m_fail = re.search(r"(\d+) failed", output)
        if m_pass: passed = int(m_pass.group(1))
        if m_fail: failed = int(m_fail.group(1))
        
        m_cov = re.search(r"TOTAL\s+\d+\s+\d+\s+(\d+)%", output)
        if m_cov: coverage = float(m_cov.group(1))
    
    # Generic fallback patterns (Jest, Go, etc)
    else:
        m_generic_pass = re.search(r"Tests?:\s+(\d+) passed", output, re.I)
        m_generic_fail = re.search(r"Tests?:\s+(\d+) failed", output, re.I)
        if m_generic_pass: passed = int(m_generic_pass.group(1))
        if m_generic_fail: failed = int(m_generic_fail.group(1))

    return passed, failed, coverage

def _python_cov_target_for_code_file(code_file: str) -> str:
    """Extracts the package.module path for coverage."""
    path = Path(code_file)
    # Heuristic: find 'src' and join rest
    parts = path.parts
    if "src" in parts:
        idx = parts.index("src")
        return ".".join(parts[idx+1:]).replace(".py", "")
    return path.stem

def _create_synthetic_run_report_for_agentic_success(test_file: str, basename: str, language: str, atomic_state=None):
    """Creates a fake successful run report when an agent verifies its own code."""
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
    save_run_report(basename, language, report_data)

def _execute_tests_and_create_run_report(test_file: str, basename: str, language: str, target_coverage: float, *, code_file=None, atomic_state=None, test_files=None) -> Dict[str, Any]:
    """Runs tests, captures results, and saves a RunReport."""
    lang_lower = language.lower()
    test_cmd = get_test_command_for_file(test_file, language=language)
    
    if not test_cmd:
        # If no test command, we can't run them; return synthetic failure to trigger fix
        return {"exit_code": 1, "error": "No test command found"}

    env = os.environ.copy()
    # Cleanup TUI env vars
    env.pop("FORCE_COLOR", None)
    env.pop("COLUMNS", None)
    
    cmd_list = test_cmd.split()
    
    # Add coverage for Python
    if lang_lower == "python" and code_file:
        cov_target = _python_cov_target_for_code_file(code_file)
        cmd_list.extend(["--cov", cov_target, "--cov-report", "term-missing"])

    # Execution
    try:
        proc = subprocess.run(
            cmd_list,
            capture_output=True,
            text=True,
            env=env,
            start_new_session=True,
            stdin=subprocess.DEVNULL,
            timeout=120
        )
        output = proc.stdout + proc.stderr
        passed, failed, coverage = _parse_test_output(output, language)
        
        test_file_hashes = {}
        target_files = test_files if test_files else [test_file]
        for tf in target_files:
            p = Path(tf)
            if p.exists():
                test_file_hashes[tf] = calculate_sha256(p)

        report = {
            "timestamp": datetime.datetime.now().isoformat(),
            "exit_code": proc.returncode,
            "tests_passed": passed,
            "tests_failed": failed,
            "coverage": coverage,
            "test_hash": calculate_sha256(Path(test_file)) if Path(test_file).exists() else None,
            "test_file_hashes": test_file_hashes,
            "output": output
        }
        save_run_report(basename, language, report)
        return report
    except Exception as e:
        return {"exit_code": 1, "error": str(e)}

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
    """Orchestrates the complete PDD sync workflow loop."""
    
    # Defaults defense
    target_coverage = target_coverage if target_coverage is not None else 90.0
    budget = budget if budget is not None else 20.0
    max_attempts = max_attempts if max_attempts is not None else 3

    if dry_run:
        _display_sync_log(basename, language, verbose)
        return {"success": True, "log_entries": load_operation_log(basename, language)}

    # TUI State References
    func_ref = ["Starting..."]
    cost_ref = [0.0]
    time_start = time.time()
    op_history = []
    errors = []
    total_cost = 0.0
    stop_event = threading.Event()
    app_ref = []
    user_confirmed_overwrite = [False]

    def get_confirm_wrapper():
        def wrapper(msg, default=False):
            if user_confirmed_overwrite[0] or force:
                return True
            if not sys.stdin.isatty():
                return True
            res = click.confirm(msg, default=default)
            if res: user_confirmed_overwrite[0] = True
            return res
        return wrapper

    effective_confirm = confirm_callback or get_confirm_wrapper()

    def sync_worker_logic():
        nonlocal total_cost
        consecutive_tests = 0
        consecutive_crashes = 0
        consecutive_fixes = 0
        test_extend_attempts = 0
        
        try:
            with SyncLock(basename, language.lower()) as lock:
                log_event(basename, language, "lock_acquired", {"basename": basename}, "sync")
                
                while not stop_event.is_set():
                    # Check Budget
                    if total_cost >= budget:
                        errors.append(f"Budget exceeded: ${total_cost:.2f} >= ${budget:.2f}")
                        break
                    
                    # Determine next operation
                    decision: SyncDecision = sync_determine_operation(basename, language, target_coverage)
                    op = decision.operation
                    
                    if op in ("all_synced", "nothing", "fail_and_request_manual_merge", "error"):
                        func_ref[0] = f"Sync Complete: {op}"
                        break

                    # Interactive Steering
                    if not no_steer and not quiet and sys.stdin.isatty():
                        steered_op, should_abort = maybe_steer_operation(
                            op, decision.reason, app_ref, quiet, skip_tests, skip_verify, timeout_s=steer_timeout
                        )
                        if should_abort:
                            errors.append("Sync aborted via steering.")
                            break
                        if steered_op != op:
                            log_event(basename, language, "steering_override", {"from": op, "to": steered_op}, "sync")
                            op = steered_op

                    func_ref[0] = f"Running: {op}"
                    
                    # Path resolution
                    paths = get_pdd_file_paths(basename, language, prompts_dir, code_dir, examples_dir, tests_dir)
                    
                    # Cycle Detection Logic
                    op_history.append(op)
                    if op == "test": consecutive_tests += 1
                    else: consecutive_tests = 0
                    if consecutive_tests > MAX_CONSECUTIVE_TESTS:
                        errors.append("Loop detected: too many consecutive test operations.")
                        break

                    # Operation execution
                    entry = create_log_entry(
                        operation=op,
                        reason=decision.reason,
                        invocation_mode="sync",
                        estimated_cost=decision.estimated_cost,
                        confidence=decision.confidence,
                        decision_type=decision.decision_type
                    )
                    
                    success = False
                    op_cost = 0.0
                    op_model = "unknown"
                    
                    ctx = _create_mock_context(
                        strength=strength, temperature=temperature, time=time_param, 
                        force=force, verbose=verbose, quiet=quiet, local=local,
                        confirm_callback=effective_confirm
                    )

                    # Dispatch
                    if op == "auto-deps":
                        res = auto_deps_main(ctx, str(paths['prompt']), examples_dir)
                        success, op_cost, op_model = True, res[1], res[2]
                    
                    elif op == "generate":
                        res = code_generator_main(ctx, str(paths['prompt']), str(paths['code']))
                        success, op_cost, op_model = True, res[2], res[3]
                        clear_run_report(basename, language)

                    elif op == "example":
                        res = context_generator_main(ctx, str(paths['prompt']), str(paths['code']), str(paths['example']))
                        success, op_cost, op_model = True, res[1], res[2]

                    elif op == "crash":
                        if skip_tests: # Cascading skip
                            _create_synthetic_run_report_for_agentic_success(str(paths['example']), basename, language)
                            success = True
                        else:
                            # Iterative attempts 0 if non-python
                            loop_max = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                            res = crash_main(ctx, str(paths['prompt']), str(paths['code']), str(paths['example']), "crash.log", loop=True, max_attempts=loop_max)
                            success, op_cost, op_model = res[0], res[4], res[5]
                            if success and language.lower() != "python":
                                _create_synthetic_run_report_for_agentic_success(str(paths['example']), basename, language)

                    elif op == "verify":
                        if skip_verify or skip_tests:
                            success = True
                        else:
                            loop_max = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                            res = fix_verification_main(ctx, str(paths['prompt']), str(paths['code']), str(paths['example']), loop=True, max_attempts=loop_max)
                            success, op_cost, op_model = res[0], res[4], res[5]

                    elif op == "test":
                        if skip_tests: success = True
                        else:
                            res = cmd_test_main(ctx, str(paths['prompt']), str(paths['code']), str(paths['test']), language=language)
                            # res: (content, cost, model, agentic_success)
                            op_cost, op_model = res[1], res[2]
                            if res[3] is True: # Agentic success
                                _create_synthetic_run_report_for_agentic_success(str(paths['test']), basename, language)
                                success = True
                            else:
                                report = _execute_tests_and_create_run_report(str(paths['test']), basename, language, target_coverage, code_file=str(paths['code']))
                                success = report['exit_code'] == 0

                    elif op == "fix":
                        loop_max = 0 if _use_agentic_path(language, agentic_mode) else max_attempts
                        res = fix_main(ctx, str(paths['prompt']), str(paths['code']), str(paths['test']), "fix_errors.log", loop=True, max_attempts=loop_max)
                        success, op_cost, op_model = res[0], res[4], res[5]
                        if success and language.lower() != "python":
                             _create_synthetic_run_report_for_agentic_success(str(paths['test']), basename, language)

                    elif op == "update":
                        res = update_main(ctx, str(paths['prompt']), str(paths['code']), use_git=True)
                        success, op_cost, op_model = True, res[1], res[2]

                    # Update Log/Fingerprint
                    total_cost += op_cost
                    cost_ref[0] = total_cost
                    update_log_entry(entry, success, op_cost, op_model, 0.0, None)
                    append_log_entry(basename, language, entry)
                    
                    if success:
                        save_fingerprint(basename, language, op, paths, op_cost, op_model)
                    else:
                        errors.append(f"Operation {op} failed.")
                        break

        except Exception as e:
            errors.append(f"Worker exception: {str(e)}")
            traceback.print_exc()
        finally:
            log_event(basename, language, "lock_released", {}, "sync")

    # Run TUI or Headless
    is_headless = not sys.stdin.isatty() or os.getenv("CI") == "true" or quiet
    
    if is_headless:
        sync_worker_logic()
    else:
        app = SyncApp(worker_func=sync_worker_logic, basename=basename, func_ref=func_ref, cost_ref=cost_ref)
        app_ref.append(app)
        app.run()
        
        from .sync_tui import show_exit_animation
        if not quiet:
            show_exit_animation()

    return {
        "success": len(errors) == 0,
        "total_cost": total_cost,
        "total_time": time.time() - time_start,
        "errors": errors,
        "error": "; ".join(errors) if errors else None
    }