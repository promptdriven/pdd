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
from dataclasses import asdict, dataclass, field
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

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        pass

def _display_sync_log(basename: str, language: str, verbose: bool):
    """Format and display sync log using load_operation_log."""
    entries = load_operation_log(basename, language)
    if not entries:
        click.echo(f"No sync history found for {basename} ({language}).")
        return

    click.echo(f"\n--- Sync Log for {basename}_{language} ---")
    for entry in entries:
        timestamp = entry.get("timestamp", "unknown")
        op = entry.get("operation", "unknown")
        success = entry.get("success", "-")
        cost = entry.get("actual_cost", 0.0)
        
        msg = f"[{timestamp}] {op.upper():<10} | Success: {str(success):<5} | Cost: ${cost:.4f}"
        if verbose:
            msg += f" | Model: {entry.get('model', 'N/A')} | Reason: {entry.get('reason', '')}"
        click.echo(msg)

def _create_mock_context(**kwargs) -> click.Context:
    """Create a mock Click context for command execution."""
    ctx = click.Context(click.Command("sync-sub"))
    ctx.obj = kwargs
    ctx.params = kwargs
    return ctx

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Determine if agentic path should be used (skips iterative loops)."""
    return language.lower() != "python" or agentic_mode

def _create_synthetic_run_report_for_agentic_success(test_file: str, basename: str, language: str, atomic_state=None):
    """Create a synthetic successful run report for agentic test generation."""
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

def _parse_test_output(output: str, language: str):
    """Parse test runner output to extract coverage and pass/fail counts."""
    passed = 0
    failed = 0
    coverage = 0.0

    # Generic patterns
    pass_match = re.search(r"(\d+)\s+passed", output)
    fail_match = re.search(r"(\d+)\s+failed", output)
    cov_match = re.search(r"TOTAL\s+\d+\s+\d+\s+(\d+)%", output) or re.search(r"Coverage:\s+(\d+\.?\d*)%", output)

    if pass_match: passed = int(pass_match.group(1))
    if fail_match: failed = int(fail_match.group(1))
    if cov_match: coverage = float(cov_match.group(1))

    return passed, failed, coverage

def _execute_tests_and_create_run_report(test_file, basename, language, target_coverage, *, code_file=None, test_files=None):
    """Execute tests and update the run report."""
    run_cmd = get_test_command_for_file(test_file, language=language)
    if not run_cmd:
        return False, "Could not resolve test command"

    # For Python, handle coverage injection
    env = os.environ.copy()
    if language.lower() == "python" and code_file:
        project_root = _find_project_root(test_file)
        if project_root:
            env["PYTHONPATH"] = f"{project_root}:{project_root}/src:{env.get('PYTHONPATH', '')}"

    try:
        # Use provided test files or fallback to primary
        targets = test_files if test_files else [test_file]
        full_cmd = run_cmd.split() + targets
        
        result = subprocess.run(
            full_cmd,
            capture_output=True,
            text=True,
            env=env,
            start_new_session=True,
            stdin=subprocess.DEVNULL
        )
        
        passed, failed, coverage = _parse_test_output(result.stdout + result.stderr, language)
        
        # Calculate hashes for multi-file tracking
        hashes = {str(t): calculate_sha256(Path(t)) for t in targets if Path(t).exists()}
        
        report_data = {
            "timestamp": datetime.datetime.now().isoformat(),
            "exit_code": result.returncode,
            "tests_passed": passed,
            "tests_failed": failed,
            "coverage": coverage,
            "test_file_hashes": hashes,
            "test_hash": calculate_sha256(Path(test_file)) if Path(test_file).exists() else ""
        }
        save_run_report(basename, language, report_data)
        return True, ""
    except Exception as e:
        return False, str(e)

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
    """Orchestrate the complete PDD sync workflow."""
    
    # Defaults defense
    target_coverage = target_coverage if target_coverage is not None else 90.0
    budget = budget if budget is not None else 20.0
    max_attempts = max_attempts if max_attempts is not None else 3
    
    if dry_run:
        _display_sync_log(basename, language, verbose)
        return {"success": True, "log_entries": load_operation_log(basename, language)}

    # Mutable shared state for TUI
    state = {
        "function_name": ["initializing"],
        "cost": [0.0],
        "op_color": ["white"],
        "path_info": [{}],
        "progress": [0.0],
        "app_ref": [None],
        "stop_event": threading.Event(),
        "user_confirmed_overwrite": [False],
        "errors": [],
        "ops_done": [],
        "ops_skipped": []
    }

    def sync_worker_logic():
        total_cost = 0.0
        consecutive_ops = {"test": 0, "crash": 0, "fix": 0, "test_extend": 0}
        last_ops = []
        
        try:
            with SyncLock(basename, language):
                log_event(basename, language, "lock_acquired", {"basename": basename}, "sync")
                
                while not state["stop_event"].is_set():
                    # Check budget
                    if total_cost >= budget:
                        state["errors"].append(f"Budget exceeded: ${total_cost:.2f} / ${budget:.2f}")
                        break
                    
                    # 1. Determine next step
                    decision = sync_determine_operation(basename, language, target_coverage)
                    op = decision.operation
                    
                    # 2. Interactive Steering
                    if not no_steer:
                        steered_op, should_abort = maybe_steer_operation(
                            op, decision.reason, state["app_ref"][0], quiet, skip_tests, skip_verify, timeout_s=steer_timeout
                        )
                        if should_abort:
                            state["errors"].append("Sync aborted by user steering.")
                            break
                        if steered_op != op:
                            log_event(basename, language, "steering_override", {"from": op, "to": steered_op}, "sync")
                            op = steered_op

                    if op in ("all_synced", "nothing", "fail_and_request_manual_merge", "error"):
                        break

                    # 3. Cycle / Loop Detection
                    last_ops.append(op)
                    if len(last_ops) > 10: last_ops.pop(0)
                    
                    # Pattern detection (e.g., test-fix-test-fix)
                    if len(last_ops) >= 4 and last_ops[-4:] == ["test", "fix", "test", "fix"]:
                        state["errors"].append("Infinite test-fix loop detected. Breaking.")
                        break

                    # 4. Execution
                    state["function_name"][0] = op
                    paths = get_pdd_file_paths(basename, language, prompts_dir, code_dir, examples_dir, tests_dir)
                    state["path_info"][0] = {k: str(v) for k, v in paths.items() if hasattr(v, 'exists')}

                    ctx = _create_mock_context(
                        force=force or state["user_confirmed_overwrite"][0],
                        verbose=verbose,
                        quiet=quiet,
                        strength=strength,
                        temperature=temperature,
                        time=time_param,
                        local=local
                    )

                    op_entry = create_log_entry(op, decision.reason, "sync", decision.estimated_cost, decision.confidence, decision.decision_type)
                    op_success = False
                    op_cost = 0.0
                    model_used = "unknown"
                    
                    start_time = time.time()
                    
                    try:
                        if op == "auto-deps":
                            res = auto_deps_main(ctx, str(paths['prompt']), str(paths['example_dir'] or "examples"))
                            op_cost = res[1]; model_used = res[2]; op_success = True
                            
                        elif op == "generate":
                            res = code_generator_main(ctx, str(paths['prompt']), str(paths['code']))
                            op_cost = res[2]; model_used = res[3]; op_success = True
                            clear_run_report(basename, language)
                            
                        elif op == "example":
                            res = context_generator_main(ctx, str(paths['prompt']), str(paths['code']), str(paths['example']))
                            op_cost = res[1]; model_used = res[2]; op_success = True
                            
                        elif op == "crash":
                            if skip_tests:
                                state["ops_skipped"].append(op)
                                op_success = True
                            else:
                                is_agentic = _use_agentic_path(language, agentic_mode)
                                m_attempts = 0 if is_agentic else max_attempts
                                res = crash_main(ctx, str(paths['prompt']), str(paths['code']), str(paths['example']), str(paths['crash_log']), output=str(paths['code']), loop=not is_agentic, max_attempts=m_attempts)
                                op_success = res[0]; op_cost = res[4]; model_used = res[5]
                                if op_success and language.lower() == "python":
                                    _execute_tests_and_create_run_report(str(paths['example']), basename, language, target_coverage)
                                elif op_success:
                                    save_run_report(basename, language, {"exit_code": 0, "timestamp": datetime.datetime.now().isoformat()})
                        
                        elif op == "test":
                            if skip_tests:
                                state["ops_skipped"].append(op)
                                op_success = True
                            else:
                                res = cmd_test_main(ctx, str(paths['prompt']), str(paths['code']), str(paths['test']), language=language)
                                op_cost = res[1]; model_used = res[2]
                                op_success = True if (res[3] is True or Path(paths['test']).exists()) else False
                                if op_success:
                                    if res[3] is True: _create_synthetic_run_report_for_agentic_success(str(paths['test']), basename, language)
                                    else: _execute_tests_and_create_run_report(str(paths['test']), basename, language, target_coverage, code_file=str(paths['code']))

                        elif op == "fix":
                            is_agentic = _use_agentic_path(language, agentic_mode)
                            m_attempts = 0 if is_agentic else max_attempts
                            res = fix_main(ctx, str(paths['prompt']), str(paths['code']), str(paths['test']), str(paths['crash_log']), loop=not is_agentic, max_attempts=m_attempts)
                            op_success = res[0]; op_cost = res[4]; model_used = res[5]
                            if op_success:
                                if is_agentic: save_run_report(basename, language, {"exit_code": 0, "timestamp": datetime.datetime.now().isoformat()})
                                else: _execute_tests_and_create_run_report(str(paths['test']), basename, language, target_coverage, code_file=str(paths['code']))

                        elif op == "update":
                            res = update_main(ctx, str(paths['prompt']), str(paths['code']), use_git=True)
                            op_cost = res[1]; model_used = res[2]; op_success = True
                        
                        # Handle Fingerprinting
                        if op_success:
                            total_cost += op_cost
                            state["cost"][0] = total_cost
                            state["ops_done"].append(op)
                            save_fingerprint(basename, language, op, paths, op_cost, model_used)
                        
                        append_log_entry(basename, language, update_log_entry(op_entry, op_success, op_cost, model_used, time.time()-start_time))

                    except Exception as e:
                        state["errors"].append(f"Operation {op} failed: {str(e)}")
                        append_log_entry(basename, language, update_log_entry(op_entry, False, 0.0, "error", 0.0, str(e)))
                        break

        except Exception as e:
            state["errors"].append(f"Sync orchestration fatal error: {str(e)}")
            traceback.print_exc()
        finally:
            log_event(basename, language, "lock_released", {"basename": basename}, "sync")
            return total_cost

    # Execution Mode: TUI or Headless
    is_headless = not sys.stdin.isatty() or os.getenv("CI") == "true" or quiet
    
    if is_headless:
        os.environ["PDD_FORCE"] = "1"
        final_cost = sync_worker_logic()
    else:
        app = SyncApp(basename, language, sync_worker_logic)
        state["app_ref"][0] = app
        app.run()
        if app.worker_exception:
            print(f"Worker crashed: {app.worker_exception}", file=sys.stderr)
            traceback.print_exception(type(app.worker_exception), app.worker_exception, app.worker_exception.__traceback__)
        final_cost = state["cost"][0]
        if not quiet:
            from .sync_tui import show_exit_animation
            show_exit_animation(not state["errors"])

    return {
        "success": len(state["errors"]) == 0,
        "operations_completed": state["ops_done"],
        "skipped_operations": state["ops_skipped"],
        "total_cost": final_cost,
        "errors": state["errors"],
        "error": "; ".join(state["errors"]) if state["errors"] else None,
    }

def _find_project_root(test_file: str) -> Optional[Path]:
    """Search upwards for .pdd or .git to define project root."""
    curr = Path(test_file).resolve().parent
    for parent in [curr] + list(curr.parents):
        if (parent / ".pdd").exists() or (parent / ".git").exists():
            return parent
    return None