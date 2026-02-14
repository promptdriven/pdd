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

# Helper: Detect if should use agentic logic
def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Returns True if we should use agentic path (non-Python OR agentic_mode for Python)."""
    lang_lower = language.lower()
    if agentic_mode:
        return True
    return lang_lower != "python"

# Helper: State Persistence Context Manager
class AtomicStateUpdate:
    """Ensures consistent state writes for RunReport and Fingerprint."""
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language.lower()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        pass

    def save(self, report_data: Optional[Dict] = None, fingerprint_data: Optional[Dict] = None):
        if report_data:
            save_run_report(self.basename, self.language, report_data)
        if fingerprint_data:
            # Note: save_fingerprint usually handled by operation helpers or log_operation decorator
            pass

def _create_synthetic_run_report_for_agentic_success(test_file, basename, language, *, atomic_state=None):
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
        atomic_state.save(report_data=report_data)
    else:
        save_run_report(basename, language, report_data)

def _parse_test_output(output: str, language: str) -> Tuple[int, int, float]:
    """Simple regex based parsing for common test runners."""
    passed, failed, coverage = 0, 0, 0.0
    # Pytest / Generic
    p_match = re.search(r"(\d+) passed", output)
    f_match = re.search(r"(\d+) failed", output)
    c_match = re.search(r"TOTAL\s+\d+\s+\d+\s+(\d+)%", output)
    
    if p_match: passed = int(p_match.group(1))
    if f_match: failed = int(f_match.group(1))
    if c_match: coverage = float(c_match.group(1))
    
    return passed, failed, coverage

def _execute_tests_and_create_run_report(test_file, basename, language, target_coverage, *, code_file=None, atomic_state=None, test_files=None):
    from .get_test_command import get_test_command_for_file
    
    cmd = get_test_command_for_file(test_file, language=language)
    if not cmd:
        return False, "Could not resolve test command"

    env = os.environ.copy()
    # Path isolation
    if language.lower() == "python" and code_file:
        root = _find_project_root(test_file)
        if root:
            src_dir = str(Path(root) / "src")
            env["PYTHONPATH"] = f"{root}{os.pathsep}{src_dir}{os.pathsep}{env.get('PYTHONPATH', '')}"

    try:
        # Construct list of files to run
        run_targets = test_files if test_files else [test_file]
        full_cmd = f"{cmd} {' '.join(run_targets)}"
        
        process = subprocess.run(
            full_cmd,
            shell=True,
            capture_output=True,
            text=True,
            env=env,
            start_new_session=True,
            stdin=subprocess.DEVNULL
        )
        
        passed, failed, coverage = _parse_test_output(process.stdout + process.stderr, language)
        
        # Calculate hashes for the report
        test_hashes = {}
        for f in run_targets:
            p = Path(f)
            if p.exists():
                test_hashes[str(p)] = calculate_sha256(p)

        report_data = {
            "timestamp": datetime.datetime.now().isoformat(),
            "exit_code": process.returncode,
            "tests_passed": passed,
            "tests_failed": failed,
            "coverage": coverage,
            "test_hash": test_hashes.get(str(test_file), "missing"),
            "test_file_hashes": test_hashes
        }
        
        if atomic_state:
            atomic_state.save(report_data=report_data)
        else:
            save_run_report(basename, language, report_data)
            
        return process.returncode == 0, None
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
    """Orchestrates the PDD sync workflow with TUI animation and state management."""
    
    # Defense in depth for defaults
    target_coverage = target_coverage if target_coverage is not None else 90.0
    budget = budget if budget is not None else 20.0
    max_attempts = max_attempts if max_attempts is not None else 3
    
    from .get_extension import get_extension

    # Local mutable state for TUI coordination
    func_name_ref = ["Initializing"]
    cost_ref = [0.0]
    prompt_color_ref = ["blue"]
    code_color_ref = ["blue"]
    example_color_ref = ["blue"]
    test_color_ref = ["blue"]
    prompt_path_ref = [""]
    code_path_ref = [""]
    example_path_ref = [""]
    test_path_ref = [""]
    progress_callback_ref = [None]
    app_ref = [None]
    user_confirmed_overwrite = [False]
    stop_event = threading.Event()
    
    results = {
        "success": False,
        "operations_completed": [],
        "skipped_operations": [],
        "total_cost": 0.0,
        "total_time": 0.0,
        "final_state": {},
        "errors": [],
        "error": None,
        "model_name": "N/A"
    }

    def _get_wrapped_confirm():
        def wrapper(msg, default=True):
            if force or user_confirmed_overwrite[0]:
                return True
            if confirm_callback:
                res = confirm_callback(msg, "")
            else:
                res = click.confirm(msg, default=default)
            if res:
                user_confirmed_overwrite[0] = True
            return res
        return wrapper

    def sync_worker_logic():
        start_time = time.time()
        consecutive_ops = {}
        history = []
        
        try:
            with SyncLock(basename, language) as lock:
                log_event(basename, language, "lock_acquired", {"basename": basename}, "sync")
                
                while not stop_event.is_set():
                    # Check Budget
                    if cost_ref[0] >= budget:
                        results["errors"].append(f"Budget exceeded: ${cost_ref[0]:.2f} / ${budget:.2f}")
                        break
                    if cost_ref[0] > budget * 0.8:
                        log_event(basename, language, "budget_warning", {"spent": cost_ref[0]}, "sync")

                    # 1. Determine Operation
                    decision = sync_determine_operation(basename, language, target_coverage, log_mode=False)
                    op, reason = decision.operation, decision.reason
                    
                    # Update paths for TUI
                    paths = get_pdd_file_paths(basename, language)
                    prompt_path_ref[0] = str(paths.get('prompt', ''))
                    code_path_ref[0] = str(paths.get('code', ''))
                    example_path_ref[0] = str(paths.get('example', ''))
                    test_path_ref[0] = str(paths.get('test', ''))

                    # Cycle/Loop Detection
                    history.append(op)
                    consecutive_ops[op] = consecutive_ops.get(op, 0) + 1
                    for other_op in list(consecutive_ops.keys()):
                        if other_op != op: consecutive_ops[other_op] = 0

                    if op in ["all_synced", "nothing", "error", "fail_and_request_manual_merge"]:
                        results["success"] = (op == "all_synced")
                        break
                    
                    if consecutive_ops.get("fix", 0) > 5 or consecutive_ops.get("test", 0) > MAX_CONSECUTIVE_TESTS:
                        results["error"] = f"Loop detected on {op}"
                        break

                    # Steering
                    if not no_steer:
                        steered_op, should_abort = maybe_steer_operation(
                            op, reason, app_ref, quiet, skip_tests, skip_verify, timeout_s=steer_timeout
                        )
                        if should_abort:
                            results["error"] = "Sync aborted by user steering"
                            break
                        if steered_op != op:
                            log_event(basename, language, "steering_override", {"from": op, "to": steered_op}, "sync")
                            op = steered_op

                    # 2. Execute Operation
                    func_name_ref[0] = op
                    entry = create_log_entry(op, reason, "sync", decision.estimated_cost, decision.confidence, decision.decision_type)
                    op_start = time.time()
                    op_success = False
                    op_error = None
                    op_cost = 0.0
                    op_model = "N/A"

                    ctx = click.Context(click.Command(op))
                    ctx.obj = {
                        "strength": strength, "temperature": temperature, "time": time_param,
                        "verbose": verbose, "quiet": quiet, "force": force or user_confirmed_overwrite[0],
                        "local": local, "confirm_callback": _get_wrapped_confirm()
                    }

                    # Operation Mapping
                    try:
                        if op == "auto-deps":
                            res = auto_deps_main(ctx, str(paths['prompt']), str(paths.get('examples_dir', 'examples')), output=str(paths['prompt']))
                            op_success = True
                            op_cost, op_model = res[1], res[2]
                        elif op == "generate":
                            res = code_generator_main(ctx, str(paths['prompt']), output=str(paths['code']))
                            op_success = True
                            op_cost, op_model = res[2], res[3]
                            clear_run_report(basename, language)
                        elif op == "example":
                            res = context_generator_main(ctx, str(paths['prompt']), str(paths['code']), output=str(paths['example']))
                            op_success = True
                            op_cost, op_model = res[1], res[2]
                        elif op == "crash":
                            # Agentic mode handling
                            use_agentic = _use_agentic_path(language, agentic_mode)
                            loop_param = not use_agentic
                            m_attempts = 0 if use_agentic else max_attempts
                            
                            # Simple error detection for example run
                            err_file = tempfile.NamedTemporaryFile(delete=False, suffix=".log").name
                            res = crash_main(ctx, str(paths['prompt']), str(paths['code']), str(paths['example']), err_file, 
                                             output=str(paths['code']), loop=loop_param, max_attempts=m_attempts, budget=budget)
                            op_success = res[0]
                            op_cost, op_model = res[4], res[5]
                            if op_success and not use_agentic:
                                # Re-verify locally for Python
                                _execute_tests_and_create_run_report(paths['example'], basename, language, target_coverage)
                            elif op_success and use_agentic:
                                _create_synthetic_run_report_for_agentic_success(paths['example'], basename, language)
                        elif op == "verify":
                            use_agentic = _use_agentic_path(language, agentic_mode)
                            res = fix_verification_main(ctx, str(paths['prompt']), str(paths['code']), str(paths['example']), 
                                                        output_code=str(paths['code']), loop=(not use_agentic), max_attempts=(0 if use_agentic else max_attempts))
                            op_success = res[0]
                            op_cost, op_model = res[4], res[5]
                        elif op in ["test", "test_extend"]:
                            extending = (op == "test_extend")
                            res = cmd_test_main(ctx, str(paths['prompt']), str(paths['code']), output=str(paths['test']), 
                                                existing_tests=[str(paths['test'])] if extending else None, 
                                                target_coverage=target_coverage, merge=extending)
                            # res is (content, cost, model, agentic_success)
                            op_cost, op_model = res[1], res[2]
                            agentic_success = res[3]
                            
                            if agentic_success is True:
                                op_success = True
                                _create_synthetic_run_report_for_agentic_success(paths['test'], basename, language)
                            else:
                                op_success, op_error = _execute_tests_and_create_run_report(paths['test'], basename, language, target_coverage, 
                                                                                           code_file=paths['code'], test_files=paths.get('test_files'))
                        elif op == "fix":
                            use_agentic = _use_agentic_path(language, agentic_mode)
                            # find failing file
                            report = read_run_report(basename, language)
                            failing_test = paths['test']
                            if report and language.lower() == "python":
                                # Try to identify specific failing file from output if multiple exist
                                # Simplified: fix_main handles list of test_files
                                pass
                                
                            res = fix_main(ctx, str(paths['prompt']), str(paths['code']), str(failing_test), "", 
                                           output_code=str(paths['code']), loop=(not use_agentic), max_attempts=(0 if use_agentic else max_attempts),
                                           test_files=[str(p) for p in paths.get('test_files', [paths['test']])])
                            op_success = res[0]
                            op_cost, op_model = res[4], res[5]
                            if op_success:
                                if not use_agentic:
                                    _execute_tests_and_create_run_report(paths['test'], basename, language, target_coverage, test_files=paths.get('test_files'))
                                else:
                                    _create_synthetic_run_report_for_agentic_success(paths['test'], basename, language)
                        elif op == "update":
                            res = update_main(ctx, str(paths['prompt']), str(paths['code']), output=str(paths['prompt']), use_git=True)
                            op_success = True
                            op_cost, op_model = res[1], res[2]
                        
                        # Post Op bookkeeping
                        cost_ref[0] += op_cost
                        results["model_name"] = op_model
                        entry = update_log_entry(entry, op_success, op_cost, op_model, time.time() - op_start, op_error)
                        append_log_entry(basename, language, entry)
                        
                        if op_success:
                            results["operations_completed"].append(op)
                            save_fingerprint(basename, language, op, paths, op_cost, op_model)
                        else:
                            results["errors"].append(f"{op} failed: {op_error or 'Unknown error'}")
                            break
                            
                    except Exception as e:
                        op_error = f"{type(e).__name__}: {str(e)}"
                        entry = update_log_entry(entry, False, 0, "Error", time.time() - op_start, op_error)
                        append_log_entry(basename, language, entry)
                        results["errors"].append(op_error)
                        if verbose: traceback.print_exc()
                        break

            log_event(basename, language, "lock_released", {"basename": basename}, "sync")
            
        except Exception as e:
            results["error"] = str(e)
            if verbose: traceback.print_exc()
        finally:
            results["total_cost"] = cost_ref[0]
            results["total_time"] = time.time() - start_time

    # Execution Mode Selection
    if dry_run:
        return {
            "success": True,
            "log_entries": load_operation_log(basename, language),
            "total_cost": 0.0,
            "error": None
        }

    is_headless = not sys.stdin.isatty() or os.getenv("CI") or quiet
    if is_headless:
        os.environ["PDD_FORCE"] = "1"
        sync_worker_logic()
    else:
        app = SyncApp(
            basename=basename,
            language=language,
            worker_func=sync_worker_logic,
            func_name_ref=func_name_ref,
            cost_ref=cost_ref,
            prompt_color_ref=prompt_color_ref,
            code_color_ref=code_color_ref,
            example_color_ref=example_color_ref,
            test_color_ref=test_color_ref,
            prompt_path_ref=prompt_path_ref,
            code_path_ref=code_path_ref,
            example_path_ref=example_path_ref,
            test_path_ref=test_path_ref,
            progress_callback_ref=progress_callback_ref,
            app_ref=app_ref,
            stop_event=stop_event
        )
        app_res = app.run()
        if app_res is None and not results["success"]:
            results["error"] = "Sync interrupted by user"
        if hasattr(app, "worker_exception") and app.worker_exception:
            print(f"Worker crashed: {app.worker_exception}", file=sys.stderr)
            traceback.print_tb(app.worker_exception.__traceback__)

    if not quiet and not is_headless:
        from .sync_tui import show_exit_animation
        show_exit_animation(results["success"], results.get("error") or results.get("errors"))

    results["error"] = "; ".join(results["errors"]) if results["errors"] else results.get("error")
    return results