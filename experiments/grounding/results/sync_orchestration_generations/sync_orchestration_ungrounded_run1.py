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
    """Context manager for consistent state writes of fingerprint and run report."""
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
    """Returns True if we should use agentic path (non-Python or agentic_mode for Python)."""
    return language.lower() != "python" or agentic_mode

def _create_mock_context(**kwargs) -> click.Context:
    """Create a mock Click context for internal command execution."""
    ctx = click.Context(click.Command("sync_internal"))
    ctx.obj = kwargs
    ctx.params = kwargs
    return ctx

def _display_sync_log(basename: str, language: str, verbose: bool):
    """Format and display the sync log to the console."""
    entries = load_operation_log(basename, language)
    if not entries:
        click.echo("No sync history found.")
        return

    click.echo(f"\n--- Sync Analysis for {basename} ({language}) ---")
    for entry in entries:
        timestamp = entry.get("timestamp", "N/A")
        op = entry.get("operation", "unknown")
        reason = entry.get("reason", "N/A")
        if verbose:
            click.echo(f"[{timestamp}] {op.upper()}: {reason}")
            if "actual_cost" in entry:
                click.echo(f"  Cost: ${entry['actual_cost']:.4f} | Model: {entry.get('model')}")
        else:
            click.echo(f"• {op}: {reason}")

def _python_cov_target_for_code_file(code_file: str) -> str:
    """Determine the dotted module path for pytest-cov from a file path."""
    p = Path(code_file)
    # Simple heuristic: if in src/, strip it
    parts = list(p.parts)
    if "src" in parts:
        parts = parts[parts.index("src")+1:]
    
    module_path = ".".join(parts).replace(p.suffix, "")
    return module_path

def _parse_test_output(output: str, language: str) -> Tuple[int, int, float]:
    """Parse test runner output to extract passing/failing counts and coverage."""
    passed = 0
    failed = 0
    coverage = 0.0

    if language.lower() == "python":
        # Pytest pattern
        pass_match = re.search(r'(\d+) passed', output)
        fail_match = re.search(r'(\d+) failed', output)
        cov_match = re.search(r'TOTAL\s+.*?\s+(\d+)%', output)
        if pass_match: passed = int(pass_match.group(1))
        if fail_match: failed = int(fail_match.group(1))
        if cov_match: coverage = float(cov_match.group(1))
    else:
        # Generic patterns for JS/TS (Jest/Vitest), Go, Cargo
        pass_match = re.search(r'Tests?:\s+.*?(\d+)\s+passed', output, re.I)
        fail_match = re.search(r'Tests?:\s+.*?(\d+)\s+failed', output, re.I)
        if not pass_match: # Go/Cargo fallback
            pass_match = re.search(r'(\d+)\s+passed', output)
            fail_match = re.search(r'(\d+)\s+failed', output)
            
        if pass_match: passed = int(pass_match.group(1))
        if fail_match: failed = int(fail_match.group(1))

    return passed, failed, coverage

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
    """Execute tests with coverage tracking and update the run report."""
    test_paths = test_files if test_files else [test_file]
    language = language.lower()
    
    if language == "python":
        python_exe = detect_host_python_executable()
        project_root = _find_project_root(test_file)
        env = os.environ.copy()
        
        # Clean env for subprocess
        env.pop("FORCE_COLOR", None)
        env.pop("COLUMNS", None)
        
        if project_root:
            src_path = str(Path(project_root) / "src")
            env["PYTHONPATH"] = f"{project_root}{os.pathsep}{src_path}{os.pathsep}{env.get('PYTHONPATH', '')}"

        cmd = [python_exe, "-m", "pytest"]
        if code_file:
            cov_target = _python_cov_target_for_code_file(code_file)
            cmd += [f"--cov={cov_target}", "--cov-report=term-missing"]
        
        if project_root:
            cmd += ["--rootdir", str(project_root), "-c", "/dev/null"]
            
        cmd += test_paths
        
        try:
            result = subprocess.run(
                cmd, 
                capture_output=True, 
                text=True, 
                env=env, 
                start_new_session=True,
                stdin=subprocess.DEVNULL
            )
            output = result.stdout + result.stderr
            passed, failed, coverage = _parse_test_output(output, language)
            
            # Map hashes of all test files
            hashes = {str(p): calculate_sha256(p) for p in test_paths}
            
            report = RunReport(
                timestamp=datetime.datetime.now().isoformat(),
                exit_code=result.returncode,
                tests_passed=passed,
                tests_failed=failed,
                coverage=coverage,
                test_hash=hashes.get(test_file),
                test_file_hashes=hashes
            )
            
            if atomic_state:
                atomic_state.set_run_report(asdict(report))
            else:
                save_run_report(basename, language, asdict(report))
            
            return {"success": result.returncode == 0, "output": output, "report": report}
        except Exception as e:
            return {"success": False, "output": str(e), "error": str(e)}
    else:
        # Non-Python logic: use get_test_command_for_file
        from .get_test_command import get_test_command_for_file
        cmd_str = get_test_command_for_file(test_file, language=language)
        if not cmd_str:
            return {"success": False, "error": f"No test runner found for {language}"}
            
        try:
            result = subprocess.run(
                cmd_str, 
                shell=True, 
                capture_output=True, 
                text=True,
                start_new_session=True,
                stdin=subprocess.DEVNULL
            )
            output = result.stdout + result.stderr
            passed, failed, _ = _parse_test_output(output, language)
            
            report = RunReport(
                timestamp=datetime.datetime.now().isoformat(),
                exit_code=result.returncode,
                tests_passed=passed,
                tests_failed=failed,
                coverage=0.0,
                test_hash=calculate_sha256(test_file)
            )
            
            if atomic_state:
                atomic_state.set_run_report(asdict(report))
            else:
                save_run_report(basename, language, asdict(report))
            return {"success": result.returncode == 0, "output": output, "report": report}
        except Exception as e:
            return {"success": False, "error": str(e)}

def _create_synthetic_run_report_for_agentic_success(test_file, basename, language, *, atomic_state=None):
    """Creates a successful RunReport when an agent claims success without local execution."""
    test_hash = calculate_sha256(test_file) if os.path.exists(test_file) else "agentic_test_success"
    report = RunReport(
        timestamp=datetime.datetime.now().isoformat(),
        exit_code=0,
        tests_passed=1,
        tests_failed=0,
        coverage=100.0,
        test_hash=test_hash
    )
    if atomic_state:
        atomic_state.set_run_report(asdict(report))
    else:
        save_run_report(basename, language, asdict(report))

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
    
    # Defaults handling
    target_coverage = target_coverage if target_coverage is not None else 90.0
    budget = budget if budget is not None else 20.0
    max_attempts = max_attempts if max_attempts is not None else 3
    
    from .sync_main import get_extension # Delayed import
    
    if dry_run:
        _display_sync_log(basename, language, verbose)
        return {"success": True, "log_entries": load_operation_log(basename, language)}

    # State for orchestration
    ops_completed = []
    ops_skipped = []
    total_cost = 0.0
    start_time = time.time()
    errors = []
    last_model = "unknown"

    # Shared refs for TUI coordination
    func_name_ref = ["Initializing..."]
    cost_ref = [0.0]
    prompt_path_ref = [None]
    code_path_ref = [None]
    example_path_ref = [None]
    test_path_ref = [None]
    prompt_color_ref = ["blue"]
    code_color_ref = ["blue"]
    example_color_ref = ["blue"]
    test_color_ref = ["blue"]
    progress_callback_ref = [None]
    app_ref = [None]
    user_confirmed_overwrite = [force] # If force, confirmed is True

    def get_confirm_callback():
        def wrapper(title: str, message: str) -> bool:
            if user_confirmed_overwrite[0]:
                return True
            if app_ref[0]:
                res = app_ref[0].request_confirmation(title, message)
                if res:
                    user_confirmed_overwrite[0] = True
                return res
            # Headless fallback
            if click.confirm(f"{title}: {message}", default=True):
                user_confirmed_overwrite[0] = True
                return True
            return False
        return wrapper

    effective_confirm_callback = confirm_callback or get_confirm_callback()

    def sync_worker_logic(stop_event: threading.Event):
        nonlocal total_cost, last_model
        
        # Tracking for cycle detection
        op_history = []
        consecutive_tests = 0
        consecutive_crashes = 0
        test_extend_attempts = 0
        
        with SyncLock(basename, language) as lock:
            if not lock.acquired:
                errors.append(f"Could not acquire lock for {basename}_{language}")
                return

            log_event(basename, language, "lock_acquired", {"pid": os.getpid()}, "sync")

            while not stop_event.is_set():
                # 1. Determine next operation
                decision = sync_determine_operation(basename, language, target_coverage)
                
                # Check for infinite loops
                op_history.append(decision.operation)
                if len(op_history) >= 3:
                    last_3 = op_history[-3:]
                    if last_3.count("auto-deps") >= 2 and decision.operation == "auto-deps":
                        decision.operation = "generate"
                        decision.reason = "Cycle detected: forcing generate"
                
                # Cycle patterns: crash-verify or test-fix
                if len(op_history) >= 4:
                    pattern = op_history[-4:]
                    if pattern in (["crash", "verify", "crash", "verify"], ["test", "fix", "test", "fix"]):
                        decision.operation = "nothing"
                        decision.reason = "Workflow cycle detected. Stopping for manual review."

                # 2. Steering
                steered_op, should_abort = decision.operation, False
                if not no_steer:
                    steered_op, should_abort = maybe_steer_operation(
                        decision.operation, decision.reason, app_ref, quiet, skip_tests, skip_verify, timeout_s=steer_timeout
                    )
                
                if should_abort:
                    log_event(basename, language, "steering_abort", {"reason": "User aborted"}, "sync")
                    break
                
                if steered_op != decision.operation:
                    log_event(basename, language, "steering_override", {"from": decision.operation, "to": steered_op}, "sync")
                    decision.operation = steered_op

                if decision.operation in ("nothing", "all_synced", "fail_and_request_manual_merge", "error"):
                    break

                # 3. Handle Skips
                effective_op = decision.operation
                if (skip_tests and effective_op in ("test", "test_extend", "fix", "verify", "crash")) or \
                   (skip_verify and effective_op == "verify"):
                    ops_skipped.append(effective_op)
                    save_fingerprint(basename, language, f"skip:{effective_op}", get_pdd_file_paths(basename, language), 0, "n/a")
                    # If skipping crash, need synthetic report to stop loop
                    if effective_op == "crash":
                        save_run_report(basename, language, asdict(RunReport(datetime.datetime.now().isoformat(), 0, 0, 0, 0.0)))
                    continue

                # 4. Prepare Paths
                pdd_files = get_pdd_file_paths(basename, language)
                prompt_path_ref[0] = pdd_files.get("prompt")
                code_path_ref[0] = pdd_files.get("code")
                example_path_ref[0] = pdd_files.get("example")
                test_path_ref[0] = pdd_files.get("test")
                
                # Update TUI strings
                func_name_ref[0] = f"Executing {effective_op}..."

                # 5. Execute Operation
                ctx = _create_mock_context(
                    strength=strength, 
                    temperature=temperature, 
                    time=time_param, 
                    verbose=verbose, 
                    quiet=quiet, 
                    force=user_confirmed_overwrite[0],
                    local=local,
                    confirm_callback=effective_confirm_callback
                )
                
                entry = create_log_entry(
                    operation=effective_op,
                    reason=decision.reason,
                    invocation_mode="sync",
                    estimated_cost=decision.estimated_cost,
                    confidence=decision.confidence,
                    decision_type=decision.decision_type
                )

                op_start = time.time()
                success, op_cost, model = False, 0.0, "unknown"
                
                try:
                    with AtomicStateUpdate(basename, language) as state:
                        if effective_op == "auto-deps":
                            # Auto-deps logic
                            from .auto_deps_main import auto_deps_main
                            res_prompt, op_cost, model = auto_deps_main(
                                ctx, str(pdd_files['prompt']), f"{examples_dir}/**/*", output=str(pdd_files['prompt'])
                            )
                            success = True
                            state.set_fingerprint(effective_op, get_pdd_file_paths(basename, language), op_cost, model)

                        elif effective_op == "generate":
                            from .code_generator_main import code_generator_main
                            res_code, inc, op_cost, model = code_generator_main(
                                ctx, str(pdd_files['prompt']), output=str(pdd_files['code'])
                            )
                            success = True
                            clear_run_report(basename, language)
                            state.set_fingerprint(effective_op, get_pdd_file_paths(basename, language), op_cost, model)

                        elif effective_op == "example":
                            from .context_generator_main import context_generator_main
                            res_ex, op_cost, model = context_generator_main(
                                ctx, str(pdd_files['prompt']), str(pdd_files['code']), output=str(pdd_files['example'])
                            )
                            success = True
                            state.set_fingerprint(effective_op, get_pdd_file_paths(basename, language), op_cost, model)

                        elif effective_op == "crash":
                            consecutive_crashes += 1
                            if consecutive_crashes > MAX_CONSECUTIVE_CRASHES:
                                raise RuntimeError("Maximum consecutive crash fix attempts reached.")
                            
                            is_agentic = _use_agentic_path(language, agentic_mode)
                            actual_max = 0 if is_agentic else max_attempts
                            
                            # Detect crash locally for non-python if needed, but usually we just let it run
                            res = crash_main(
                                ctx, str(pdd_files['prompt']), str(pdd_files['code']), 
                                str(pdd_files['example']), "crash.log",
                                output=str(pdd_files['code']), loop=True, max_attempts=actual_max, budget=budget
                            )
                            success, op_cost, model = res[0], res[4], res[5]
                            if success:
                                if language.lower() == "python":
                                    # Verify python
                                    pass
                                else:
                                    # Synthetic success for non-python
                                    state.set_run_report(asdict(RunReport(datetime.datetime.now().isoformat(), 0, 1, 0, 0.0)))
                                state.set_fingerprint(effective_op, get_pdd_file_paths(basename, language), op_cost, model)

                        elif effective_op == "verify":
                            is_agentic = _use_agentic_path(language, agentic_mode)
                            actual_max = 0 if is_agentic else max_attempts
                            res = fix_verification_main(
                                ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(pdd_files['example']),
                                output_code=str(pdd_files['code']), loop=True, max_attempts=actual_max, budget=budget
                            )
                            success, op_cost, model = res[0], res[4], res[5]
                            if success:
                                state.set_fingerprint(effective_op, get_pdd_file_paths(basename, language), op_cost, model)

                        elif effective_op in ("test", "test_extend"):
                            if effective_op == "test":
                                consecutive_tests += 1
                                if consecutive_tests > MAX_CONSECUTIVE_TESTS:
                                    raise RuntimeError("Maximum consecutive test generation attempts reached.")
                            
                            is_extend = (effective_op == "test_extend")
                            # test_extend only supported for Python in local mode
                            if is_extend and language.lower() != "python":
                                success, op_cost, model = True, 0.0, "n/a"
                            else:
                                res = cmd_test_main(
                                    ctx, str(pdd_files['prompt']), str(pdd_files['code']),
                                    output=str(pdd_files['test']), language=language,
                                    existing_tests=[str(pdd_files['test'])] if is_extend else None,
                                    target_coverage=target_coverage if is_extend else None,
                                    merge=is_extend
                                )
                                # Tuple is (code, cost, model, agentic_success)
                                op_cost, model, agentic_success = res[1], res[2], res[3]
                                
                                if agentic_success is True:
                                    _create_synthetic_run_report_for_agentic_success(pdd_files['test'], basename, language, atomic_state=state)
                                    success = True
                                else:
                                    # Run locally
                                    test_res = _execute_tests_and_create_run_report(
                                        pdd_files['test'], basename, language, target_coverage, 
                                        code_file=pdd_files['code'], atomic_state=state,
                                        test_files=pdd_files.get('test_files')
                                    )
                                    success = test_res['success']
                                state.set_fingerprint(effective_op, get_pdd_file_paths(basename, language), op_cost, model)

                        elif effective_op == "fix":
                            is_agentic = _use_agentic_path(language, agentic_mode)
                            actual_max = 0 if is_agentic else max_attempts
                            
                            # Identify specific failing file if multiple exist
                            target_test = pdd_files['test']
                            run_rep = read_run_report(basename, language)
                            if run_rep and pdd_files.get('test_files'):
                                # Hypothetically we'd run pytest and extract, but fix_main handles error_file.
                                # For sync orchestration, we re-run to get fresh error log.
                                test_exec = _execute_tests_and_create_run_report(
                                    target_test, basename, language, target_coverage, 
                                    code_file=pdd_files['code'], test_files=pdd_files.get('test_files')
                                )
                                failing_files = extract_failing_files_from_output(test_exec.get('output', ""))
                                if failing_files:
                                    target_test = failing_files[0]

                            res = fix_main(
                                ctx, str(pdd_files['prompt']), str(pdd_files['code']), str(target_test),
                                output_code=str(pdd_files['code']), output_test=str(target_test),
                                loop=True, max_attempts=actual_max, budget=budget,
                                test_files=pdd_files.get('test_files')
                            )
                            success, op_cost, model = res[0], res[4], res[5]
                            if success:
                                if language.lower() == "python":
                                    _execute_tests_and_create_run_report(
                                        pdd_files['test'], basename, language, target_coverage, 
                                        code_file=pdd_files['code'], atomic_state=state,
                                        test_files=pdd_files.get('test_files')
                                    )
                                else:
                                    _create_synthetic_run_report_for_agentic_success(pdd_files['test'], basename, language, atomic_state=state)
                                state.set_fingerprint(effective_op, get_pdd_file_paths(basename, language), op_cost, model)

                        elif effective_op == "update":
                            res_prompt, op_cost, model = update_main(
                                ctx, str(pdd_files['prompt']), str(pdd_files['code']), output=str(pdd_files['prompt']), use_git=True
                            )
                            success = True
                            state.set_fingerprint(effective_op, get_pdd_file_paths(basename, language), op_cost, model)

                except Exception as e:
                    success = False
                    last_model = "error"
                    errors.append(f"Operation {effective_op} failed: {str(e)}")
                    if verbose:
                        traceback.print_exc()

                # Cleanup operation tracking
                total_cost += op_cost
                cost_ref[0] = total_cost
                last_model = model
                
                updated_entry = update_log_entry(
                    entry, success, op_cost, model, time.time() - op_start, 
                    errors[-1] if not success and errors else None
                )
                append_log_entry(basename, language, updated_entry)
                
                if success:
                    ops_completed.append(effective_op)
                    # Reset counters on success if they were specific to those types
                    if effective_op != "test": consecutive_tests = 0
                    if effective_op != "crash": consecutive_crashes = 0
                
                if total_cost >= budget:
                    log_event(basename, language, "budget_exhausted", {"total": total_cost, "limit": budget}, "sync")
                    break
                elif total_cost >= budget * 0.8:
                    log_event(basename, language, "budget_warning", {"remaining": budget - total_cost}, "sync")

            log_event(basename, language, "lock_released", {}, "sync")

    # Run TUI or Headless
    is_headless = not sys.stdin.isatty() or os.getenv("CI") == "true" or quiet
    
    if is_headless:
        os.environ["PDD_FORCE"] = "1"
        stop_event = threading.Event()
        sync_worker_logic(stop_event)
    else:
        app = SyncApp(
            worker_func=sync_worker_logic,
            basename=basename,
            language=language,
            func_name_ref=func_name_ref,
            cost_ref=cost_ref,
            prompt_path_ref=prompt_path_ref,
            code_path_ref=code_path_ref,
            example_path_ref=example_path_ref,
            test_path_ref=test_path_ref,
            prompt_color_ref=prompt_color_ref,
            code_color_ref=code_color_ref,
            example_color_ref=example_color_ref,
            test_color_ref=test_color_ref,
            progress_callback_ref=progress_callback_ref
        )
        app_ref[0] = app
        res = app.run()
        
        if res is None:
            return {"success": False, "error": "Sync interrupted by user"}
            
        if app.worker_exception:
            print(f"Worker crashed: {app.worker_exception}", file=sys.stderr)
            traceback.print_exception(type(app.worker_exception), app.worker_exception, app.worker_exception.__traceback__)
            errors.append(str(app.worker_exception))

        from .sync_tui import show_exit_animation
        show_exit_animation()

    final_paths = get_pdd_file_paths(basename, language)
    final_state = {k: {"exists": os.path.exists(v) if isinstance(v, str) else False, "path": v} for k, v in final_paths.items()}

    return {
        "success": len(errors) == 0,
        "operations_completed": ops_completed,
        "skipped_operations": ops_skipped,
        "total_cost": total_cost,
        "total_time": time.time() - start_time,
        "final_state": final_state,
        "errors": errors,
        "error": "; ".join(errors) if errors else None,
        "model_name": last_model,
    }
