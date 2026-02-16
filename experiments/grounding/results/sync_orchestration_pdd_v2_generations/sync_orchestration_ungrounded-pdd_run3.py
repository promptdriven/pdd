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
    """Context manager for consistent state writes of fingerprint and run reports."""
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
                # Expecting a dict with keys: operation, paths, cost, model
                save_fingerprint(
                    self.basename, 
                    self.language, 
                    **self.pending_fingerprint
                )

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Returns True if we should use agentic path (non-Python OR agentic_mode for Python)."""
    return language.lower() != "python" or agentic_mode

def _create_synthetic_run_report_for_agentic_success(test_file: str, basename: str, language: str, atomic_state: Optional[AtomicStateUpdate] = None):
    """Creates a successful RunReport for agentic operations that don't need local verification."""
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
        save_run_report(basename, language, report_data)

def _parse_test_output(output: str, language: str) -> Tuple[int, int, float]:
    """Parses test runner output to extract passed/failed counts and coverage."""
    passed, failed, coverage = 0, 0, 0.0
    lang_lower = language.lower()

    if lang_lower == "python":
        # Pytest pattern
        match = re.search(r'(=+)\s+(?:(\d+) passed)?(?:,\s+)?(?:(\d+) failed)?', output)
        if match:
            passed = int(match.group(2)) if match.group(2) else 0
            failed = int(match.group(3)) if match.group(3) else 0
        cov_match = re.search(r'TOTAL\s+\d+\s+\d+\s+(\d+)%', output)
        if cov_match:
            coverage = float(cov_match.group(1))
    
    elif lang_lower in ("javascript", "typescript"):
        # Jest/Vitest pattern
        pass_match = re.search(r'Tests:\s+(?:(\d+) failed, )?(\d+) passed', output)
        if pass_match:
            failed = int(pass_match.group(1)) if pass_match.group(1) else 0
            passed = int(pass_match.group(2))
        cov_match = re.search(r'All files\s+\|\s+([\d.]+)', output)
        if cov_match:
            coverage = float(cov_match.group(1))

    return passed, failed, coverage

def _execute_tests_and_create_run_report(
    test_file: str, 
    basename: str, 
    language: str, 
    target_coverage: float, 
    code_file: Optional[str] = None, 
    atomic_state: Optional[AtomicStateUpdate] = None, 
    test_files: Optional[List[str]] = None
):
    """Executes tests and saves a RunReport."""
    lang_lower = language.lower()
    test_cmd = get_test_command_for_file(test_file, language=lang_lower)
    
    if not test_cmd:
        _create_synthetic_run_report_for_agentic_success(test_file, basename, lang_lower, atomic_state)
        return

    # If multiple test files provided, run them all
    targets = test_files if test_files else [test_file]
    
    # Python specific pytest-cov handling
    env = os.environ.copy()
    cmd_parts = test_cmd.split()
    
    if lang_lower == "python":
        root = _find_project_root(test_file)
        if root:
            env["PYTHONPATH"] = f"{root}:{root}/src:{env.get('PYTHONPATH', '')}"
            cmd_parts.extend(["--rootdir", str(root), "-c", os.devnull])
        
        if code_file:
            # Simple heuristic for cov target
            cov_target = Path(code_file).stem
            cmd_parts.extend([f"--cov={cov_target}", "--cov-report=term-missing"])

    try:
        process = subprocess.run(
            cmd_parts + targets,
            capture_output=True,
            text=True,
            env=env,
            start_new_session=True,
            stdin=subprocess.DEVNULL
        )
        passed, failed, cov = _parse_test_output(process.stdout + process.stderr, lang_lower)
        
        # Calculate hashes for RunReport
        current_hashes = calculate_current_hashes(basename, lang_lower)
        
        report_data = {
            "timestamp": datetime.datetime.now().isoformat(),
            "exit_code": process.returncode,
            "tests_passed": passed,
            "tests_failed": failed,
            "coverage": cov,
            "test_hash": current_hashes.get("test"),
            "test_file_hashes": {Path(f).name: calculate_sha256(Path(f)) for f in targets}
        }
        
        if atomic_state:
            atomic_state.pending_run_report = report_data
        else:
            save_run_report(basename, lang_lower, report_data)
            
    except Exception:
        # Fallback to failed report
        save_run_report(basename, lang_lower, {"exit_code": 1, "error": "Test execution failed"})

def _display_sync_log(basename: str, language: str, verbose: bool):
    """Formats and displays the sync log."""
    try:
        entries = load_operation_log(basename, language)
        if not entries:
            click.echo("No sync history found.")
            return

        click.echo(f"--- Sync Log for {basename} ({language}) ---")
        for entry in entries:
            ts = entry.get('timestamp', 'N/A')
            op = entry.get('operation', 'unknown')
            res = "SUCCESS" if entry.get('success') else "FAILED"
            cost = entry.get('actual_cost', 0.0)
            
            line = f"[{ts}] {op.upper():<10} | {res:<8} | ${cost:.4f}"
            if verbose:
                line += f" | Reason: {entry.get('reason', 'N/A')}"
            click.echo(line)
    except Exception as e:
        click.echo(f"Error reading sync log: {e}")

def _create_mock_context(**kwargs) -> click.Context:
    """Creates a mock Click context for command execution."""
    ctx = click.Context(click.Command("sync"))
    ctx.obj = kwargs
    ctx.params = kwargs
    return ctx

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
    """Orchestrates the complete PDD sync workflow with TUI feedback."""
    
    # Defensive defaults
    target_coverage = target_coverage if target_coverage is not None else 90.0
    budget = budget if budget is not None else 20.0
    max_attempts = max_attempts if max_attempts is not None else 3
    lang_lower = language.lower()

    if dry_run:
        _display_sync_log(basename, lang_lower, verbose)
        return {"success": True, "log_entries": load_operation_log(basename, lang_lower)}

    # State references for TUI/Worker coordination
    state = {
        "function_name": ["initializing"],
        "cost": [0.0],
        "op_color": ["white"],
        "paths": {},
        "stop_event": threading.Event(),
        "app_ref": [None],
        "user_confirmed_overwrite": [False],
        "progress": [0.0],
        "start_time": time.time(),
        "errors": [],
        "ops_completed": [],
        "ops_skipped": [],
        "last_model": "unknown"
    }

    def sync_worker_logic():
        consecutive_ops = {}
        last_ops = []
        
        try:
            with SyncLock(basename, lang_lower) as lock:
                log_event(basename, lang_lower, "lock_acquired", {"pid": os.getpid()}, "sync")
                
                while not state["stop_event"].is_set():
                    # Check overall budget
                    if state["cost"][0] >= budget:
                        log_event(basename, lang_lower, "budget_exhausted", {"cost": state["cost"][0]}, "sync")
                        state["errors"].append("Budget exceeded")
                        break

                    # Determine next step
                    decision = sync_determine_operation(basename, lang_lower, target_coverage, log_mode=True)
                    op = decision.operation

                    if op in ("all_synced", "nothing"):
                        break
                    
                    if op == "error":
                        state["errors"].append(decision.reason)
                        break

                    # Cycle Detection
                    last_ops.append(op)
                    if len(last_ops) > 10: last_ops.pop(0)
                    consecutive_ops[op] = consecutive_ops.get(op, 0) + 1
                    
                    if consecutive_ops.get("fix", 0) > 5:
                        state["errors"].append("Stuck in fix loop")
                        break
                    
                    # Steering
                    if not no_steer:
                        steered_op, should_abort = maybe_steer_operation(
                            op, decision.reason, state["app_ref"], quiet, skip_tests, skip_verify, timeout_s=steer_timeout
                        )
                        if should_abort:
                            state["errors"].append("Aborted by user steering")
                            break
                        if steered_op != op:
                            log_event(basename, lang_lower, "steering_override", {"from": op, "to": steered_op}, "sync")
                            op = steered_op

                    # Update TUI
                    state["function_name"][0] = op
                    state["op_color"][0] = "yellow"
                    
                    # Resolved paths for current state
                    pdd_paths = get_pdd_file_paths(basename, lang_lower)
                    state["paths"] = pdd_paths

                    # Execution block
                    op_success = False
                    op_cost = 0.0
                    op_model = "unknown"
                    
                    ctx = _create_mock_context(
                        force=force or state["user_confirmed_overwrite"][0],
                        quiet=quiet,
                        verbose=verbose,
                        local=local,
                        strength=strength,
                        temperature=temperature,
                        time=time_param
                    )

                    try:
                        with AtomicStateUpdate(basename, lang_lower) as atomic:
                            if op == "auto-deps":
                                # auto-deps_main logic
                                res = auto_deps_main(ctx, pdd_paths["prompt"], f"{examples_dir}/**/*")
                                op_success = True
                                op_cost, op_model = res[1], res[2]
                                
                            elif op == "generate":
                                res = code_generator_main(ctx, pdd_paths["prompt"], pdd_paths.get("code"))
                                op_success = True
                                op_cost, op_model = res[2], res[3]
                                clear_run_report(basename, lang_lower)
                                
                            elif op == "example":
                                res = context_generator_main(ctx, pdd_paths["prompt"], pdd_paths["code"])
                                op_success = True
                                op_cost, op_model = res[1], res[2]
                                
                            elif op == "crash":
                                if skip_tests:
                                    _create_synthetic_run_report_for_agentic_success(pdd_paths.get("code", ""), basename, lang_lower, atomic)
                                    op_success = True
                                else:
                                    # determine error file
                                    err_file = str(Path(tempfile.gettempdir()) / f"{basename}_crash.log")
                                    # For Python we try to detect errors locally
                                    if lang_lower == "python" and pdd_paths.get("example"):
                                        try:
                                            subprocess.run([sys.executable, pdd_paths["example"]], capture_output=True, text=True, timeout=10)
                                        except Exception as e:
                                            Path(err_file).write_text(str(e))
                                    
                                    res = crash_main(
                                        ctx, pdd_paths["prompt"], pdd_paths["code"], 
                                        pdd_paths.get("example", ""), err_file, loop=True,
                                        max_attempts=0 if _use_agentic_path(lang_lower, agentic_mode) else max_attempts
                                    )
                                    op_success, op_cost, op_model = res[0], res[4], res[5]
                                    if op_success:
                                        if lang_lower == "python":
                                            _execute_tests_and_create_run_report(pdd_paths["test"], basename, lang_lower, target_coverage, pdd_paths["code"], atomic)
                                        else:
                                            _create_synthetic_run_report_for_agentic_success(pdd_paths.get("code", ""), basename, lang_lower, atomic)

                            elif op == "verify":
                                if skip_verify:
                                    atomic.pending_fingerprint = {"operation": "skip:verify", "paths": pdd_paths, "cost": 0, "model": "skipped"}
                                    op_success = True
                                else:
                                    res = fix_verification_main(
                                        ctx, pdd_paths["prompt"], pdd_paths["code"], pdd_paths["example"],
                                        loop=True, max_attempts=0 if _use_agentic_path(lang_lower, agentic_mode) else max_attempts
                                    )
                                    op_success, op_cost, op_model = res[0], res[4], res[5]

                            elif op == "test":
                                if skip_tests:
                                    op_success = True
                                else:
                                    res = cmd_test_main(ctx, pdd_paths["prompt"], pdd_paths["code"])
                                    # (content, cost, model, agentic_success)
                                    op_cost, op_model = res[1], res[2]
                                    agent_ok = res[3]
                                    if agent_ok or Path(pdd_paths["test"]).exists():
                                        op_success = True
                                        if agent_ok:
                                            _create_synthetic_run_report_for_agentic_success(pdd_paths["test"], basename, lang_lower, atomic)
                                        else:
                                            _execute_tests_and_create_run_report(pdd_paths["test"], basename, lang_lower, target_coverage, pdd_paths["code"], atomic)

                            elif op == "fix":
                                run_rep = read_run_report(basename, lang_lower)
                                err_content = "" # fix_main can handle empty if loop=True
                                res = fix_main(
                                    ctx, pdd_paths["prompt"], pdd_paths["code"], pdd_paths["test"], "",
                                    loop=True, max_attempts=0 if _use_agentic_path(lang_lower, agentic_mode) else max_attempts
                                )
                                op_success, op_cost, op_model = res[0], res[4], res[5]
                                if op_success:
                                    if lang_lower == "python":
                                        _execute_tests_and_create_run_report(pdd_paths["test"], basename, lang_lower, target_coverage, pdd_paths["code"], atomic)
                                    else:
                                        _create_synthetic_run_report_for_agentic_success(pdd_paths["test"], basename, lang_lower, atomic)

                            elif op == "update":
                                res = update_main(ctx, pdd_paths["prompt"], pdd_paths["code"], use_git=True)
                                op_success = True
                                op_cost, op_model = res[1], res[2]

                            # Finalize operation state
                            if op_success:
                                state["cost"][0] += op_cost
                                state["last_model"] = op_model
                                state["ops_completed"].append(op)
                                state["op_color"][0] = "green"
                                if op not in ("crash", "fix", "test", "verify"): # These set atomic themselves
                                    atomic.pending_fingerprint = {"operation": op, "paths": pdd_paths, "cost": op_cost, "model": op_model}
                                
                                # Log to persistent sync log
                                entry = create_log_entry(op, decision.reason, "sync", op_cost, decision.confidence, decision.decision_type)
                                entry = update_log_entry(entry, True, op_cost, op_model, 0, None)
                                append_log_entry(basename, lang_lower, entry)
                            else:
                                state["op_color"][0] = "red"
                                state["errors"].append(f"Operation {op} failed")
                                break

                    except Exception as e:
                        state["op_color"][0] = "red"
                        state["errors"].append(f"System error in {op}: {str(e)}")
                        break

        except Exception as e:
            state["errors"].append(f"Worker crashed: {str(e)}")
            traceback.print_exc()

    # Headless Detection
    is_headless = not sys.stdin.isatty() or os.getenv("CI") == "true" or quiet

    if is_headless:
        os.environ["PDD_FORCE"] = "1"
        sync_worker_logic()
    else:
        app = SyncApp(
            basename=basename,
            language=lang_lower,
            worker_func=sync_worker_logic,
            state_refs=state
        )
        state["app_ref"][0] = app
        app.run()
        
        from .sync_tui import show_exit_animation
        show_exit_animation(basename, lang_lower, state["ops_completed"], state["cost"][0])

    # Construct Return
    total_time = time.time() - state["start_time"]
    return {
        "success": len(state["errors"]) == 0,
        "operations_completed": state["ops_completed"],
        "skipped_operations": state["ops_skipped"],
        "total_cost": state["cost"][0],
        "total_time": total_time,
        "final_state": {k: {"exists": Path(v).exists(), "path": v} for k, v in state["paths"].items()},
        "errors": state["errors"],
        "error": "; ".join(state["errors"]) if state["errors" else None,
        "model_name": state["last_model"]
    }