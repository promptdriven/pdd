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
from pathlib import Path
from typing import Dict, Any, Optional, List, Callable
from dataclasses import asdict, dataclass, field
from datetime import timezone

import click

# Internal PDD Imports
from .sync_tui import SyncApp, show_exit_animation
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
from .pytest_output import extract_failing_files_from_output
from . import DEFAULT_STRENGTH, __version__

# Constants
MAX_CONSECUTIVE_TESTS = 3
MAX_TEST_EXTEND_ATTEMPTS = 2
MAX_CONSECUTIVE_CRASHES = 3
MAX_CYCLE_REPEATS = 2

class AtomicStateUpdate:
    """Context manager for consistent state writes (RunReport + Fingerprint)."""
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language
        self.pending_report = None
        self.pending_fingerprint = None

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            if self.pending_report:
                save_run_report(self.pending_report, self.basename, self.language)
            if self.pending_fingerprint:
                self._write_fingerprint(self.pending_fingerprint)

    def _write_fingerprint(self, fp: Fingerprint):
        path = META_DIR / f"{self.basename}_{self.language}.json"
        temp_fd, temp_path = tempfile.mkstemp(dir=META_DIR, text=True)
        try:
            with os.fdopen(temp_fd, 'w') as f:
                json.dump(fp.__dict__, f, indent=4)
            os.replace(temp_path, path)
        except Exception:
            if os.path.exists(temp_path):
                os.remove(temp_path)
            raise

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
) -> Dict[str, Any]:
    """Orchestrates the complete PDD sync workflow with TUI feedback."""
    
    if dry_run:
        log_entries = load_sync_log(basename, language)
        _display_sync_log(basename, language, verbose)
        return {"success": True, "log_entries": log_entries}

    # Shared state for TUI
    stop_event = threading.Event()
    current_func_ref = ["analyzing"]
    cost_ref = [0.0]
    p_color, c_color, e_color, t_color = ["blue"], ["blue"], ["blue"], ["blue"]
    p_path, c_path, e_path, t_path = [""], [""], [""], [""]
    app_ref = []
    
    # Resolve paths early
    try:
        paths = get_pdd_file_paths(basename, language)
        p_path[0] = paths['prompt']
        c_path[0] = paths['code']
        e_path[0] = paths['example']
        t_path[0] = paths['test']
    except Exception as e:
        return {"success": False, "error": str(e), "errors": [str(e)]}

    results = {
        "success": False,
        "operations_completed": [],
        "skipped_operations": [],
        "total_cost": 0.0,
        "total_time": 0.0,
        "errors": [],
        "model_name": None
    }

    def worker_logic():
        start_time = time.time()
        consecutive_ops = []
        
        try:
            with SyncLock(basename, language):
                log_sync_event(basename, language, "lock_acquired", {"pid": os.getpid()})
                
                while not stop_event.is_set():
                    # 1. Determine next operation
                    decision = sync_determine_operation(basename, language, target_coverage)
                    op = decision.operation
                    
                    # Check terminal states
                    if op in ("all_synced", "nothing"):
                        results["success"] = True
                        break
                    if op in ("error", "fail_and_request_manual_merge", "analyze_conflict"):
                        results["errors"].append(f"Terminal state reached: {op}. {decision.reason}")
                        break

                    # Check Budget
                    if cost_ref[0] >= budget:
                        results["errors"].append(f"Budget exceeded: ${cost_ref[0]:.2f} >= ${budget:.2f}")
                        break
                    if cost_ref[0] > budget * 0.8:
                        log_sync_event(basename, language, "budget_warning", {"current": cost_ref[0], "limit": budget})

                    # Cycle Detection
                    consecutive_ops.append(op)
                    if len(consecutive_ops) > 10: consecutive_ops.pop(0)
                    
                    if _detect_infinite_loop(consecutive_ops):
                        results["errors"].append("Infinite loop detected in workflow. Stopping.")
                        break

                    # 2. Execute Operation
                    current_func_ref[0] = op
                    op_start = time.time()
                    
                    # Handle Skips
                    if (skip_verify and op in ("verify", "crash")) or (skip_tests and op in ("test", "test_extend", "fix")):
                        results["skipped_operations"].append(op)
                        _handle_skip(basename, language, op, paths)
                        continue

                    # Execute
                    try:
                        op_result = _execute_op(op, basename, language, paths, {
                            "ctx": _create_mock_context(strength=strength, temperature=temperature, time=time_param, local=local, force=force, verbose=verbose),
                            "target_coverage": target_coverage,
                            "max_attempts": max_attempts if language == "python" else 0,
                            "budget": budget - cost_ref[0],
                            "app": app_ref[0] if app_ref else None
                        })
                        
                        # Update state
                        cost = op_result.get("cost", 0.0)
                        cost_ref[0] += cost
                        results["total_cost"] = cost_ref[0]
                        results["model_name"] = op_result.get("model")
                        results["operations_completed"].append(op)
                        
                        # Update TUI colors based on success
                        _update_box_colors(op, op_result.get("success", False), p_color, c_color, e_color, t_color)
                        
                    except Exception as e:
                        results["errors"].append(f"Operation {op} failed: {str(e)}")
                        log_sync_event(basename, language, "op_error", {"op": op, "error": str(e)})
                        break

                results["total_time"] = time.time() - start_time
                log_sync_event(basename, language, "lock_released", {"duration": results["total_time"]})

        except Exception as e:
            results["errors"].append(f"Sync worker crashed: {str(e)}")
            results["traceback"] = traceback.format_exc()
        finally:
            stop_event.set()

    # Headless vs TUI
    is_headless = not sys.stdout.isatty() or os.getenv("CI") or quiet
    if is_headless:
        os.environ["PDD_FORCE"] = "1"
        worker_logic()
    else:
        app = SyncApp(
            basename=basename,
            func_name_ref=current_func_ref,
            cost_ref=cost_ref,
            budget=budget,
            p_path=p_path, c_path=c_path, e_path=e_path, t_path=t_path,
            p_color=p_color, c_color=c_color, e_color=e_color, t_color=t_color,
            stop_event=stop_event
        )
        app_ref.append(app)
        app.worker_func = worker_logic
        app.run()
        
        if not quiet:
            show_exit_animation(basename, results["success"], results["total_cost"], results["total_time"])

    results["error"] = "; ".join(results["errors"]) if results["errors"] else None
    return results

def _execute_op(op: str, basename: str, language: str, paths: Dict, config: Dict) -> Dict:
    """Dispatches to the specific PDD command implementation."""
    ctx = config["ctx"]
    atomic = AtomicStateUpdate(basename, language)
    
    with atomic:
        if op == "auto-deps":
            # auto_deps_main returns (prompt, cost, model)
            _, cost, model = auto_deps_main(ctx, paths['prompt'], "examples/**/*", output=paths['prompt'])
            res = {"success": True, "cost": cost, "model": model}
        
        elif op == "generate":
            # code_generator_main returns (code, incremental, cost, model)
            _, _, cost, model = code_generator_main(ctx, paths['prompt'], output=paths['code'])
            # Clear run report to force re-validation
            run_path = META_DIR / f"{basename}_{language}_run.json"
            if run_path.exists(): run_path.unlink()
            res = {"success": True, "cost": cost, "model": model}

        elif op == "example":
            _, cost, model = context_generator_main(ctx, paths['prompt'], paths['code'], output=paths['example'])
            res = {"success": True, "cost": cost, "model": model}

        elif op == "crash":
            success, _, _, _, cost, model = crash_main(
                ctx, paths['prompt'], paths['code'], paths['example'], 
                str(META_DIR / "crash.log"), output=paths['code'], loop=True, 
                max_attempts=config["max_attempts"], budget=config["budget"]
            )
            # Re-run to update report
            _execute_tests_and_create_run_report(paths['example'], basename, language, config["target_coverage"], code_file=paths['code'], atomic_state=atomic)
            res = {"success": success, "cost": cost, "model": model}

        elif op == "verify":
            success, _, _, _, cost, model = fix_verification_main(
                ctx, paths['prompt'], paths['code'], paths['example'], 
                output_code=paths['code'], loop=True, max_attempts=config["max_attempts"], budget=config["budget"]
            )
            res = {"success": success, "cost": cost, "model": model}

        elif op == "test":
            _, cost, model = cmd_test_main(ctx, paths['prompt'], paths['code'], output=paths['test'])
            _execute_tests_and_create_run_report(paths['test'], basename, language, config["target_coverage"], code_file=paths['code'], atomic_state=atomic)
            res = {"success": True, "cost": cost, "model": model}

        elif op == "test_extend":
            _, cost, model = cmd_test_main(
                ctx, paths['prompt'], paths['code'], output=paths['test'], 
                existing_tests=[paths['test']], target_coverage=config["target_coverage"], merge=True
            )
            _execute_tests_and_create_run_report(paths['test'], basename, language, config["target_coverage"], code_file=paths['code'], atomic_state=atomic)
            res = {"success": True, "cost": cost, "model": model}

        elif op == "fix":
            # Identify failing files
            run_report = read_run_report(basename, language)
            test_to_fix = paths['test']
            if run_report and getattr(run_report, 'output', None):
                failing = extract_failing_files_from_output(run_report.output)
                if failing: test_to_fix = failing[0]

            success, _, _, _, cost, model = fix_main(
                ctx, paths['prompt'], paths['code'], test_to_fix, "", 
                output_code=paths['code'], loop=True, max_attempts=config["max_attempts"], budget=config["budget"]
            )
            _execute_tests_and_create_run_report(paths['test'], basename, language, config["target_coverage"], code_file=paths['code'], atomic_state=atomic)
            res = {"success": success, "cost": cost, "model": model}

        elif op == "update":
            _, cost, model = update_main(ctx, paths['prompt'], paths['code'], use_git=True)
            res = {"success": True, "cost": cost, "model": model}
        
        else:
            raise ValueError(f"Unknown operation: {op}")

        # Save Fingerprint on success
        if res.get("success"):
            _save_operation_fingerprint(basename, language, op, paths, res['cost'], res['model'], atomic)
            
    return res

def _execute_tests_and_create_run_report(test_file: str, basename: str, language: str, target_coverage: float, *, code_file=None, atomic_state=None, test_files=None):
    """Runs tests and captures results into a RunReport."""
    cmd = get_test_command_for_file(test_file, language=language)
    if not cmd: return
    
    # Isolate from TUI
    env = os.environ.copy()
    env.pop("FORCE_COLOR", None)
    env.pop("COLUMNS", None)
    
    try:
        proc = subprocess.run(cmd, shell=True, capture_output=True, text=True, env=env, start_new_session=True, stdin=subprocess.DEVNULL)
        passed, failed, coverage = _parse_test_output(proc.stdout + proc.stderr, language)
        
        report = RunReport(
            timestamp=datetime.datetime.now(timezone.utc).isoformat(),
            exit_code=proc.returncode,
            tests_passed=passed,
            tests_failed=failed,
            coverage=coverage,
            output=proc.stdout + proc.stderr
        )
        
        if atomic_state:
            atomic_state.pending_report = report
        else:
            save_run_report(report, basename, language)
            
    except Exception as e:
        logging.error(f"Failed to execute tests: {e}")

def _parse_test_output(output: str, language: str):
    """Heuristic parsing of test runner output."""
    passed, failed, coverage = 0, 0, 0.0
    
    # Pytest
    if "collected" in output:
        m = re.search(r"(\d+) passed", output)
        if m: passed = int(m.group(1))
        m = re.search(r"(\d+) failed", output)
        if m: failed = int(m.group(1))
        m = re.search(r"TOTAL\s+\d+\s+\d+\s+(\d+)%", output)
        if m: coverage = float(m.group(1))
        
    # Jest/Vitest
    elif "Tests:" in output:
        m = re.search(r"(\d+) passed", output)
        if m: passed = int(m.group(1))
        m = re.search(r"(\d+) failed", output)
        if m: failed = int(m.group(1))
        m = re.search(r"All files\s+\|\s+([\d.]+)", output)
        if m: coverage = float(m.group(1))

    return passed, failed, coverage

def _save_operation_fingerprint(basename, language, operation, paths, cost, model, atomic_state):
    """Prepares a fingerprint for the atomic update."""
    hashes = calculate_current_hashes(paths)
    fp = Fingerprint(
        version=__version__,
        timestamp=datetime.datetime.now(timezone.utc).isoformat(),
        operation=operation,
        prompt_hash=hashes.get('prompt'),
        code_hash=hashes.get('code'),
        example_hash=hashes.get('example'),
        test_hash=hashes.get('test'),
        cost=cost,
        model=model
    )
    atomic_state.pending_fingerprint = fp

def _handle_skip(basename, language, op, paths):
    """Saves a 'skip' fingerprint and synthetic report."""
    hashes = calculate_current_hashes(paths)
    fp = Fingerprint(
        version=__version__,
        timestamp=datetime.datetime.now(timezone.utc).isoformat(),
        operation=f"skip:{op}",
        prompt_hash=hashes.get('prompt'),
        code_hash=hashes.get('code'),
        example_hash=hashes.get('example'),
        test_hash=hashes.get('test')
    )
    path = META_DIR / f"{basename}_{language}.json"
    with open(path, 'w') as f:
        json.dump(fp.__dict__, f, indent=4)
        
    if op in ("verify", "crash"):
        report = RunReport(datetime.datetime.now(timezone.utc).isoformat(), 0, 1, 0, 100.0)
        save_run_report(report, basename, language)

def _detect_infinite_loop(ops: List[str]) -> bool:
    """Detects repetitive patterns in the operation history."""
    if len(ops) < 4: return False
    
    # Consecutive limits
    if ops[-MAX_CONSECUTIVE_TESTS:] == ["test"] * MAX_CONSECUTIVE_TESTS: return True
    if ops[-MAX_CONSECUTIVE_CRASHES:] == ["crash"] * MAX_CONSECUTIVE_CRASHES: return True
    
    # Cycle limits (e.g. crash -> verify -> crash -> verify)
    if len(ops) >= 4 * MAX_CYCLE_REPEATS:
        tail = ops[-(4 * MAX_CYCLE_REPEATS):]
        if tail == ["crash", "verify"] * (2 * MAX_CYCLE_REPEATS): return True
        if tail == ["test", "fix"] * (2 * MAX_CYCLE_REPEATS): return True
        
    return False

def _update_box_colors(op, success, p, c, e, t):
    """Updates TUI box colors based on operation outcome."""
    color = "green" if success else "red"
    if op == "auto-deps": p[0] = color
    elif op in ("generate", "crash", "verify"): c[0] = color
    elif op == "example": e[0] = color
    elif op in ("test", "test_extend", "fix"): t[0] = color

def _create_mock_context(**kwargs):
    """Creates a minimal Click-like context."""
    class MockCtx:
        def __init__(self, params):
            self.params = params
            self.obj = params
        def ensure_object(self, t): return self.obj
    return MockCtx(kwargs)

def save_run_report(report: RunReport, basename: str, language: str):
    path = META_DIR / f"{basename}_{language}_run.json"
    with open(path, 'w') as f:
        json.dump(report.__dict__, f, indent=4)

def log_sync_event(basename, language, event, details):
    path = META_DIR / f"{basename}_{language}_sync.log"
    entry = {
        "timestamp": datetime.datetime.now(timezone.utc).isoformat(),
        "event": event,
        "details": details
    }
    with open(path, 'a') as f:
        f.write(json.dumps(entry) + "\n")

def load_sync_log(basename, language):
    path = META_DIR / f"{basename}_{language}_sync.log"
    if not path.exists(): return []
    with open(path, 'r') as f:
        return [json.loads(line) for line in f]

def _display_sync_log(basename, language, verbose):
    entries = load_sync_log(basename, language)
    if not entries:
        print(f"No sync history found for {basename}_{language}")
        return
    for e in entries:
        print(f"[{e['timestamp']}] {e['event']}: {e['details']}")

if __name__ == "__main__":
    # Example usage if run as a script
    sync_orchestration("example_module", language="python")

# End of file",
  "focus": "python",
  "explanation": "The extracted code is a Python module that orchestrates a PDD (Prompt-Driven Development) workflow. It includes logic for state management, TUI integration, operation dispatching (generate, test, fix, etc.), and infinite loop detection. The code was extracted from the provided LLM output, ensuring all imports, classes, and functions are preserved and properly formatted according to PEP 8. A conditional main block was added for example execution as per the instructions."
}