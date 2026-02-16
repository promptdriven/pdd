An implementation of the `sync_orchestration` module for the PDD (Prompt-Driven Development) CLI. This module coordinates the complete development workflow, managing state, executing operations, and providing real-time feedback via the TUI.

```python
# sync_orchestration_python.prompt

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
from typing import Dict, Any, Optional, List, Callable, Tuple, Union
from dataclasses import asdict, dataclass, field
import click

from .sync_tui import maybe_steer_operation, DEFAULT_STEER_TIMEOUT_S
from .sync_tui import SyncApp
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
DEFAULT_BUDGET = 20.0
DEFAULT_MAX_ATTEMPTS = 3


def get_extension(language: str) -> str:
    """Helper to get file extension from language name."""
    lang_lower = language.lower()
    if lang_lower == "python":
        return ".py"
    elif lang_lower in ("javascript", "js"):
        return ".js"
    elif lang_lower in ("typescript", "ts"):
        return ".ts"
    elif lang_lower in ("java",):
        return ".java"
    elif lang_lower in ("cpp", "c++"):
        return ".cpp"
    elif lang_lower in ("c",):
        return ".c"
    elif lang_lower in ("go", "golang"):
        return ".go"
    elif lang_lower in ("rust",):
        return ".rs"
    return f".{lang_lower}"


def _create_mock_context(local: bool = False, verbose: bool = False, 
                        quiet: bool = False, force: bool = False, **kwargs) -> click.Context:
    """Creates a mock Click context for invoking CLI commands programmatically."""
    ctx = click.Context(click.Command("mock"))
    ctx.params = {"local": local, "force": force, "quiet": quiet, "verbose": verbose}
    ctx.obj = {
        "local": local,
        "verbose": verbose,
        "quiet": quiet,
        "force": force,
        **kwargs
    }
    return ctx


def _parse_test_output(output: str, language: str) -> Tuple[int, int, float]:
    """
    Parses test runner output to extract (tests_passed, tests_failed, coverage).
    
    Returns:
        Tuple of (passed, failed, coverage_percent)
    """
    passed = 0
    failed = 0
    coverage = 0.0
    lang_lower = language.lower()

    if lang_lower == "python":
        # Pytest output parsing
        # Try to find "X passed, Y failed" pattern
        passed_match = re.search(r"(\d+) passed", output)
        if passed_match:
            passed = int(passed_match.group(1))
        
        failed_match = re.search(r"(\d+) failed", output)
        if failed_match:
            failed = int(failed_match.group(1))
        
        error_match = re.search(r"(\d+) error", output)
        if error_match:
            # Treat errors as failures for PDD purposes
            failed += int(error_match.group(1))

        # Coverage parsing from pytest-cov
        cov_match = re.search(r"TOTAL\s+\d+\s+\d+\s+(\d+)%", output)
        if cov_match:
            coverage = float(cov_match.group(1))
            
    elif lang_lower in ("javascript", "typescript", "js", "ts"):
        # Jest/Vitest output parsing
        passed_match = re.search(r"Tests:\s+.*?(\d+) passed", output)
        if passed_match:
            passed = int(passed_match.group(1))
            
        failed_match = re.search(r"Tests:\s+.*?(\d+) failed", output)
        if failed_match:
            failed = int(failed_match.group(1))
            
        # Jest coverage: All files | % Stmts | ...
        cov_match = re.search(r"All files\s+\|\s+([\d\.]+)", output)
        if cov_match:
            try:
                coverage = float(cov_match.group(1))
            except ValueError:
                pass

    elif lang_lower in ("go", "golang"):
        # Go test output
        if "PASS" in output:
            passed = 1  # Approximate if individual count unavailable
        if "FAIL" in output:
            failed = 1
            
        cov_match = re.search(r"coverage: ([\d\.]+)% of statements", output)
        if cov_match:
            coverage = float(cov_match.group(1))
            
    elif lang_lower == "rust":
        # Cargo test output
        passed_match = re.search(r"test result: ok\. (\d+) passed", output)
        if passed_match:
            passed = int(passed_match.group(1))
            
        failed_match = re.search(r"(\d+) failed", output)
        if failed_match:
            failed = int(failed_match.group(1))

    return passed, failed, coverage


def _python_cov_target_for_code_file(code_file: Union[str, Path]) -> Optional[str]:
    """Determines dotted module path for pytest-cov from a code file path."""
    try:
        path = Path(code_file).resolve()
        # Find project root (setup.py, pyproject.toml, .git, etc)
        root = _find_project_root(path)
        if not root:
            return None
            
        # Calculate relative path from root
        try:
            rel_path = path.relative_to(root)
        except ValueError:
            return None
            
        # Convert to dotted notation, removing extension
        parts = list(rel_path.parts)
        if parts[-1].endswith('.py'):
            parts[-1] = parts[-1][:-3]
        
        # If inside src/, remove src from dotted path if it's a layout root
        if parts[0] == 'src' and (root / 'src').is_dir():
            parts = parts[1:]
            
        return ".".join(parts)
    except Exception:
        return None


def _python_cov_target_for_test_and_code(test_file: str, code_file: str, fallback: str) -> str:
    """Attempts to determine the best coverage target for pytest."""
    target = _python_cov_target_for_code_file(code_file)
    return target if target else fallback


class AtomicStateUpdate:
    """Context manager for atomic updates of PDD state files."""
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language.lower()
        self.meta_dir = Path(META_DIR)
        self.fingerprint_file = self.meta_dir / f"{_safe_basename(basename)}_{self.language}.json"
        self.run_report_file = self.meta_dir / f"{_safe_basename(basename)}_{self.language}_run.json"
        
        self.pending_fingerprint = None
        self.pending_run_report = None

    def __enter__(self):
        return self

    def save_fingerprint(self, data: Dict[str, Any]):
        self.pending_fingerprint = data

    def save_run_report(self, data: Dict[str, Any]):
        self.pending_run_report = data
    
    def clear_run_report(self):
        self.pending_run_report = "DELETE"

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type:
            return False  # Propagate exception
            
        # Write updates atomically if possible (using temp files + rename)
        if self.pending_fingerprint:
            self._atomic_write(self.fingerprint_file, self.pending_fingerprint)
            
        if self.pending_run_report:
            if self.pending_run_report == "DELETE":
                if self.run_report_file.exists():
                    self.run_report_file.unlink()
            else:
                self._atomic_write(self.run_report_file, self.pending_run_report)
        return True

    def _atomic_write(self, target_path: Path, data: Dict[str, Any]):
        tmp_fd, tmp_path = tempfile.mkstemp(dir=self.meta_dir, text=True)
        try:
            with os.fdopen(tmp_fd, 'w') as f:
                json.dump(data, f, indent=2)
            # Atomic rename
            os.replace(tmp_path, target_path)
        except Exception:
            os.unlink(tmp_path)
            raise


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
    """
    Executes tests and creates a RunReport.
    Supports running multiple test files if test_files list is provided.
    """
    lang_lower = language.lower()
    
    # Determine which files to run
    files_to_run = test_files if test_files else [test_file]
    
    # Prepare environment
    env = os.environ.copy()
    
    # Remove TUI interference
    env.pop("FORCE_COLOR", None)
    env.pop("COLUMNS", None)
    
    cmd_args = []
    
    if lang_lower == "python":
        # Python-specific logic with coverage
        project_root = _find_project_root(Path(test_file))
        if project_root:
            pythonpath = env.get("PYTHONPATH", "")
            src_path = str(project_root / "src")
            root_path = str(project_root)
            env["PYTHONPATH"] = f"{src_path}:{root_path}:{pythonpath}"

        python_exe = detect_host_python_executable() or sys.executable
        cmd_args = [python_exe, "-m", "pytest"]
        
        # Add coverage arguments if code_file known
        if code_file:
            # Try to get module name for coverage
            cov_target = _python_cov_target_for_test_and_code(test_file, code_file, basename)
            if cov_target:
                cmd_args.extend([f"--cov={cov_target}", "--cov-report=term-missing"])
        
        # Add test files
        cmd_args.extend(files_to_run)
        
        # Prevent picking up conftest from parent dirs if we found a root
        if project_root:
            cmd_args.extend(["-c", "/dev/null", f"--rootdir={project_root}"])

    else:
        # Non-Python languages: use generic test runner detection
        # We only support running multiple files if the test runner supports it
        # For now, we construct the command for the primary test file
        # and assume other files are picked up by the runner or we run them sequentially
        test_cmd = get_test_command_for_file(test_file, language=language)
        if not test_cmd:
            # Fallback if no test command found
            return RunReport(
                timestamp=datetime.datetime.now().isoformat(),
                exit_code=1,
                tests_passed=0,
                tests_failed=0,
                coverage=0.0,
                error="Could not determine test command"
            )
        cmd_args = test_cmd.split()

    # Execute
    try:
        result = subprocess.run(
            cmd_args,
            env=env,
            capture_output=True,
            text=True,
            start_new_session=True,  # Isolate from TUI process group
            stdin=subprocess.DEVNULL
        )
        stdout = result.stdout
        stderr = result.stderr
        exit_code = result.returncode
    except Exception as e:
        exit_code = 1
        stdout = ""
        stderr = str(e)

    # Parse output
    passed, failed, coverage = _parse_test_output(stdout + "\n" + stderr, language)
    
    # If exit code is non-zero but failed count is 0, it might be an error or crash
    if exit_code != 0 and failed == 0:
        # In pytest, exit code 1 means tests failed, 2 means interrupted/error
        # We'll assume at least 1 failure if non-zero exit
        failed = 1
    
    # Calculate hashes for report
    current_hash = calculate_sha256(Path(test_file))
    test_file_hashes = {}
    if test_files:
        for tf in test_files:
            if os.path.exists(tf):
                test_file_hashes[os.path.basename(tf)] = calculate_sha256(Path(tf))

    report = RunReport(
        timestamp=datetime.datetime.now().isoformat(),
        exit_code=exit_code,
        tests_passed=passed,
        tests_failed=failed,
        coverage=coverage,
        output=stdout + "\n" + stderr,
        test_hash=current_hash,
        test_file_hashes=test_file_hashes if test_file_hashes else None
    )

    # Save report
    if atomic_state:
        atomic_state.save_run_report(asdict(report))
    else:
        save_run_report(basename, language, asdict(report))
        
    return report


def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Returns True if we should use agentic path (non-Python OR agentic_mode for Python)."""
    return language.lower() != "python" or agentic_mode


def _create_synthetic_run_report_for_agentic_success(
    test_file: str, 
    basename: str, 
    language: str, 
    *, 
    atomic_state: Optional[AtomicStateUpdate] = None
) -> RunReport:
    """Creates a synthetic successful RunReport for agentic operations."""
    test_path = Path(test_file)
    test_hash = calculate_sha256(test_path) if test_path.exists() else "agentic_test_success"
    
    report = RunReport(
        timestamp=datetime.datetime.now().isoformat(),
        exit_code=0,
        tests_passed=1,  # Assume success
        tests_failed=0,
        coverage=0.0,    # Unknown
        test_hash=test_hash,
        output="Agentic verification successful"
    )
    
    if atomic_state:
        atomic_state.save_run_report(asdict(report))
    else:
        save_run_report(basename, language, asdict(report))
        
    return report


def sync_orchestration(
    basename: str,
    target_coverage: float = 90.0,
    language: str = "python",
    prompts_dir: str = "prompts",
    code_dir: str = "src",
    examples_dir: str = "examples",
    tests_dir: str = "tests",
    max_attempts: int = DEFAULT_MAX_ATTEMPTS,
    budget: float = DEFAULT_BUDGET,
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
    """
    Orchestrates the complete PDD sync workflow.
    """
    # Defaults defense in depth
    if target_coverage is None: target_coverage = 90.0
    if budget is None: budget = DEFAULT_BUDGET
    if max_attempts is None: max_attempts = DEFAULT_MAX_ATTEMPTS

    # State initialization
    start_time = time.time()
    total_cost = 0.0
    operations_completed = []
    skipped_operations = []
    errors = []
    file_state = {}
    last_model = None
    
    # Path resolution
    lang_ext = get_extension(language)
    
    # Use lowercase for language in metadata paths (case-insensitive filesystem safety)
    lang_lower = language.lower()

    # Determine if headless
    is_headless = (
        quiet 
        or not sys.stdout.isatty() 
        or os.environ.get("CI") 
        or os.environ.get("PDD_HEADLESS")
    )
    
    # Override confirm_callback in headless mode to auto-confirm if not provided
    user_confirmed_overwrite = [False]
    if is_headless and not confirm_callback:
        # In headless mode, we assume force=True or we just proceed
        # Setting PDD_FORCE=1 is a common pattern for headless runs in PDD
        os.environ["PDD_FORCE"] = "1"
        
        def headless_confirm(msg, file_path):
            user_confirmed_overwrite[0] = True
            return True
        confirm_callback = headless_confirm

    # Dry run handling
    if dry_run:
        # Load existing log if available
        log_entries = load_operation_log(basename, lang_lower)
        
        # Run one determination to see what would happen next
        try:
            decision = sync_determine_operation(
                basename, language, target_coverage, 
                prompts_dir=prompts_dir, code_dir=code_dir, 
                examples_dir=examples_dir, tests_dir=tests_dir,
                log_mode=True
            )
            
            # Format output for dry run
            dry_run_result = {
                "success": True,
                "operations_completed": [],
                "skipped_operations": [],
                "total_cost": 0.0,
                "total_time": 0.0,
                "final_state": {},
                "errors": [],
                "error": None,
                "model_name": None,
                "log_entries": log_entries,
                "next_operation": decision.operation,
                "reason": decision.reason,
                "confidence": decision.confidence
            }
            
            if verbose:
                # Print detailed log
                print(f"\n[Dry Run Analysis for {basename}]")
                print(f"Next Operation: {decision.operation}")
                print(f"Reason: {decision.reason}")
                print(f"Confidence: {decision.confidence}")
                print(f"Estimated Cost: ${decision.estimated_cost:.4f}")
            else:
                # Concise output
                print(json.dumps(dry_run_result, indent=2))
                
            return dry_run_result
            
        except Exception as e:
            return {
                "success": False,
                "error": str(e),
                "errors": [str(e)],
                "log_entries": log_entries
            }

    # TUI Coordination References
    app_ref: List[SyncApp] = []
    stop_event = threading.Event()
    
    # Mutable references for TUI updates
    function_name_ref = ["Initializing"]
    cost_ref = [0.0]
    
    # Status colors and paths for UI
    # Keys: prompt, code, example, test
    file_status_colors_ref = {
        "prompt": "yellow", "code": "blue", "example": "blue", "test": "blue"
    }
    file_paths_ref = {
        "prompt": "", "code": "", "example": "", "test": ""
    }
    
    # Callback for auto-deps progress
    progress_callback_ref = [None]
    
    # Loop tracking variables
    consecutive_tests = 0
    consecutive_crashes = 0
    consecutive_fixes = 0
    test_extend_attempts = 0
    cycle_history = []  # To detect repeating patterns like crash->verify->crash
    
    # Main workflow logic
    def sync_worker_logic():
        nonlocal total_cost, last_model, consecutive_tests, consecutive_crashes
        nonlocal consecutive_fixes, test_extend_attempts
        
        # Acquire lock
        try:
            with SyncLock(basename, lang_lower) as lock:
                log_event(basename, lang_lower, "lock_acquired", {"pid": os.getpid()}, "sync")
                
                # Check file paths initially
                paths_result = get_pdd_file_paths(
                    basename, language, prompts_dir, code_dir, examples_dir, tests_dir
                )
                
                # Update UI paths
                if paths_result.get("prompt"):
                    file_paths_ref["prompt"] = str(paths_result["prompt"])
                    file_status_colors_ref["prompt"] = "green"
                else:
                    file_status_colors_ref["prompt"] = "red"
                    
                # Main Loop
                while not stop_event.is_set():
                    # Budget Check
                    if total_cost >= budget:
                        msg = f"Budget limit reached (${budget:.2f})"
                        errors.append(msg)
                        log_event(basename, lang_lower, "budget_exceeded", {"limit": budget}, "sync")
                        break
                        
                    if budget - total_cost < (budget * 0.2):
                         log_event(basename, lang_lower, "budget_warning", {"remaining": budget - total_cost}, "sync")

                    # Determine Operation
                    try:
                        decision = sync_determine_operation(
                            basename, language, target_coverage,
                            prompts_dir=prompts_dir, code_dir=code_dir,
                            examples_dir=examples_dir, tests_dir=tests_dir
                        )
                    except Exception as e:
                        errors.append(f"Error determining operation: {e}")
                        traceback.print_exc()
                        break
                    
                    op = decision.operation
                    reason = decision.reason
                    
                    # Update TUI
                    function_name_ref[0] = f"{op}"
                    
                    # Terminal states
                    if op in ("all_synced", "nothing"):
                        function_name_ref[0] = "Synced"
                        break
                    
                    if op in ("fail_and_request_manual_merge", "error"):
                        errors.append(f"Sync failed: {reason}")
                        function_name_ref[0] = "Error"
                        break
                    
                    # Steering
                    if not no_steer and not is_headless:
                        # Call steering (interactive)
                        steered_op, should_abort = maybe_steer_operation(
                            op, reason, app_ref, quiet, skip_tests, skip_verify,
                            timeout_s=steer_timeout
                        )
                        
                        if should_abort:
                            errors.append("Operation aborted by user")
                            break
                            
                        if steered_op != op:
                            log_event(basename, lang_lower, "steering_override", 
                                     {"original": op, "new": steered_op}, "sync")
                            op = steered_op
                    
                    # Cycle Detection
                    cycle_history.append(op)
                    if len(cycle_history) > 10:
                        cycle_history.pop(0)
                        
                    # Pattern detection logic here if needed (e.g. crash->verify->crash->verify)
                    # Simplified checks:
                    if op == "test":
                        consecutive_tests += 1
                        if consecutive_tests > MAX_CONSECUTIVE_TESTS:
                            errors.append(f"Aborting: Too many consecutive test operations ({consecutive_tests})")
                            break
                    else:
                        consecutive_tests = 0
                        
                    if op == "crash":
                        consecutive_crashes += 1
                        if consecutive_crashes > MAX_CONSECUTIVE_CRASHES:
                            errors.append("Aborting: Too many consecutive crash operations")
                            break
                    else:
                        consecutive_crashes = 0
                        
                    if op == "fix":
                        consecutive_fixes += 1
                        if consecutive_fixes > 5:
                            errors.append("Aborting: Too many consecutive fix operations")
                            break
                    else:
                        consecutive_fixes = 0

                    # Resolve paths again (files might have been created)
                    paths = get_pdd_file_paths(
                        basename, language, prompts_dir, code_dir, examples_dir, tests_dir
                    )
                    
                    # Update UI status colors based on op
                    if op == "generate": file_status_colors_ref["code"] = "yellow"
                    elif op == "example": file_status_colors_ref["example"] = "yellow"
                    elif op == "test": file_status_colors_ref["test"] = "yellow"
                    
                    # Execute Operation
                    success = False
                    op_cost = 0.0
                    op_model = "unknown"
                    
                    # Create log entry
                    log_entry = create_log_entry(
                        operation=op,
                        reason=reason,
                        invocation_mode="sync",
                        estimated_cost=decision.estimated_cost,
                        confidence=decision.confidence,
                        decision_type=decision.decision_type
                    )

                    try:
                        with AtomicStateUpdate(basename, lang_lower) as atomic_state:
                            
                            # --- OP: AUTO-DEPS ---
                            if op == "auto-deps":
                                prompt_path = str(paths["prompt"])
                                # Use list of dirs if provided, or default
                                deps_ctx = _create_mock_context(
                                    local=local, verbose=verbose, quiet=quiet, force=True,
                                    strength=strength, temperature=temperature
                                )
                                # Pass progress callback to context if supported by auto_deps_main
                                # (Assuming auto_deps_main has been updated to accept it, or we wrap)
                                # For now we just run it
                                
                                res = auto_deps_main(
                                    ctx=deps_ctx,
                                    prompt_file=prompt_path,
                                    directory_path=examples_dir, # recursive scan default
                                    output=prompt_path, # overwrite
                                    force_scan=False,
                                    auto_deps_csv_path=None
                                )
                                
                                # Auto-deps returns (content, cost, model) or throws
                                if isinstance(res, tuple) and len(res) >= 3:
                                    _, op_cost, op_model = res[0], res[1], res[2]
                                success = True

                            # --- OP: GENERATE ---
                            elif op == "generate":
                                if not paths.get("prompt"):
                                    raise FileNotFoundError("Prompt file missing")
                                    
                                prompt_path = str(paths["prompt"])
                                code_path = str(paths.get("code") or Path(code_dir) / f"{basename}{lang_ext}")
                                
                                gen_ctx = _create_mock_context(
                                    local=local, verbose=verbose, quiet=quiet, force=True,
                                    strength=strength, temperature=temperature, time=time_param
                                )
                                
                                # code_generator_main returns (code, incremental, cost, model)
                                res = code_generator_main(
                                    ctx=gen_ctx,
                                    prompt_file=prompt_path,
                                    output=code_path,
                                    original_prompt_file_path=None, # Auto-detect from git
                                    force_incremental_flag=False
                                )
                                
                                op_cost, op_model = res[2], res[3]
                                success = True
                                
                                # Clear run report to force re-verification
                                atomic_state.clear_run_report()
                                file_paths_ref["code"] = code_path
                                file_status_colors_ref["code"] = "green"

                            # --- OP: EXAMPLE ---
                            elif op == "example":
                                prompt_path = str(paths["prompt"])
                                code_path = str(paths["code"])
                                example_path = str(paths.get("example") or Path(examples_dir) / f"{basename}_example{lang_ext}")
                                
                                ex_ctx = _create_mock_context(
                                    local=local, verbose=verbose, quiet=quiet, force=True,
                                    strength=strength, temperature=temperature
                                )
                                
                                res = context_generator_main(
                                    ctx=ex_ctx,
                                    prompt_file=prompt_path,
                                    code_file=code_path,
                                    output=example_path
                                )
                                
                                op_cost, op_model = res[1], res[2]
                                success = True
                                file_paths_ref["example"] = example_path
                                file_status_colors_ref["example"] = "green"

                            # --- OP: CRASH ---
                            elif op == "crash":
                                if skip_verify:
                                    skipped_operations.append("crash")
                                    # Create synthetic success report
                                    atomic_state.save_run_report(asdict(RunReport(
                                        timestamp=datetime.datetime.now().isoformat(),
                                        exit_code=0, tests_passed=1, tests_failed=0, coverage=0.0,
                                        output="Skipped crash verification"
                                    )))
                                    success = True
                                else:
                                    prompt_path = str(paths["prompt"])
                                    code_path = str(paths["code"])
                                    program_path = str(paths["example"])
                                    # Error log file usually generated by previous run attempt
                                    # But crash_main can run the program itself if we pass loop=True
                                    # For sync orchestration, we generally want loop=True
                                    
                                    # Determine if we should use agentic fallback
                                    use_agentic = _use_agentic_path(language, agentic_mode)
                                    attempts_limit = 0 if use_agentic else max_attempts
                                    
                                    crash_ctx = _create_mock_context(
                                        local=local, verbose=verbose, quiet=quiet, force=True,
                                        strength=strength, temperature=temperature, time=time_param
                                    )
                                    
                                    # crash_main returns (success, final_code, final_program, attempts, cost, model)
                                    # Or throws
                                    res = crash_main(
                                        ctx=crash_ctx,
                                        prompt_file=prompt_path,
                                        code_file=code_path,
                                        program_file=program_path,
                                        error_file="crash_errors.log", # Temporary file
                                        output=code_path,
                                        output_program=program_path,
                                        loop=True,
                                        max_attempts=attempts_limit,
                                        budget=budget - total_cost,
                                        agentic_fallback=True # Allow fallback
                                    )
                                    
                                    success, _, _, _, op_cost, op_model = res
                                    
                                    # If non-python, assume success means it runs now
                                    if success:
                                        if use_agentic:
                                            _create_synthetic_run_report_for_agentic_success(
                                                program_path, basename, language, atomic_state=atomic_state
                                            )
                                        else:
                                            # Python: re-run to verify
                                            # We just assume success here, verification happens in verify step or next cycle
                                            pass

                            # --- OP: VERIFY ---
                            elif op == "verify":
                                if skip_verify:
                                    skipped_operations.append("verify")
                                    success = True
                                    # Create synthetic report so we don't get stuck
                                    atomic_state.save_run_report(asdict(RunReport(
                                        timestamp=datetime.datetime.now().isoformat(),
                                        exit_code=0, tests_passed=1, tests_failed=0, coverage=0.0,
                                        output="Skipped functional verification"
                                    )))
                                else:
                                    prompt_path = str(paths["prompt"])
                                    code_path = str(paths["code"])
                                    program_path = str(paths["example"])
                                    
                                    use_agentic = _use_agentic_path(language, agentic_mode)
                                    attempts_limit = 0 if use_agentic else max_attempts

                                    verify_ctx = _create_mock_context(
                                        local=local, verbose=verbose, quiet=quiet, force=True,
                                        strength=strength, temperature=temperature, time=time_param
                                    )
                                    
                                    res = fix_verification_main(
                                        ctx=verify_ctx,
                                        prompt_file=prompt_path,
                                        code_file=code_path,
                                        program_file=program_path,
                                        output_code=code_path,
                                        output_program=program_path,
                                        output_results=f"{basename}_verify_results.log",
                                        loop=True,
                                        max_attempts=attempts_limit,
                                        budget=budget - total_cost,
                                        agentic_fallback=True
                                    )
                                    
                                    success, _, _, _, op_cost, op_model = res
                                    if success:
                                         if use_agentic:
                                            _create_synthetic_run_report_for_agentic_success(
                                                program_path, basename, language, atomic_state=atomic_state
                                            )

                            # --- OP: TEST ---
                            elif op == "test":
                                if skip_tests:
                                    skipped_operations.append("test")
                                    success = True
                                else:
                                    prompt_path = str(paths["prompt"])
                                    code_path = str(paths["code"])
                                    # Default test path
                                    test_path = str(paths.get("test") or Path(tests_dir) / f"test_{basename}{lang_ext}")
                                    
                                    test_ctx = _create_mock_context(
                                        local=local, verbose=verbose, quiet=quiet, force=True,
                                        strength=strength, temperature=temperature
                                    )
                                    
                                    # cmd_test_main returns (code, cost, model, agentic_success)
                                    res = cmd_test_main(
                                        ctx=test_ctx,
                                        prompt_file=prompt_path,
                                        code_file=code_path,
                                        output=test_path,
                                        language=language,
                                        target_coverage=target_coverage,
                                        merge=False # Fresh generation
                                    )
                                    
                                    # Unpack carefully
                                    _, op_cost, op_model, agentic_success = res
                                    
                                    # Determine success
                                    if agentic_success is not None:
                                        success = agentic_success
                                        if success:
                                            _create_synthetic_run_report_for_agentic_success(
                                                test_path, basename, language, atomic_state=atomic_state
                                            )
                                    else:
                                        # Python/legacy behavior: check file creation
                                        success = os.path.exists(test_path)
                                        if success:
                                            # Run tests to populate report
                                            _execute_tests_and_create_run_report(
                                                test_path, basename, language, target_coverage, 
                                                code_file=code_path, atomic_state=atomic_state
                                            )
                                    
                                    if success:
                                        file_paths_ref["test"] = test_path
                                        file_status_colors_ref["test"] = "green"

                            # --- OP: TEST_EXTEND ---
                            elif op == "test_extend":
                                if skip_tests or test_extend_attempts >= MAX_TEST_EXTEND_ATTEMPTS:
                                    skipped_operations.append("test_extend")
                                    success = True
                                elif _use_agentic_path(language, agentic_mode):
                                     # Skip extend for non-Python/agentic
                                    skipped_operations.append("test_extend")
                                    success = True
                                else:
                                    test_extend_attempts += 1
                                    prompt_path = str(paths["prompt"])
                                    code_path = str(paths["code"])
                                    test_path = str(paths["test"])
                                    
                                    # Get coverage report
                                    # Assuming coverage.xml or similar exists from previous run
                                    # For PDD's simple pytest runs, we might not have XML
                                    # But cmd_test_main can handle existing tests
                                    
                                    test_ctx = _create_mock_context(
                                        local=local, verbose=verbose, quiet=quiet, force=True,
                                        strength=strength, temperature=temperature
                                    )
                                    
                                    res = cmd_test_main(
                                        ctx=test_ctx,
                                        prompt_file=prompt_path,
                                        code_file=code_path,
                                        output=test_path,
                                        language=language,
                                        target_coverage=target_coverage,
                                        existing_tests=[test_path],
                                        merge=True # Merge new tests
                                    )
                                    
                                    _, op_cost, op_model, _ = res
                                    success = True
                                    
                                    # Re-run tests
                                    _execute_tests_and_create_run_report(
                                        test_path, basename, language, target_coverage, 
                                        code_file=code_path, atomic_state=atomic_state
                                    )

                            # --- OP: FIX ---
                            elif op == "fix":
                                prompt_path = str(paths["prompt"])
                                code_path = str(paths["code"])
                                test_path = str(paths["test"])
                                
                                # Handle multiple test files
                                test_files = paths.get("test_files", [test_path])
                                failing_file = test_path
                                
                                # Try to identify failing file from last run output if possible
                                if "run_report" in locals() and "output" in locals()["run_report"]:
                                    # This requires us to read the run report, which we can do
                                    try:
                                        rr = read_run_report(basename, language)
                                        if rr and rr.output:
                                            extracted = extract_failing_files_from_output(rr.output, [Path(f) for f in test_files])
                                            if extracted:
                                                failing_file = str(extracted[0])
                                    except:
                                        pass
                                
                                use_agentic = _use_agentic_path(language, agentic_mode)
                                attempts_limit = 0 if use_agentic else max_attempts

                                fix_ctx = _create_mock_context(
                                    local=local, verbose=verbose, quiet=quiet, force=True,
                                    strength=strength, temperature=temperature, time=time_param
                                )
                                
                                # fix_main returns (success, fixed_test, fixed_code, attempts, cost, model)
                                res = fix_main(
                                    ctx=fix_ctx,
                                    prompt_file=prompt_path,
                                    code_file=code_path,
                                    unit_test_file=test_path, # Passed as primary
                                    error_file="fix_errors.log", # Ignored in loop mode mostly
                                    output_test=failing_file, # Update specific file
                                    output_code=code_path,
                                    loop=True,
                                    max_attempts=attempts_limit,
                                    budget=budget - total_cost,
                                    agentic_fallback=True,
                                    test_files=test_files # Pass all for context
                                )
                                
                                success, _, _, _, op_cost, op_model = res
                                
                                if success:
                                    if use_agentic:
                                        _create_synthetic_run_report_for_agentic_success(
                                            test_path, basename, language, atomic_state=atomic_state
                                        )
                                    else:
                                        # Python: Re-run to update report
                                        _execute_tests_and_create_run_report(
                                            test_path, basename, language, target_coverage, 
                                            code_file=code_path, atomic_state=atomic_state,
                                            test_files=test_files
                                        )

                            # --- OP: UPDATE ---
                            elif op == "update":
                                prompt_path = str(paths["prompt"])
                                code_path = str(paths["code"])
                                
                                update_ctx = _create_mock_context(
                                    local=local, verbose=verbose, quiet=quiet, force=True,
                                    strength=strength, temperature=temperature
                                )
                                
                                # update_main returns (prompt, cost, model)
                                res = update_main(
                                    ctx=update_ctx,
                                    input_prompt_file=prompt_path,
                                    modified_code_file=code_path,
                                    use_git=False, # We use explicit files
                                    input_code_file=None, # Should infer or we might need original...
                                    # Actually update usually needs git or original. 
                                    # If not git, we might lack original. 
                                    # But update_main can handle just modifying prompt to match code
                                    # assuming code is source of truth now.
                                )
                                
                                _, op_cost, op_model = res
                                success = True
                                
                                # After update, we should clear run report because prompt changed?
                                # Actually, code didn't change, prompt did. 
                                # But we want to re-verify consistency.
                                atomic_state.clear_run_report()

                            # Save Fingerprint on Success
                            if success:
                                current_hashes = calculate_current_hashes(
                                    prompt=paths.get("prompt"),
                                    code=paths.get("code"),
                                    example=paths.get("example"),
                                    test=paths.get("test")
                                )
                                # Add test files hashes if any
                                if "test_files" in paths:
                                    for tf in paths["test_files"]:
                                        if os.path.exists(tf):
                                            current_hashes[f"hash_{os.path.basename(tf)}"] = calculate_sha256(Path(tf))

                                atomic_state.save_fingerprint({
                                    "version": "1.0",
                                    "timestamp": datetime.datetime.now().isoformat(),
                                    "last_operation": op,
                                    "hashes": current_hashes,
                                    "cost": op_cost,
                                    "model": op_model
                                })

                    except Exception as e:
                        success = False
                        msg = f"Exception in {op}: {str(e)}"
                        errors.append(msg)
                        if verbose:
                            traceback.print_exc()
                        
                        # Update log with failure
                        update_log_entry(
                            entry=log_entry,
                            success=False,
                            cost=op_cost,
                            model=op_model,
                            duration=time.time() - start_time, # Rough duration
                            error=str(e)
                        )
                        append_log_entry(basename, lang_lower, log_entry)
                        break

                    # Update Log Entry with Success
                    update_log_entry(
                        entry=log_entry,
                        success=success,
                        cost=op_cost,
                        model=op_model,
                        duration=time.time() - start_time,
                        error=None
                    )
                    append_log_entry(basename, lang_lower, log_entry)
                    
                    # Accumulate costs
                    total_cost += op_cost
                    cost_ref[0] = total_cost
                    last_model = op_model
                    
                    if success:
                        operations_completed.append(op)
                        # Reset status colors for completed items
                        if op == "generate": file_status_colors_ref["code"] = "green"
                        elif op == "example": file_status_colors_ref["example"] = "green"
                        elif op == "test": file_status_colors_ref["test"] = "green"
                    else:
                        errors.append(f"Operation {op} failed")
                        break
                        
        except Exception as e:
            errors.append(f"Sync loop error: {str(e)}")
            if verbose:
                traceback.print_exc()
        finally:
            log_event(basename, lang_lower, "lock_released", {}, "sync")

    # Start Worker
    if is_headless:
        # Run directly
        sync_worker_logic()
        final_file_state = {} # Would be populated if we needed it
    else:
        # Run via TUI
        app = SyncApp(
            worker_func=sync_worker_logic,
            basename=basename,
            function_name_ref=function_name_ref,
            cost_ref=cost_ref,
            file_status_colors_ref=file_status_colors_ref,
            file_paths_ref=file_paths_ref,
            stop_event=stop_event,
            confirm_callback=confirm_callback,
            user_confirmed_overwrite=user_confirmed_overwrite,
            progress_callback_ref=progress_callback_ref
        )
        app_ref.append(app)
        
        try:
            app.run()
        except Exception as e:
            # Check for worker exception
            if hasattr(app, 'worker_exception') and app.worker_exception:
                print(f"Worker thread crashed: {app.worker_exception}", file=sys.stderr)
                traceback.print_exception(type(app.worker_exception), app.worker_exception, app.worker_exception.__traceback__)
            else:
                print(f"TUI crashed: {e}", file=sys.stderr)
            errors.append(str(e))
            
        if not quiet and not is_headless:
            # Import strictly here to avoid circular imports if any
            from .sync_tui import show_exit_animation
            show_exit_animation()

    # Final result compilation
    final_paths = get_pdd_file_paths(
        basename, language, prompts_dir, code_dir, examples_dir, tests_dir
    )
    final_state = {
        k: {"exists": p.exists(), "path": str(p)} 
        for k, p in final_paths.items() 
        if isinstance(p, Path)
    }

    # Output CSV Cost if requested
    if output_cost:
        # PDD infrastructure handles this via global flags, but if we need to write specific record
        pass

    return {
        "success": len(errors) == 0,
        "operations_completed": operations_completed,
        "skipped_operations": skipped_operations,
        "total_cost": total_cost,
        "total_time": time.time() - start_time,
        "final_state": final_state,
        "errors": errors,
        "error": "; ".join(errors) if errors else None,
        "model_name": last_model,
        "log_entries": [] # Only populated in dry_run
    }
```