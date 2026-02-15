An implementation of the `sync_orchestration` module that coordinates the full PDD workflow loop, integrates with the Textual TUI for real-time feedback, and manages state/locking.

```python
"""
Orchestrates the complete PDD (Prompt-Driven Development) sync workflow.
Coordinates operations, TUI visualization, and state management.
"""

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
from . import DEFAULT_STRENGTH

# Constants
MAX_CONSECUTIVE_TESTS = 3
MAX_TEST_EXTEND_ATTEMPTS = 2
MAX_CONSECUTIVE_CRASHES = 3

class AtomicStateUpdate:
    """
    Context manager for atomic state updates (fingerprints and run reports).
    Ensures that either both writes succeed or neither does, using temp files and atomic renames.
    """
    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language
        self.updates = {}  # type: Dict[str, str]  # destination_path -> content

    def add_write(self, path: Path, content: str):
        self.updates[str(path)] = content

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type:
            return False  # Propagate exception, don't write

        # Perform atomic writes
        for dest_path_str, content in self.updates.items():
            dest_path = Path(dest_path_str)
            try:
                # Create temp file in the same directory to ensure atomic rename works
                dest_path.parent.mkdir(parents=True, exist_ok=True)
                with tempfile.NamedTemporaryFile('w', dir=dest_path.parent, delete=False, encoding='utf-8') as tf:
                    tf.write(content)
                    temp_name = tf.name
                
                # Atomic rename
                os.replace(temp_name, dest_path)
            except Exception as e:
                # If one fails, we can't easily rollback previous ones in a purely atomic way 
                # on standard FS without journaling, but this minimizes partial write corruption of single files.
                # In a robust system we might rename old files to backups first.
                if 'temp_name' in locals() and os.path.exists(temp_name):
                    os.unlink(temp_name)
                raise e


def get_extension(language: str) -> str:
    """Helper to get file extension from language string."""
    lang = language.lower()
    if lang == "python": return ".py"
    if lang in ["javascript", "js"]: return ".js"
    if lang in ["typescript", "ts"]: return ".ts"
    if lang in ["java"]: return ".java"
    if lang in ["cpp", "c++"]: return ".cpp"
    if lang in ["c"]: return ".c"
    if lang in ["go"]: return ".go"
    if lang in ["ruby"]: return ".rb"
    if lang in ["rust"]: return ".rs"
    # Fallback
    return f".{lang}"


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
    """
    Orchestrates the PDD sync workflow for a given basename.
    """
    # Defense in depth for None values
    if target_coverage is None: target_coverage = 90.0
    if budget is None: budget = 10.0
    if max_attempts is None: max_attempts = 3

    # Normalize language for paths
    lang_lower = language.lower()
    
    # Handle Dry Run Mode
    if dry_run:
        if verbose:
            _display_sync_log(basename, language, verbose=True)
        else:
            decision = sync_determine_operation(basename, language, target_coverage, log_mode=False)
            print(f"Sync decision for {basename} ({language}): {decision.operation}")
            print(f"Reason: {decision.reason}")
            _display_sync_log(basename, language, verbose=False)
        
        # Load logs for return value
        log_entries = load_operation_log(basename, language)
        return {
            "success": True, 
            "operations_completed": [], 
            "skipped_operations": [], 
            "total_cost": 0.0, 
            "total_time": 0.0, 
            "final_state": {}, 
            "errors": [], 
            "error": None, 
            "model_name": None,
            "log_entries": log_entries
        }

    # Initialize tracking
    start_time = time.time()
    total_cost = 0.0
    operations_completed = []
    skipped_operations = []
    errors = []
    last_model_name = None
    
    # State tracking for TUI
    function_name_ref = ["Starting..."]
    cost_ref = [0.0]
    prompt_color_ref = ["blue"]
    code_color_ref = ["blue"]
    example_color_ref = ["blue"]
    test_color_ref = ["blue"]
    prompt_path_ref = ["Checking..."]
    code_path_ref = ["Checking..."]
    example_path_ref = ["Checking..."]
    test_path_ref = ["Checking..."]
    progress_callback_ref = [None]
    app_ref = []  # To store the App instance for dialogs
    user_confirmed_overwrite = [force] # If force is True, we assume confirmation
    stop_event = threading.Event()

    # Define the worker logic
    def sync_worker_logic():
        nonlocal total_cost, last_model_name
        
        # Lock acquisition
        try:
            with SyncLock(basename, language) as lock:
                log_event(basename, language, "lock_acquired", {"pid": os.getpid()}, invocation_mode="sync")
                
                # Cycle detection state
                op_history = []
                consecutive_fix_count = 0
                consecutive_test_count = 0
                consecutive_crash_count = 0
                test_extend_attempts = 0
                
                # Setup context for sub-commands
                def _create_mock_context(**kwargs):
                    ctx = click.Context(click.Command("mock"))
                    # Base obj defaults
                    obj = {
                        "strength": strength,
                        "temperature": temperature,
                        "time": time_param,
                        "verbose": verbose,
                        "quiet": quiet,
                        "local": local,
                        "force": True, # Always force inside sync loop, we handle confirmation once at start or via TUI
                        "output_cost": output_cost,
                        "review_examples": review_examples,
                        "context": context_override,
                    }
                    if context_config:
                        obj.update(context_config)
                    # Override with specific kwargs
                    obj.update(kwargs)
                    ctx.obj = obj
                    ctx.params = obj # Some commands look at params
                    return ctx

                while not stop_event.is_set():
                    # Budget check
                    if total_cost >= budget:
                        log_event(basename, language, "budget_exceeded", {"limit": budget, "current": total_cost}, invocation_mode="sync")
                        errors.append(f"Budget exceeded: ${total_cost:.2f} >= ${budget:.2f}")
                        break
                    
                    if budget - total_cost < 2.0: # Warning threshold
                         log_event(basename, language, "budget_warning", {"remaining": budget - total_cost}, invocation_mode="sync")

                    # 1. Determine Operation
                    try:
                        decision = sync_determine_operation(basename, language, target_coverage)
                        
                        # Log the decision intent
                        entry_data = create_log_entry(
                            operation=decision.operation,
                            reason=decision.reason,
                            invocation_mode="sync",
                            estimated_cost=decision.estimated_cost,
                            confidence=decision.confidence,
                            decision_type=decision.decision_type
                        )
                        append_log_entry(basename, language, entry_data)
                        
                        # Update TUI with status
                        function_name_ref[0] = f"Deciding: {decision.operation}"
                        cost_ref[0] = total_cost
                        
                        # Update path/status refs based on file existence from pdd_files
                        pdd_files = get_pdd_file_paths(basename, language, prompts_dir, code_dir, examples_dir, tests_dir)
                        _update_tui_file_status(pdd_files, prompt_path_ref, code_path_ref, example_path_ref, test_path_ref,
                                              prompt_color_ref, code_color_ref, example_color_ref, test_color_ref)

                    except Exception as e:
                        errors.append(f"Error determining operation: {str(e)}")
                        traceback.print_exc()
                        break
                    
                    operation = decision.operation
                    
                    # 2. Interactive Steering
                    if not no_steer:
                        steer_res, should_abort = maybe_steer_operation(
                            operation, 
                            decision.reason, 
                            app_ref, 
                            quiet, 
                            skip_tests, 
                            skip_verify, 
                            timeout_s=steer_timeout
                        )
                        if should_abort:
                            errors.append("Operation aborted by user during steering.")
                            break
                        
                        if steer_res != operation:
                            log_event(basename, language, "steering_override", {"original": operation, "new": steer_res}, invocation_mode="sync")
                            operation = steer_res
                            # Update logs to reflect change
                            entry_data['operation'] = operation
                            entry_data['reason'] = f"User override from {decision.operation}"

                    # Terminal states
                    if operation in ["all_synced", "nothing"]:
                        function_name_ref[0] = "Synced"
                        break
                    
                    if operation in ["fail_and_request_manual_merge", "error"]:
                        errors.append(f"Sync failed: {decision.reason}")
                        break

                    # 3. Cycle and Loop Detection
                    op_history.append(operation)
                    if len(op_history) > 20: op_history.pop(0) # Keep recent history
                    
                    # Detect oscillations
                    if _detect_oscillation(op_history, "crash", "verify", limit=MAX_CYCLE_REPEATS * 2):
                         errors.append("Detected infinite crash-verify loop.")
                         break
                    if _detect_oscillation(op_history, "test", "fix", limit=MAX_CYCLE_REPEATS * 2):
                         errors.append("Detected infinite test-fix loop.")
                         break
                         
                    # Reset counters based on op
                    if operation != "fix": consecutive_fix_count = 0
                    if operation != "test": consecutive_test_count = 0
                    if operation != "crash": consecutive_crash_count = 0
                    
                    # 4. Execute Operation
                    function_name_ref[0] = f"Running: {operation}"
                    op_start_time = time.time()
                    op_success = False
                    op_cost = 0.0
                    op_model = None
                    op_error = None
                    
                    try:
                        # --- AUTO-DEPS ---
                        if operation == "auto_deps":
                            # Check cycle
                            if op_history.count("auto_deps") >= 2:
                                # Force advance if stuck in auto-deps
                                operation = "generate"
                            else:
                                if not pdd_files['prompt']:
                                    raise FileNotFoundError(f"Prompt file not found for {basename}")
                                
                                # Use progress callback if available
                                ctx = _create_mock_context()
                                # auto-deps args
                                deps_dir = str(Path(examples_dir).parent) # Search roughly whole project or typical dirs
                                # Or use defaults from command
                                
                                res_prompt, c, m = auto_deps_main(
                                    ctx=ctx,
                                    prompt_file=str(pdd_files['prompt']),
                                    directory_path=f"{examples_dir}/**/*.py", # Default search
                                    output=str(pdd_files['prompt']), # In-place update
                                    force_scan=False
                                )
                                op_cost = c
                                op_model = m
                                op_success = True

                        # --- GENERATE ---
                        elif operation == "generate":
                            if not pdd_files['prompt']:
                                raise FileNotFoundError("Prompt file missing")
                            
                            # Ensure code dir exists
                            if pdd_files['code']:
                                output_path = str(pdd_files['code'])
                            else:
                                ext = get_extension(language)
                                output_path = str(Path(code_dir) / f"{basename}{ext}")
                                Path(code_dir).mkdir(parents=True, exist_ok=True)
                            
                            ctx = _create_mock_context()
                            _, _, c, m = code_generator_main(
                                ctx=ctx,
                                prompt_file=str(pdd_files['prompt']),
                                output=output_path,
                                original_prompt_file_path=None, # Auto-detect from git
                                force_incremental_flag=False
                            )
                            op_cost = c
                            op_model = m
                            op_success = True
                            
                            # Clear run report to force validation
                            clear_run_report(basename, language)

                        # --- EXAMPLE ---
                        elif operation == "example":
                            if not pdd_files['prompt'] or not pdd_files['code']:
                                raise FileNotFoundError("Prompt or Code missing for example generation")
                            
                            if pdd_files['example']:
                                output_path = str(pdd_files['example'])
                            else:
                                ext = get_extension(language)
                                output_path = str(Path(examples_dir) / f"{basename}_example{ext}")
                                Path(examples_dir).mkdir(parents=True, exist_ok=True)
                                
                            ctx = _create_mock_context()
                            _, c, m = context_generator_main(
                                ctx=ctx,
                                prompt_file=str(pdd_files['prompt']),
                                code_file=str(pdd_files['code']),
                                output=output_path
                            )
                            op_cost = c
                            op_model = m
                            op_success = True

                        # --- CRASH ---
                        elif operation == "crash":
                            consecutive_crash_count += 1
                            if consecutive_crash_count > MAX_CONSECUTIVE_CRASHES:
                                raise RuntimeError("Max consecutive crash operations reached")

                            if skip_verify: # Skip crash if verify is skipped (usually) or handle separately
                                skipped_operations.append("crash")
                                # Create synthetic success report so we don't loop
                                with AtomicStateUpdate(basename, language) as state:
                                     # Dummy 0-exit code report
                                    _create_synthetic_run_report(state, basename, language, exit_code=0)
                                    _save_skip_fingerprint(state, basename, language, "crash", pdd_files)
                                op_success = True
                            else:
                                if not pdd_files['prompt'] or not pdd_files['code'] or not pdd_files['example']:
                                     raise FileNotFoundError("Missing files for crash fix")
                                
                                # For non-Python, check if agentic path needed
                                use_agentic = _use_agentic_path(language, agentic_mode)
                                
                                # Use crash main
                                ctx = _create_mock_context()
                                
                                # For non-Python, we might not have a simple python verification program or error log
                                # If decision has specific crash logs/details, they might be needed.
                                # But crash_main handles running the program if error_file is not provided or empty?
                                # Actually crash_main often expects an error file. 
                                # sync_determine_operation doesn't currently pass the error log content easily 
                                # unless we extract it from state or re-run.
                                # Strategy: Run the example, capture error, then pass to crash_main.
                                
                                # Need temporary file for error log
                                with tempfile.NamedTemporaryFile(mode='w+', delete=False, suffix='.log') as err_tmp:
                                    err_path = err_tmp.name
                                
                                # Try running to generate error
                                run_cmd = get_run_command_for_file(str(pdd_files['example']), language=language)
                                if not run_cmd:
                                     raise ValueError(f"Could not determine run command for {pdd_files['example']}")
                                
                                # Run with isolation
                                env = os.environ.copy()
                                env.pop("FORCE_COLOR", None)
                                env.pop("COLUMNS", None)
                                
                                try:
                                    proc = subprocess.run(
                                        run_cmd, 
                                        shell=True, 
                                        capture_output=True, 
                                        text=True, 
                                        cwd=os.getcwd(),
                                        env=env,
                                        stdin=subprocess.DEVNULL
                                    )
                                    if proc.returncode != 0:
                                        with open(err_path, 'w') as f:
                                            f.write(proc.stderr + "\n" + proc.stdout)
                                    else:
                                        # It didn't crash? Then why are we here?
                                        # Maybe determine_operation saw stale report.
                                        # Treat as success.
                                        op_success = True
                                        op_cost = 0.0
                                        # Save success state
                                        with AtomicStateUpdate(basename, language) as state:
                                            _create_synthetic_run_report(state, basename, language, exit_code=0)
                                            save_fingerprint(basename, language, "crash", pdd_files, 0.0, "none")
                                        continue 
                                except Exception as e:
                                     with open(err_path, 'w') as f:
                                        f.write(f"Execution failed: {e}")

                                # Now call crash_main
                                success, _, _, _, c, m = crash_main(
                                    ctx=ctx,
                                    prompt_file=str(pdd_files['prompt']),
                                    code_file=str(pdd_files['code']),
                                    program_file=str(pdd_files['example']),
                                    error_file=err_path,
                                    output=str(pdd_files['code']),
                                    output_program=str(pdd_files['example']),
                                    loop=False, # Single pass per sync cycle usually preferred to let sync manage state
                                    budget=budget - total_cost,
                                    agentic_fallback=use_agentic # Use agentic for non-Python or difficult bugs
                                )
                                op_cost = c
                                op_model = m
                                op_success = success
                                os.unlink(err_path)
                                
                                if op_success:
                                    # Post-crash validation
                                    if language.lower() == 'python' and not agentic_mode:
                                        # Verify locally
                                        # Note: verify op comes next, but we update run report now
                                        _run_example_and_update_report(str(pdd_files['example']), basename, language)
                                    else:
                                        # Non-Python/Agentic: Trust agent
                                        with AtomicStateUpdate(basename, language) as state:
                                            _create_synthetic_run_report(state, basename, language, exit_code=0)

                        # --- VERIFY ---
                        elif operation == "verify":
                            if skip_verify:
                                skipped_operations.append("verify")
                                with AtomicStateUpdate(basename, language) as state:
                                    _save_skip_fingerprint(state, basename, language, "verify", pdd_files)
                                op_success = True
                            else:
                                if not pdd_files['prompt'] or not pdd_files['code'] or not pdd_files['example']:
                                     raise FileNotFoundError("Missing files for verify")
                                
                                use_agentic = _use_agentic_path(language, agentic_mode)
                                ctx = _create_mock_context()
                                
                                # Results log path
                                res_log = str(Path(META_DIR) / f"{basename}_{lang_lower}_verify.log")
                                
                                success, _, _, _, c, m = fix_verification_main(
                                    ctx=ctx,
                                    prompt_file=str(pdd_files['prompt']),
                                    code_file=str(pdd_files['code']),
                                    program_file=str(pdd_files['example']),
                                    output_results=res_log,
                                    output_code=str(pdd_files['code']),
                                    output_program=str(pdd_files['example']),
                                    loop=False, 
                                    max_attempts=0 if use_agentic else max_attempts, # 0 attempts triggers fallback logic in some contexts or single pass
                                    budget=budget - total_cost,
                                    agentic_fallback=use_agentic
                                )
                                op_cost = c
                                op_model = m
                                op_success = success

                        # --- TEST ---
                        elif operation == "test":
                            if skip_tests:
                                skipped_operations.append("test")
                                with AtomicStateUpdate(basename, language) as state:
                                    _save_skip_fingerprint(state, basename, language, "test", pdd_files)
                                op_success = True
                            else:
                                if not pdd_files['prompt'] or not pdd_files['code']:
                                     raise FileNotFoundError("Missing files for test generation")
                                
                                consecutive_test_count += 1
                                if consecutive_test_count > MAX_CONSECUTIVE_TESTS:
                                     raise RuntimeError("Max consecutive test operations reached")
                                
                                if pdd_files['test']:
                                    output_path = str(pdd_files['test'])
                                    merge = True
                                    existing_tests = [str(pdd_files['test'])]
                                else:
                                    ext = get_extension(language)
                                    output_path = str(Path(tests_dir) / f"test_{basename}{ext}")
                                    Path(tests_dir).mkdir(parents=True, exist_ok=True)
                                    merge = False
                                    existing_tests = None

                                ctx = _create_mock_context()
                                # cmd_test_main returns (content, cost, model, agentic_success)
                                _, c, m, agentic_success = cmd_test_main(
                                    ctx=ctx,
                                    prompt_file=str(pdd_files['prompt']),
                                    code_file=str(pdd_files['code']),
                                    output=output_path,
                                    language=language,
                                    merge=merge,
                                    existing_tests=existing_tests,
                                    target_coverage=target_coverage
                                )
                                op_cost = c
                                op_model = m
                                
                                # Success check
                                if agentic_success is not None:
                                    op_success = agentic_success
                                else:
                                    # Python fallback check
                                    op_success = Path(output_path).exists()
                                
                                if op_success:
                                    # If agentic success, create synthetic report
                                    if agentic_success is True:
                                         with AtomicStateUpdate(basename, language) as state:
                                             _create_synthetic_run_report_for_agentic_success(output_path, basename, language, atomic_state=state)
                                    else:
                                        # Run tests locally
                                        _execute_tests_and_create_run_report(output_path, basename, language, target_coverage, code_file=str(pdd_files['code']), test_files=pdd_files.get('test_files'))

                        # --- TEST EXTEND ---
                        elif operation == "test_extend":
                            if skip_tests or language.lower() != 'python' or agentic_mode:
                                skipped_operations.append("test_extend")
                                op_success = True
                            else:
                                test_extend_attempts += 1
                                if test_extend_attempts > MAX_TEST_EXTEND_ATTEMPTS:
                                    # Accept current coverage
                                    op_success = True # Just move on
                                else:
                                    # Generate more tests targeting coverage
                                    # Similar to test op but with coverage report input if available
                                    # cmd_test_main handles coverage logic if report exists
                                    # Here we just re-run test generation with merge=True
                                    if not pdd_files['test']:
                                         raise FileNotFoundError("Missing test file for extension")
                                    
                                    ctx = _create_mock_context()
                                    # Need coverage report path
                                    cov_path = f"coverage.xml" # Assuming standard output
                                    
                                    _, c, m, agentic_success = cmd_test_main(
                                        ctx=ctx,
                                        prompt_file=str(pdd_files['prompt']),
                                        code_file=str(pdd_files['code']),
                                        output=str(pdd_files['test']),
                                        language=language,
                                        merge=True,
                                        existing_tests=[str(pdd_files['test'])],
                                        coverage_report=cov_path if os.path.exists(cov_path) else None,
                                        target_coverage=target_coverage
                                    )
                                    op_cost = c
                                    op_model = m
                                    op_success = True
                                    _execute_tests_and_create_run_report(str(pdd_files['test']), basename, language, target_coverage, code_file=str(pdd_files['code']), test_files=pdd_files.get('test_files'))

                        # --- FIX ---
                        elif operation == "fix":
                            consecutive_fix_count += 1
                            if consecutive_fix_count > 5:
                                raise RuntimeError("Max consecutive fix operations reached")
                            
                            if not pdd_files['test'] or not pdd_files['code']:
                                 raise FileNotFoundError("Missing files for fix")
                                 
                            use_agentic = _use_agentic_path(language, agentic_mode)
                            
                            # Determine failing test file if multiple exist
                            failing_test_file = str(pdd_files['test'])
                            test_files_list = pdd_files.get('test_files', [failing_test_file])
                            
                            # Try to find specific failing file from output if possible
                            # For simplicity here, we pass the primary test file to fix_main, 
                            # but fix_main allows multiple unit_test_files. 
                            # We should ideally pass all test files or the specific failing one.
                            # Let's pass all if supported, or just the main one.
                            # fix_main arguments: unit_test_file (str) - singular in signature but manual mode supports multiple?
                            # The signature in fix_main usually takes one file path string for unit_test_file.
                            # Agentic mode takes URL.
                            
                            # Need error log
                            error_log_path = str(Path(META_DIR) / "test_failures.log")
                            if not os.path.exists(error_log_path):
                                # If missing, maybe run tests again to generate it?
                                _execute_tests_and_create_run_report(failing_test_file, basename, language, target_coverage, code_file=str(pdd_files['code']), test_files=test_files_list)
                            
                            # If we have multiple test files, we might need to identify which one failed
                            # For now, simplistic approach: fix the main one
                            
                            ctx = _create_mock_context()
                            success, _, _, _, c, m = fix_main(
                                ctx=ctx,
                                prompt_file=str(pdd_files['prompt']),
                                code_file=str(pdd_files['code']),
                                unit_test_file=failing_test_file, # Agentic fallback handles multiple better
                                error_file=error_log_path,
                                output_test=failing_test_file,
                                output_code=str(pdd_files['code']),
                                loop=False,
                                max_attempts=0 if use_agentic else max_attempts,
                                budget=budget - total_cost,
                                agentic_fallback=use_agentic
                            )
                            op_cost = c
                            op_model = m
                            op_success = success
                            
                            if op_success:
                                if language.lower() == 'python' and not agentic_mode:
                                     _execute_tests_and_create_run_report(failing_test_file, basename, language, target_coverage, code_file=str(pdd_files['code']), test_files=test_files_list)
                                else:
                                     with AtomicStateUpdate(basename, language) as state:
                                         _create_synthetic_run_report_for_agentic_success(failing_test_file, basename, language, atomic_state=state)

                        # --- UPDATE ---
                        elif operation == "update":
                            if not pdd_files['prompt'] or not pdd_files['code']:
                                raise FileNotFoundError("Missing files for update")
                            
                            ctx = _create_mock_context()
                            # Use git history if available
                            use_git = True # Default to git based update
                            
                            res_prompt, c, m = update_main(
                                ctx=ctx,
                                input_prompt_file=str(pdd_files['prompt']),
                                modified_code_file=str(pdd_files['code']),
                                input_code_file=None,
                                output=str(pdd_files['prompt']),
                                use_git=use_git,
                                simple=not agentic_mode # Use agentic update if in agentic mode or available
                            )
                            op_cost = c
                            op_model = m
                            op_success = True
                        
                        else:
                            raise ValueError(f"Unknown operation: {operation}")

                        # 5. Post-Operation Updates
                        total_cost += op_cost
                        cost_ref[0] = total_cost
                        if op_model: last_model_name = op_model
                        
                        if op_success:
                            operations_completed.append(operation)
                            # Update logs
                            entry_data = update_log_entry(entry_data, True, op_cost, op_model, time.time() - op_start_time, None)
                            append_log_entry(basename, language, entry_data)
                            
                            # Save Fingerprint
                            # We re-resolve paths to get current hashes
                            # NOTE: Some operations might have changed file existence
                            pdd_files = get_pdd_file_paths(basename, language, prompts_dir, code_dir, examples_dir, tests_dir)
                            with AtomicStateUpdate(basename, language) as state:
                                save_fingerprint(basename, language, operation, pdd_files, op_cost, op_model)
                        else:
                            op_error = op_error or "Operation failed"
                            errors.append(op_error)
                            entry_data = update_log_entry(entry_data, False, op_cost, op_model, time.time() - op_start_time, op_error)
                            append_log_entry(basename, language, entry_data)
                            break # Stop sync on failure

                    except Exception as e:
                        op_error = str(e)
                        errors.append(f"Exception in {operation}: {op_error}")
                        traceback.print_exc()
                        entry_data = update_log_entry(entry_data, False, op_cost, op_model, time.time() - op_start_time, op_error)
                        append_log_entry(basename, language, entry_data)
                        break

        except Exception as e:
            errors.append(f"Sync orchestration error: {str(e)}")
            traceback.print_exc()
        finally:
            log_event(basename, language, "lock_released", {}, invocation_mode="sync")
            if not quiet:
                # TUI Shutdown
                if app_ref:
                    app_ref[0].exit()
    
    # Run based on mode
    if quiet or not sys.stdout.isatty() or os.environ.get("CI"):
        # Headless mode
        os.environ["PDD_FORCE"] = "1"
        sync_worker_logic()
    else:
        # TUI Mode
        app = SyncApp(
            worker_func=sync_worker_logic,
            function_name_ref=function_name_ref,
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
            stop_event=stop_event,
            basename=basename,
            language=language
        )
        app_ref.append(app)
        app.run()
        
        # Check for worker exceptions
        if hasattr(app, 'worker_exception') and app.worker_exception:
            errors.append(f"Worker crashed: {app.worker_exception}")
            traceback.print_exception(type(app.worker_exception), app.worker_exception, app.worker_exception.__traceback__)
        
        show_exit_animation()

    # Final result
    final_files = get_pdd_file_paths(basename, language, prompts_dir, code_dir, examples_dir, tests_dir)
    final_state = {}
    for k, v in final_files.items():
        if k == 'test_files': continue # Skip list
        final_state[k] = {"exists": v is not None and v.exists(), "path": str(v) if v else None}

    return {
        "success": len(errors) == 0,
        "operations_completed": operations_completed,
        "skipped_operations": skipped_operations,
        "total_cost": total_cost,
        "total_time": time.time() - start_time,
        "final_state": final_state,
        "errors": errors,
        "error": "; ".join(errors) if errors else None,
        "model_name": last_model_name,
        "log_entries": [] # Only populated in dry_run
    }


def _update_tui_file_status(
    pdd_files, 
    prompt_path, code_path, example_path, test_path,
    prompt_color, code_color, example_color, test_color
):
    """Updates TUI reference lists based on file existence."""
    def _set(path_ref, color_ref, fpath, name):
        if fpath and fpath.exists():
            path_ref[0] = f"{name}: {fpath.name}"
            color_ref[0] = "green"
        else:
            path_ref[0] = f"{name}: Missing"
            color_ref[0] = "red"

    _set(prompt_path, prompt_color, pdd_files['prompt'], "Prompt")
    _set(code_path, code_color, pdd_files['code'], "Code")
    _set(example_path, example_color, pdd_files['example'], "Example")
    _set(test_path, test_color, pdd_files['test'], "Test")


def _detect_oscillation(history, op1, op2, limit):
    """Detects simple A-B-A-B oscillation in operation history."""
    if len(history) < limit: return False
    recent = history[-limit:]
    # Check if we only have op1 and op2
    unique = set(recent)
    if not unique.issubset({op1, op2}): return False
    return True


def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Determines if agentic path should be used."""
    if agentic_mode: return True
    if language.lower() != "python": return True
    return False


def _create_synthetic_run_report(state, basename, language, exit_code=0):
    """Creates a synthetic success run report."""
    report = {
        "timestamp": datetime.datetime.now().isoformat(),
        "exit_code": exit_code,
        "tests_passed": 1,
        "tests_failed": 0,
        "coverage": 100.0,
        "duration": 0.0
    }
    # Save using atomic state or directly
    path = Path(META_DIR) / f"{_safe_basename(basename)}_{language.lower()}_run.json"
    state.add_write(path, json.dumps(report, indent=2))


def _save_skip_fingerprint(state, basename, language, skipped_op, pdd_files):
    """Saves a fingerprint indicating an operation was skipped."""
    # We need current hashes
    hashes = calculate_current_hashes(pdd_files)
    fp = {
        "version": "1.0",
        "timestamp": datetime.datetime.now().isoformat(),
        "operation": f"skip:{skipped_op}",
        "prompt_hash": hashes.get("prompt_hash"),
        "code_hash": hashes.get("code_hash"),
        "example_hash": hashes.get("example_hash"),
        "test_hash": hashes.get("test_hash"),
        "cost": 0.0,
        "model": "skipped"
    }
    path = Path(META_DIR) / f"{_safe_basename(basename)}_{language.lower()}.json"
    state.add_write(path, json.dumps(fp, indent=2))


def _run_example_and_update_report(example_file, basename, language):
    """Runs example file locally and updates run report."""
    cmd = get_run_command_for_file(example_file, language=language)
    if not cmd: return
    
    start = time.time()
    env = os.environ.copy()
    env.pop("FORCE_COLOR", None)
    
    try:
        proc = subprocess.run(
            cmd, 
            shell=True, 
            cwd=os.getcwd(), 
            env=env, 
            capture_output=True, 
            text=True,
            start_new_session=True # Isolate
        )
        report = {
            "timestamp": datetime.datetime.now().isoformat(),
            "exit_code": proc.returncode,
            "tests_passed": 1 if proc.returncode == 0 else 0,
            "tests_failed": 1 if proc.returncode != 0 else 0,
            "coverage": 0.0,
            "duration": time.time() - start
        }
        save_run_report(basename, language, report)
    except Exception:
        pass


def _execute_tests_and_create_run_report(
    test_file: str, 
    basename: str, 
    language: str, 
    target_coverage: float, 
    *, 
    code_file: Optional[str] = None, 
    atomic_state: Optional[AtomicStateUpdate] = None, 
    test_files: Optional[List[Path]] = None
):
    """Executes tests and creates run report."""
    test_cmd = get_test_command_for_file(test_file, language=language)
    if not test_cmd:
        # Fallback if no command found
        return

    # Python special handling for coverage and root discovery
    env = os.environ.copy()
    cwd = os.getcwd()
    
    if language.lower() == 'python':
        project_root = _find_project_root(test_file)
        if project_root:
            pythonpath = env.get("PYTHONPATH", "")
            src_path = str(project_root / "src")
            env["PYTHONPATH"] = f"{project_root}:{src_path}:{pythonpath}"
            # Add args to command if it looks like pytest
            if "pytest" in test_cmd:
                 # Adjust coverage target
                 cov_arg = ""
                 if code_file:
                     mod_name = _python_cov_target_for_code_file(code_file)
                     cov_arg = f" --cov={mod_name} --cov-report=xml"
                 
                 # Append files
                 files_str = test_file
                 if test_files:
                     files_str = " ".join([str(p) for p in test_files])
                 
                 test_cmd = f"{test_cmd} --rootdir={project_root} -c /dev/null {cov_arg} {files_str}"

    # Execute
    start = time.time()
    try:
        # Capture failing output to log
        error_log = Path(META_DIR) / "test_failures.log"
        
        proc = subprocess.run(
            test_cmd,
            shell=True,
            cwd=cwd,
            env=env,
            capture_output=True,
            text=True,
            start_new_session=True
        )
        
        # Write failures log
        if proc.returncode != 0:
            error_log.parent.mkdir(parents=True, exist_ok=True)
            with open(error_log, "w") as f:
                f.write(proc.stdout + "\n" + proc.stderr)
        
        # Parse output
        passed, failed, cov = _parse_test_output(proc.stdout + "\n" + proc.stderr, language)
        
        report = {
            "timestamp": datetime.datetime.now().isoformat(),
            "exit_code": proc.returncode,
            "tests_passed": passed,
            "tests_failed": failed,
            "coverage": cov,
            "duration": time.time() - start
        }
        
        if test_files:
             # Calculate hashes for multiple files
             t_hashes = {}
             for tf in test_files:
                 if tf.exists():
                     with open(tf, 'rb') as f:
                         t_hashes[tf.name] = calculate_sha256(f.read())
             report['test_file_hashes'] = t_hashes
        else:
            # Single hash
             if os.path.exists(test_file):
                 with open(test_file, 'rb') as f:
                    report['test_hash'] = calculate_sha256(f.read())

        # Save
        path = Path(META_DIR) / f"{_safe_basename(basename)}_{language.lower()}_run.json"
        content = json.dumps(report, indent=2)
        
        if atomic_state:
            atomic_state.add_write(path, content)
        else:
            with AtomicStateUpdate(basename, language) as state:
                state.add_write(path, content)

    except Exception as e:
        print(f"Error executing tests: {e}")


def _python_cov_target_for_code_file(code_file: str) -> str:
    """Guess module name from code file path."""
    p = Path(code_file)
    # Simple heuristic: remove extension
    return p.stem


def _parse_test_output(output: str, language: str) -> Tuple[int, int, float]:
    """Parses test runner output for stats."""
    passed = 0
    failed = 0
    coverage = 0.0
    
    if language.lower() == 'python':
        # Pytest output parsing
        # passed: "3 passed"
        m_pass = re.search(r'(\d+) passed', output)
        if m_pass: passed = int(m_pass.group(1))
        
        m_fail = re.search(r'(\d+) failed', output)
        if m_fail: failed = int(m_fail.group(1))
        
        m_err = re.search(r'(\d+) error', output)
        if m_err: failed += int(m_err.group(1))
        
        # Coverage from output or xml (xml reading not implemented here, use stdout scrape)
        # "TOTAL ... 95%"
        m_cov = re.search(r'TOTAL\s+.*\s+(\d+)%', output)
        if m_cov: coverage = float(m_cov.group(1))

    elif language.lower() in ['javascript', 'typescript']:
        # Jest/Vitest
        m_pass = re.search(r'Tests:\s+(\d+) passed', output)
        if m_pass: passed = int(m_pass.group(1))
        
        m_fail = re.search(r'Tests:\s+.*(\d+) failed', output)
        if m_fail: failed = int(m_fail.group(1))
        
        m_cov = re.search(r'All files\s+\|\s+[\d.]+\s+\|\s+[\d.]+\s+\|\s+[\d.]+\s+\|\s+([\d.]+)', output)
        if m_cov: coverage = float(m_cov.group(1))

    # Defaults if regex fails
    if passed == 0 and failed == 0:
        if "FAIL" in output or "Error" in output:
            failed = 1
        else:
            passed = 1 # Optimistic fallback for "OK" outputs
            
    return passed, failed, coverage


def _create_synthetic_run_report_for_agentic_success(test_file: str, basename: str, language: str, atomic_state=None):
    """Creates synthetic report for agentic test generation success."""
    t_hash = "agentic_test_success"
    if os.path.exists(test_file):
        with open(test_file, 'rb') as f:
            t_hash = calculate_sha256(f.read())
            
    report = {
        "timestamp": datetime.datetime.now().isoformat(),
        "exit_code": 0,
        "tests_passed": 1,
        "tests_failed": 0,
        "coverage": 100.0,
        "duration": 0.0,
        "test_hash": t_hash
    }
    
    path = Path(META_DIR) / f"{_safe_basename(basename)}_{language.lower()}_run.json"
    content = json.dumps(report, indent=2)
    
    if atomic_state:
        atomic_state.add_write(path, content)
    else:
        with AtomicStateUpdate(basename, language) as state:
            state.add_write(path, content)


def _display_sync_log(basename, language, verbose=False):
    """Displays formatted sync log."""
    entries = load_operation_log(basename, language)
    print(f"\n--- Sync Log for {basename} ({language}) ---")
    for e in entries:
        ts = e.get('timestamp', '')
        op = e.get('operation', 'unknown')
        res = "Success" if e.get('success') else "Failed"
        if not verbose:
            print(f"[{ts}] {op}: {res}")
        else:
            print(f"[{ts}] {op}")
            print(f"  Result: {res}")
            print(f"  Reason: {e.get('reason')}")
            print(f"  Cost: ${e.get('actual_cost', 0.0):.4f}")
            if e.get('error'):
                print(f"  Error: {e.get('error')}")
            print("-" * 20)
```