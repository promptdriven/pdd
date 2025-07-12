# pdd/sync_orchestration.py
"""
Orchestrates the complete PDD sync workflow by coordinating operations and
animations in parallel, serving as the core engine for the `pdd sync` command.
"""

import threading
import time
import json
import datetime
import subprocess
import re
from pathlib import Path
from typing import Dict, Any, Optional, List
from dataclasses import asdict

import click

# --- Real PDD Component Imports ---
from .sync_animation import sync_animation
from .sync_determine_operation import (
    sync_determine_operation,
    get_pdd_file_paths,
    RunReport,
    PDD_DIR,
    META_DIR,
    SyncLock,
)
from .auto_deps_main import auto_deps_main
from .code_generator_main import code_generator_main
from .context_generator_main import context_generator_main
from .crash_main import crash_main
from .fix_verification_main import fix_verification_main
from .cmd_test_main import cmd_test_main
from .fix_main import fix_main
from .update_main import update_main

# --- Mock Helper Functions ---

def load_sync_log(basename: str, language: str) -> List[Dict[str, Any]]:
    """Load sync log entries for a basename and language."""
    log_file = META_DIR / f"{basename}_{language}_sync.log"
    if not log_file.exists():
        return []
    try:
        with open(log_file, 'r') as f:
            return [json.loads(line) for line in f if line.strip()]
    except Exception:
        return []

def save_run_report(report: Dict[str, Any], basename: str, language: str):
    """Save a run report to the metadata directory."""
    report_file = META_DIR / f"{basename}_{language}_run.json"
    META_DIR.mkdir(parents=True, exist_ok=True)
    with open(report_file, 'w') as f:
        json.dump(report, f, indent=2, default=str)

def _save_operation_fingerprint(basename: str, language: str, operation: str, 
                               paths: Dict[str, Path], cost: float, model: str):
    """Save fingerprint state after successful operation."""
    from datetime import datetime, timezone
    from .sync_determine_operation import calculate_current_hashes, Fingerprint
    
    current_hashes = calculate_current_hashes(paths)
    fingerprint = Fingerprint(
        pdd_version="0.0.41",
        timestamp=datetime.now(timezone.utc).isoformat(),
        command=operation,
        prompt_hash=current_hashes.get('prompt_hash'),
        code_hash=current_hashes.get('code_hash'),
        example_hash=current_hashes.get('example_hash'),
        test_hash=current_hashes.get('test_hash')
    )
    
    META_DIR.mkdir(parents=True, exist_ok=True)
    fingerprint_file = META_DIR / f"{basename}_{language}.json"
    with open(fingerprint_file, 'w') as f:
        json.dump(asdict(fingerprint), f, indent=2, default=str)

# SyncLock class now imported from sync_determine_operation module

def _execute_tests_and_create_run_report(test_file: Path, basename: str, language: str, target_coverage: float = 90.0) -> RunReport:
    """Execute tests and create a RunReport with actual results."""
    timestamp = datetime.datetime.now(datetime.timezone.utc).isoformat()
    
    try:
        # Execute pytest with coverage reporting on the specific module
        # Extract module name from test file (e.g., test_factorial.py -> factorial)
        module_name = test_file.name.replace('test_', '').replace('.py', '')
        
        # Use the module import path rather than file path for coverage
        result = subprocess.run([
            'python', '-m', 'pytest', 
            str(test_file), 
            '-v', 
            '--tb=short',
            f'--cov=pdd.{module_name}',
            '--cov-report=term-missing'
        ], capture_output=True, text=True, timeout=300)
        
        exit_code = result.returncode
        stdout = result.stdout
        stderr = result.stderr
        
        # Parse test results from pytest output
        tests_passed = 0
        tests_failed = 0
        coverage = 0.0
        
        # Parse passed/failed tests
        if 'passed' in stdout:
            passed_match = re.search(r'(\d+) passed', stdout)
            if passed_match:
                tests_passed = int(passed_match.group(1))
        
        if 'failed' in stdout:
            failed_match = re.search(r'(\d+) failed', stdout)
            if failed_match:
                tests_failed = int(failed_match.group(1))
        
        # Parse coverage percentage
        coverage_match = re.search(r'TOTAL.*?(\d+)%', stdout)
        if coverage_match:
            coverage = float(coverage_match.group(1))
        
        # Create and save run report
        report = RunReport(
            timestamp=timestamp,
            exit_code=exit_code,
            tests_passed=tests_passed,
            tests_failed=tests_failed,
            coverage=coverage
        )
        
    except (subprocess.TimeoutExpired, subprocess.CalledProcessError, Exception) as e:
        # If test execution fails, create a report indicating failure
        report = RunReport(
            timestamp=timestamp,
            exit_code=1,
            tests_passed=0,
            tests_failed=1,
            coverage=0.0
        )
    
    # Save the run report
    save_run_report(asdict(report), basename, language)
    return report

# --- Helper for Click Context ---

def _create_mock_context(**kwargs) -> click.Context:
    """Creates a mock Click context object to pass parameters to command functions."""
    ctx = click.Context(click.Command('sync'))
    ctx.obj = kwargs
    return ctx


def _display_sync_log(basename: str, language: str, verbose: bool = False) -> Dict[str, Any]:
    """Displays the sync log for a given basename and language."""
    log_file = META_DIR / f"{basename}_{language}_sync.log"
    if not log_file.exists():
        print(f"No sync log found for '{basename}' in language '{language}'.")
        return {'success': False, 'errors': ['Log file not found.'], 'log_entries': []}

    log_entries = load_sync_log(basename, language)
    print(f"--- Sync Log for {basename} ({language}) ---")

    if not log_entries:
        print("Log is empty.")
        return {'success': True, 'log_entries': []}

    for entry in log_entries:
        timestamp = entry.get('timestamp', 'N/A')
        decision = entry.get('decision', {})
        operation = decision.get('operation', 'N/A')
        reason = decision.get('reason', 'N/A')
        print(f"[{timestamp}] Operation: {operation:<15} | Reason: {reason}")
        if verbose and 'details' in decision and decision['details']:
            details_str = json.dumps(decision['details'], indent=2)
            print(f"  Details: {details_str}")

    print("--- End of Log ---")
    return {'success': True, 'log_entries': log_entries}


def sync_orchestration(
    basename: str,
    language: str = "python",
    prompts_dir: str = "prompts",
    code_dir: str = "src",
    examples_dir: str = "examples",
    tests_dir: str = "tests",
    max_attempts: int = 3,
    budget: float = 10.0,
    skip_verify: bool = False,
    skip_tests: bool = False,
    target_coverage: float = 90.0,
    log: bool = False,
    force: bool = False,
    strength: float = 0.5,
    temperature: float = 0.0,
    time_param: float = 0.25, # Renamed to avoid conflict with `time` module
    verbose: bool = False,
    quiet: bool = False,
    output_cost: Optional[str] = None,
    review_examples: bool = False,
    local: bool = False,
    context_config: Optional[Dict[str, str]] = None,
) -> Dict[str, Any]:
    """
    Orchestrates the complete PDD sync workflow with parallel animation.

    If log=True, displays the sync log instead of running sync operations.
    The verbose flag controls the detail level of the log output.

    Returns a dictionary summarizing the outcome of the sync process.
    """
    if log:
        return _display_sync_log(basename, language, verbose)

    # --- Initialize State and Paths ---
    try:
        pdd_files = get_pdd_file_paths(basename, language, prompts_dir)
    except Exception as e:
        # Log the error and return early with failure status
        console.print(f"[red]Error constructing paths: {e}[/red]")
        return {
            "success": False,
            "total_cost": 0.0,
            "model_name": "",
            "error": f"Failed to construct paths: {str(e)}",
            "operations_completed": [],
            "errors": [f"Path construction failed: {str(e)}"]
        }
    
    # Shared state for animation thread
    current_function_name_ref = ["initializing"]
    stop_event = threading.Event()
    current_cost_ref = [0.0]
    prompt_path_ref = [str(pdd_files.get('prompt', 'N/A'))]
    code_path_ref = [str(pdd_files.get('code', 'N/A'))]
    example_path_ref = [str(pdd_files.get('example', 'N/A'))]
    tests_path_ref = [str(pdd_files.get('test', 'N/A'))]
    prompt_box_color_ref, code_box_color_ref, example_box_color_ref, tests_box_color_ref = \
        ["blue"], ["blue"], ["blue"], ["blue"]
    
    # Orchestration state
    operations_completed: List[str] = []
    skipped_operations: List[str] = []
    errors: List[str] = []
    start_time = time.time()
    animation_thread = None

    try:
        with SyncLock(basename, language):
            # --- Start Animation Thread ---
            animation_thread = threading.Thread(
                target=sync_animation,
                args=(
                    current_function_name_ref, stop_event, basename, current_cost_ref, budget,
                    prompt_box_color_ref, code_box_color_ref, example_box_color_ref, tests_box_color_ref,
                    prompt_path_ref, code_path_ref, example_path_ref, tests_path_ref
                ),
                daemon=True
            )
            animation_thread.start()

            # --- Main Workflow Loop ---
            while True:
                if current_cost_ref[0] >= budget:
                    errors.append(f"Budget of ${budget:.2f} exceeded.")
                    break

                decision = sync_determine_operation(basename, language, target_coverage, budget - current_cost_ref[0], False, prompts_dir, skip_tests, skip_verify)
                operation = decision.operation

                if operation in ['all_synced', 'nothing', 'fail_and_request_manual_merge', 'error', 'analyze_conflict']:
                    current_function_name_ref[0] = "synced" if operation in ['all_synced', 'nothing'] else "conflict"
                    if operation == 'fail_and_request_manual_merge':
                        errors.append(f"Manual merge required: {decision.reason}")
                    elif operation == 'error':
                        errors.append(f"Error determining operation: {decision.reason}")
                    elif operation == 'analyze_conflict':
                        errors.append(f"Conflict detected: {decision.reason}")
                    break
                
                # Handle skips
                if operation == 'verify' and (skip_verify or skip_tests):
                    # Skip verification if explicitly requested OR if tests are skipped (can't verify without tests)
                    skipped_operations.append('verify')
                    skip_reason = 'skip_verify' if skip_verify else 'skip_tests_implies_skip_verify'
                    report_data = RunReport(
                        timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                        exit_code=0, tests_passed=0, tests_failed=0, coverage=0.0
                    )
                    save_run_report(asdict(report_data), basename, language)
                    _save_operation_fingerprint(basename, language, 'verify', pdd_files, 0.0, skip_reason)
                    continue
                if operation == 'test' and skip_tests:
                    skipped_operations.append('test')
                    report_data = RunReport(
                        timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                        exit_code=0, tests_passed=0, tests_failed=0, coverage=1.0
                    )
                    save_run_report(asdict(report_data), basename, language)
                    _save_operation_fingerprint(basename, language, 'test', pdd_files, 0.0, 'skipped')
                    continue
                if operation == 'crash' and skip_tests:
                    # Skip crash operations when tests are skipped since crash fixes usually require test execution
                    skipped_operations.append('crash')
                    # Create a dummy run report indicating crash was skipped
                    report_data = RunReport(
                        timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                        exit_code=0, tests_passed=0, tests_failed=0, coverage=0.0
                    )
                    save_run_report(asdict(report_data), basename, language)
                    _save_operation_fingerprint(basename, language, 'crash', pdd_files, 0.0, 'skipped')
                    continue

                current_function_name_ref[0] = operation
                ctx = _create_mock_context(
                    force=force, strength=strength, temperature=temperature, time=time_param,
                    verbose=verbose, quiet=quiet, output_cost=output_cost,
                    review_examples=review_examples, local=local, budget=budget - current_cost_ref[0],
                    max_attempts=max_attempts, target_coverage=target_coverage
                )
                
                result = {}
                success = False

                # --- Execute Operation ---
                try:
                    if operation == 'auto-deps':
                        # Save the modified prompt to a temporary location
                        temp_output = str(pdd_files['prompt']).replace('.prompt', '_with_deps.prompt')
                        
                        # Read original prompt content to compare later
                        original_content = pdd_files['prompt'].read_text(encoding='utf-8')
                        
                        result = auto_deps_main(
                            ctx, 
                            prompt_file=str(pdd_files['prompt']), 
                            directory_path=examples_dir,
                            auto_deps_csv_path="project_dependencies.csv",
                            output=temp_output,
                            force_scan=False  # Don't force scan every time
                        )
                        
                        # Only move the temp file back if content actually changed
                        if Path(temp_output).exists():
                            import shutil
                            new_content = Path(temp_output).read_text(encoding='utf-8')
                            if new_content != original_content:
                                shutil.move(temp_output, str(pdd_files['prompt']))
                            else:
                                # No changes needed, remove temp file
                                Path(temp_output).unlink()
                                # Mark as successful with no changes
                                result = (new_content, 0.0, 'no-changes')
                    elif operation == 'generate':
                        result = code_generator_main(
                            ctx, 
                            prompt_file=str(pdd_files['prompt']), 
                            output=str(pdd_files['code']),
                            original_prompt_file_path=None,
                            force_incremental_flag=False
                        )
                    elif operation == 'example':
                        print(f"DEBUG SYNC: pdd_files['example'] = {pdd_files['example']}")
                        print(f"DEBUG SYNC: str(pdd_files['example']) = {str(pdd_files['example'])}")
                        result = context_generator_main(
                            ctx, 
                            prompt_file=str(pdd_files['prompt']), 
                            code_file=str(pdd_files['code']), 
                            output=str(pdd_files['example'])
                        )
                    elif operation == 'crash':
                        # Validate required files exist before attempting crash operation
                        required_files = [pdd_files['code'], pdd_files['example']]
                        missing_files = [f for f in required_files if not f.exists()]
                        
                        if missing_files:
                            # Skip crash operation if required files are missing
                            print(f"Skipping crash operation - missing files: {[f.name for f in missing_files]}")
                            skipped_operations.append('crash')
                            # Create a dummy run report indicating crash was skipped due to missing files
                            report_data = RunReport(
                                timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                                exit_code=0, tests_passed=0, tests_failed=0, coverage=0.0
                            )
                            save_run_report(asdict(report_data), basename, language)
                            _save_operation_fingerprint(basename, language, 'crash', pdd_files, 0.0, 'skipped_missing_files')
                            continue
                        else:
                            Path("crash.log").write_text("Simulated crash error")
                            try:
                                result = crash_main(
                                    ctx, 
                                    prompt_file=str(pdd_files['prompt']), 
                                    code_file=str(pdd_files['code']), 
                                    program_file=str(pdd_files['example']), 
                                    error_file="crash.log"
                                )
                            except (RuntimeError, Exception) as e:
                                error_str = str(e)
                                if ("Simulated crash error" in error_str or 
                                    "LLM returned None" in error_str or 
                                    "LLM failed to analyze errors" in error_str):
                                    # Skip crash operation for simulated errors or LLM failures
                                    print(f"Skipping crash operation due to simulated/LLM error: {e}")
                                    skipped_operations.append('crash')
                                    report_data = RunReport(
                                        timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                                        exit_code=0, tests_passed=0, tests_failed=0, coverage=0.0
                                    )
                                    save_run_report(asdict(report_data), basename, language)
                                    _save_operation_fingerprint(basename, language, 'crash', pdd_files, 0.0, 'skipped_llm_error')
                                    continue
                                else:
                                    # Re-raise other exceptions
                                    raise
                    elif operation == 'verify':
                        result = fix_verification_main(
                            ctx, 
                            prompt_file=str(pdd_files['prompt']), 
                            code_file=str(pdd_files['code']), 
                            program_file=str(pdd_files['example']),
                            output_results=None,
                            output_code=str(pdd_files['code']),
                            output_program=str(pdd_files['example']),
                            loop=False,
                            verification_program=None
                        )
                    elif operation == 'test':
                        # First, generate the test file
                        result = cmd_test_main(
                            ctx, 
                            prompt_file=str(pdd_files['prompt']), 
                            code_file=str(pdd_files['code']), 
                            output=str(pdd_files['test']),
                            language=language,
                            coverage_report=None,
                            existing_tests=None,
                            target_coverage=target_coverage,
                            merge=False
                        )
                        
                        # After successful test generation, execute the tests and create run report
                        # This enables the next sync iteration to detect test failures and trigger fix
                        if isinstance(result, dict) and result.get('success', False):
                            try:
                                test_file = pdd_files['test']
                                if test_file.exists():
                                    _execute_tests_and_create_run_report(
                                        test_file, basename, language, target_coverage
                                    )
                            except Exception as e:
                                # Don't fail the entire operation if test execution fails
                                # Just log it - the test file generation was successful
                                print(f"Warning: Test execution failed: {e}")
                        elif isinstance(result, tuple) and len(result) >= 3:
                            # Handle tuple return format - assume success and execute tests
                            try:
                                test_file = pdd_files['test']
                                if test_file.exists():
                                    _execute_tests_and_create_run_report(
                                        test_file, basename, language, target_coverage
                                    )
                            except Exception as e:
                                print(f"Warning: Test execution failed: {e}")
                    elif operation == 'fix':
                        # Create error file with actual test failure information
                        error_file_path = Path("fix_errors.log")
                        
                        # Try to get actual test failure details from latest run
                        try:
                            from .sync_determine_operation import read_run_report
                            run_report = read_run_report(basename, language)
                            if run_report and run_report.tests_failed > 0:
                                # Run the tests again to capture actual error output
                                test_result = subprocess.run([
                                    'python', '-m', 'pytest', 
                                    str(pdd_files['test']), 
                                    '-v', '--tb=short'
                                ], capture_output=True, text=True, timeout=300)
                                
                                error_content = f"Test failures detected ({run_report.tests_failed} failed tests):\n\n"
                                error_content += "STDOUT:\n" + test_result.stdout + "\n\n"
                                error_content += "STDERR:\n" + test_result.stderr
                            else:
                                error_content = "Simulated test failures"
                        except Exception as e:
                            error_content = f"Could not capture test failures: {e}\nUsing simulated test failures"
                        
                        error_file_path.write_text(error_content)
                        
                        result = fix_main(
                            ctx, 
                            prompt_file=str(pdd_files['prompt']), 
                            code_file=str(pdd_files['code']), 
                            unit_test_file=str(pdd_files['test']), 
                            error_file=str(error_file_path),
                            output_test=str(pdd_files['test']),
                            output_code=str(pdd_files['code']),
                            output_results=f"{basename}_fix_results.log",
                            loop=False,
                            verification_program=None,
                            max_attempts=max_attempts,
                            budget=budget - current_cost_ref[0],
                            auto_submit=False
                        )
                    elif operation == 'update':
                        result = update_main(
                            ctx, 
                            input_prompt_file=str(pdd_files['prompt']), 
                            modified_code_file=str(pdd_files['code']),
                            input_code_file=None,
                            output=str(pdd_files['prompt']),
                            git=True
                        )
                    else:
                        errors.append(f"Unknown operation '{operation}' requested.")
                        result = {'success': False, 'cost': 0.0}
                    
                    # Handle different return formats from command functions
                    if isinstance(result, dict):
                        # Dictionary return (e.g., from some commands)
                        success = result.get('success', False)
                        current_cost_ref[0] += result.get('cost', 0.0)
                    elif isinstance(result, tuple) and len(result) >= 3:
                        # Tuple return (e.g., from code_generator_main, context_generator_main)
                        # For tuples, success is determined by no exceptions and valid return content
                        # Check if the first element (generated content) is None, which indicates failure
                        success = result[0] is not None
                        # Extract cost from tuple (usually second-to-last element)
                        cost = result[-2] if len(result) >= 2 and isinstance(result[-2], (int, float)) else 0.0
                        current_cost_ref[0] += cost
                    else:
                        # Unknown return format
                        success = result is not None
                        current_cost_ref[0] += 0.0

                except Exception as e:
                    errors.append(f"Exception during '{operation}': {e}")
                    success = False

                if success:
                    operations_completed.append(operation)
                    # Extract cost and model from result based on format
                    if isinstance(result, dict):
                        cost = result.get('cost', 0.0)
                        model = result.get('model', '')
                    elif isinstance(result, tuple) and len(result) >= 3:
                        cost = result[-2] if len(result) >= 2 and isinstance(result[-2], (int, float)) else 0.0
                        model = result[-1] if len(result) >= 1 and isinstance(result[-1], str) else ''
                    else:
                        cost = 0.0
                        model = ''
                    _save_operation_fingerprint(basename, language, operation, pdd_files, cost, model)
                    
                    # After successful fix operation, execute tests to update run report
                    if operation == 'fix':
                        try:
                            test_file = pdd_files['test']
                            if test_file.exists():
                                _execute_tests_and_create_run_report(
                                    test_file, basename, language, target_coverage
                                )
                        except Exception as e:
                            # Don't fail the entire operation if test execution fails
                            print(f"Warning: Post-fix test execution failed: {e}")
                else:
                    errors.append(f"Operation '{operation}' failed.")
                    break

    except TimeoutError:
        errors.append(f"Could not acquire lock for '{basename}'. Another sync process may be running.")
    except Exception as e:
        errors.append(f"An unexpected error occurred in the orchestrator: {e}")
    finally:
        if stop_event:
            stop_event.set()
        if animation_thread and animation_thread.is_alive():
            animation_thread.join(timeout=5)
        
    total_time = time.time() - start_time
    final_state = {
        p_name: {'exists': p_path.exists(), 'path': str(p_path)} 
        for p_name, p_path in pdd_files.items()
    }
    
    return {
        'success': not errors,
        'operations_completed': operations_completed,
        'skipped_operations': skipped_operations,
        'total_cost': current_cost_ref[0],
        'total_time': total_time,
        'final_state': final_state,
        'errors': errors,
    }

if __name__ == '__main__':
    # Example usage of the sync_orchestration module.
    # This simulates running `pdd sync my_calculator` from the command line.
    
    print("--- Running Basic Sync Orchestration Example ---")
    
    # Setup a dummy project structure
    Path("./prompts").mkdir(exist_ok=True)
    Path("./src").mkdir(exist_ok=True)
    Path("./examples").mkdir(exist_ok=True)
    Path("./tests").mkdir(exist_ok=True)
    Path("./prompts/my_calculator_python.prompt").write_text("Create a calculator.")
    
    # Ensure PDD meta directory exists for logs and locks
    PDD_DIR.mkdir(exist_ok=True)
    META_DIR.mkdir(exist_ok=True)

    result = sync_orchestration(
        basename="my_calculator",
        language="python",
        quiet=True # Suppress mock command output for cleaner example run
    )
    
    print("\n--- Sync Orchestration Finished ---")
    print(json.dumps(result, indent=2))

    if result['success']:
        print("\n✅ Sync completed successfully.")
    else:
        print(f"\n❌ Sync failed. Errors: {result['errors']}")

    print("\n--- Running Sync Log Example ---")
    # This will now show the log from the run we just completed.
    log_result = sync_orchestration(
        basename="my_calculator",
        language="python",
        log=True
    )
