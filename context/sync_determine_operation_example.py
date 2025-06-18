import os
import shutil
import json
import datetime
from pathlib import Path
import time # For SyncLock demonstration

# Assume the provided module is saved as 'pdd_sync_logic.py'
# in a directory 'pdd' which is part of PYTHONPATH.
# e.g., your project structure might be:
# your_project/
#   pdd/
#     __init__.py
#     pdd_sync_logic.py
#     load_prompt_template.py (placeholder or actual)
#     llm_invoke.py (placeholder or actual)
#   examples/
#     run_sync_logic_example.py (this file)
#
# To run this example, ensure 'your_project' directory is in PYTHONPATH,
# or run from 'your_project' directory.

from pdd.pdd_sync_logic import (
    determine_sync_operation,
    analyze_conflict_with_llm,
    Fingerprint,
    RunReport,
    SyncLock,
    SyncDecision, # For type hinting
    asdict,
    calculate_sha256,
    get_pdd_file_paths,
    # Constants from the module that define directory structure
    PDD_DIR,
    META_DIR,
    LOCKS_DIR,
    PROMPTS_ROOT_DIR,
    CODE_ROOT_DIR, # Usually Path(".")
    EXAMPLES_ROOT_DIR,
    TESTS_ROOT_DIR
)

# --- Configuration for the example ---
# All example operations will occur within this directory
EXAMPLE_ROOT_DIR = Path("./example_pdd_project_root")

TEST_BASENAME = "greeter"
TEST_LANGUAGE = "python"
TEST_TARGET_COVERAGE = 0.85

# Store original CWD to restore it later
ORIGINAL_CWD = Path.cwd()

# --- Helper functions for the example ---

def setup_example_environment():
    """
    Creates the necessary directory structure for the example relative to EXAMPLE_ROOT_DIR
    and changes the current working directory to EXAMPLE_ROOT_DIR.
    The module's functions use relative paths, so CWD needs to be the project root.
    """
    if EXAMPLE_ROOT_DIR.exists():
        shutil.rmtree(EXAMPLE_ROOT_DIR)
    EXAMPLE_ROOT_DIR.mkdir(parents=True, exist_ok=True)
    
    os.chdir(EXAMPLE_ROOT_DIR)

    # Create directories expected by the module for PDD files
    # The module's _ensure_pdd_dirs_exist() will create .pdd/*,
    # but we need to create roots for prompts, code, examples, tests.
    PROMPTS_ROOT_DIR.mkdir(parents=True, exist_ok=True)
    # CODE_ROOT_DIR is usually ".", so no need to create it explicitly.
    EXAMPLES_ROOT_DIR.mkdir(parents=True, exist_ok=True)
    TESTS_ROOT_DIR.mkdir(parents=True, exist_ok=True)
    
    print(f"Set up example environment in: {EXAMPLE_ROOT_DIR.resolve()}")
    print(f"Current working directory: {Path.cwd()}")

def cleanup_example_environment():
    """
    Changes CWD back to the original and removes the example directory.
    """
    os.chdir(ORIGINAL_CWD)
    if EXAMPLE_ROOT_DIR.exists():
        shutil.rmtree(EXAMPLE_ROOT_DIR)
    print(f"\nCleaned up example environment. Restored CWD to: {ORIGINAL_CWD}")

def _create_dummy_file(file_path: Path, content: str = ""):
    """Creates a dummy file with given content, ensuring parent directories exist."""
    file_path.parent.mkdir(parents=True, exist_ok=True)
    file_path.write_text(content)
    print(f"  Created/updated file: {file_path}")
    return file_path

def _write_json_dataclass(file_path: Path, data_obj: any):
    """Writes a dataclass object to a JSON file."""
    file_path.parent.mkdir(parents=True, exist_ok=True)
    with open(file_path, 'w') as f:
        json.dump(asdict(data_obj), f, indent=2)
    print(f"  Created JSON file: {file_path}")

def _delete_file(file_path: Path):
    """Deletes a file if it exists."""
    if file_path.exists():
        file_path.unlink()
        print(f"  Deleted file: {file_path}")

def print_decision(decision: SyncDecision):
    """Prints the SyncDecision in a readable format."""
    print(f"  Decision Operation: {decision.operation}")
    print(f"  Reason: {decision.reason}")
    if decision.details:
        print(f"  Details: {decision.details}")

# --- Main example function ---
def run_pdd_sync_logic_example():
    """
    Demonstrates various scenarios using the pdd_sync_logic module.
    """
    print(f"\n--- Running PDD Sync Logic Example for unit: {TEST_BASENAME} ({TEST_LANGUAGE}) ---")

    pdd_files = get_pdd_file_paths(TEST_BASENAME, TEST_LANGUAGE)
    fingerprint_file_path = META_DIR / f"{TEST_BASENAME}_{TEST_LANGUAGE}.json"
    run_report_file_path = META_DIR / f"{TEST_BASENAME}_{TEST_LANGUAGE}_run.json"

    # --- Scenario 1: New unit, only prompt file exists, no fingerprint ---
    print("\nScenario 1: New unit - Prompt exists, no fingerprint")
    _create_dummy_file(pdd_files['prompt'], f"# Prompt for {TEST_BASENAME}")
    # Ensure other files and fingerprint don't exist from previous runs within this example
    _delete_file(pdd_files['code'])
    _delete_file(pdd_files['example'])
    _delete_file(pdd_files['test'])
    _delete_file(fingerprint_file_path)
    _delete_file(run_report_file_path)


    decision = determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    print_decision(decision)
    assert decision.operation == 'generate'

    # --- Scenario 2: Prompt changed after initial generation (fingerprint exists) ---
    print("\nScenario 2: Prompt changed - Fingerprint exists")
    # Create a dummy fingerprint as if 'generate' was run
    prompt_hash_s1 = calculate_sha256(pdd_files['prompt'])
    fp_s1 = Fingerprint(
        pdd_version="0.1.0",
        timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        command="generate",
        prompt_hash=prompt_hash_s1,
        code_hash="dummy_code_hash_s1", # Assume code was generated
        example_hash=None,
        test_hash=None
    )
    _write_json_dataclass(fingerprint_file_path, fp_s1)
    _create_dummy_file(pdd_files['code'], "print('Initial code')") # Dummy code file

    # Now, modify the prompt
    _create_dummy_file(pdd_files['prompt'], f"# Prompt for {TEST_BASENAME}\n# Updated content")
    
    decision = determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    print_decision(decision)
    assert decision.operation == 'generate'

    # --- Scenario 3: Multiple files changed (conflict) ---
    print("\nScenario 3: Conflict - Prompt and Code changed, requires LLM analysis")
    # Update fingerprint to reflect current prompt and some code
    current_prompt_hash_s3 = calculate_sha256(pdd_files['prompt'])
    current_code_hash_s3 = calculate_sha256(pdd_files['code'])
    fp_s3 = Fingerprint(
        pdd_version="0.1.0",
        timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        command="update", # Or some other command
        prompt_hash=current_prompt_hash_s3,
        code_hash=current_code_hash_s3,
        example_hash=None,
        test_hash=None
    )
    _write_json_dataclass(fingerprint_file_path, fp_s3)

    # Simulate user modifying both prompt and code independently
    _create_dummy_file(pdd_files['prompt'], f"# Prompt for {TEST_BASENAME}\n# User prompt modification")
    _create_dummy_file(pdd_files['code'], "print('User code modification')")

    decision = determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    print_decision(decision)
    assert decision.operation == 'analyze_conflict'

    if decision.operation == 'analyze_conflict':
        print("\n  Calling analyze_conflict_with_llm...")
        # The module's get_git_diff will be called. If not in a git repo, diffs will be empty.
        # The placeholder LLM in the module will provide a simulated response.
        changed_files_list = decision.details.get('changed_files', [])
        llm_decision = analyze_conflict_with_llm(
            TEST_BASENAME, TEST_LANGUAGE, fp_s3, changed_files_list
        )
        print("  LLM Analysis Decision:")
        print_decision(llm_decision)
        # The placeholder LLM is set to return low confidence, leading to 'fail_and_request_manual_merge'
        assert llm_decision.operation == 'fail_and_request_manual_merge'

    # --- Scenario 4: Run report indicates test failures ---
    print("\nScenario 4: Runtime signal - Test failures reported")
    # Reset files to a "stable" state according to fingerprint to focus on run report
    _create_dummy_file(pdd_files['prompt'], f"# Prompt for {TEST_BASENAME}\n# User prompt modification") # Content from fp_s3's prompt_hash source
    _create_dummy_file(pdd_files['code'], "print('User code modification')") # Content from fp_s3's code_hash source
    # Update fingerprint to match these files
    fp_s4 = Fingerprint(
        pdd_version="0.1.0",
        timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        command="generate",
        prompt_hash=calculate_sha256(pdd_files['prompt']),
        code_hash=calculate_sha256(pdd_files['code']),
        example_hash=None,
        test_hash=None
    )
    _write_json_dataclass(fingerprint_file_path, fp_s4)


    # Create a run report indicating test failures
    rr_s4 = RunReport(
        timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        exit_code=0,
        tests_passed=5,
        tests_failed=2,
        coverage=0.70
    )
    _write_json_dataclass(run_report_file_path, rr_s4)

    decision = determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    print_decision(decision)
    assert decision.operation == 'fix'
    _delete_file(run_report_file_path) # Clean up for next scenario

    # --- Scenario 5: SyncLock demonstration ---
    print("\nScenario 5: SyncLock basic usage")
    lock_basename = "lock_demo"
    
    # Ensure no old lock file exists
    lock_file_path = LOCKS_DIR / f"{lock_basename}_{TEST_LANGUAGE}.lock"
    _delete_file(lock_file_path)

    try:
        with SyncLock(lock_basename, TEST_LANGUAGE) as lock_instance:
            print(f"  Acquired lock for {lock_basename}. Lock file: {lock_instance.lock_file_path}")
            assert lock_instance.lock_file_path.exists()
            
            # Try acquiring again (re-entrancy by same SyncLock instance)
            lock_instance.acquire() 
            print("  Successfully re-acquired lock (re-entrant, same instance).")

            # Try acquiring with a new SyncLock instance (re-entrancy by same process)
            with SyncLock(lock_basename, TEST_LANGUAGE) as inner_lock:
                print("  Successfully acquired lock with new instance (re-entrant, new instance).")
                assert inner_lock._is_reentrant_acquisition

            print("  Inner lock released.")
            assert lock_instance.lock_file_path.exists() # Outer lock still holds

        print(f"  Outer lock for {lock_basename} released. Lock file should be gone.")
        assert not lock_instance.lock_file_path.exists()
    except TimeoutError as e:
        print(f"  Locking demonstration failed: {e}")
    except Exception as e:
        print(f"  An unexpected error occurred during lock test: {e}")
        # Ensure cleanup if error occurs
        if lock_file_path.exists():
            _delete_file(lock_file_path)
        raise


    print("\n--- PDD Sync Logic Example Completed ---")

if __name__ == "__main__":
    try:
        setup_example_environment()
        run_pdd_sync_logic_example()
    finally:
        cleanup_example_environment()
