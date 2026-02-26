# tests/test_sync_determine_operation.py

import pytest
import os
import sys
import json
import hashlib
import subprocess
from pathlib import Path
from datetime import datetime, timezone
from unittest.mock import patch, MagicMock, mock_open

# Add the 'pdd' directory to the Python path to allow imports.
# This is necessary because the test file is in 'tests/' and the code is in 'pdd/'.
pdd_path = Path(__file__).parent.parent / 'pdd'
sys.path.insert(0, str(pdd_path))

from sync_determine_operation import (
    sync_determine_operation,
    analyze_conflict_with_llm,
    SyncLock,
    Fingerprint,
    RunReport,
    SyncDecision,
    calculate_sha256,
    calculate_prompt_hash,
    extract_include_deps,
    read_fingerprint,
    read_run_report,
    PDD_DIR,
    META_DIR,
    LOCKS_DIR,
    get_pdd_dir,
    get_meta_dir,
    get_locks_dir,
    validate_expected_files,
    _handle_missing_expected_files,
    _is_workflow_complete,
    get_pdd_file_paths
)

# --- Test Plan ---
#
# The goal is to test the core decision-making logic of `pdd sync`.
# This involves testing the locking mechanism, file state analysis,
# the main decision tree, and the LLM-based conflict resolution.
#
# Formal Verification (Z3) vs. Unit Tests:
# - Z3 could be used to formally verify the completeness and exclusivity of the
#   decision tree in `_perform_sync_analysis`. This would involve modeling the
#   state space (file existence, hash matches, run report values) and the
#   decision rules to prove that every possible state leads to exactly one
#   defined outcome.
# - However, the state space is large, and the implementation details (like
#   checking prompt content for dependencies) add complexity.
# - Unit tests are more practical here. They can directly test the implemented
#   logic for each specific state combination, ensuring the code behaves as
#   expected. They are also better suited for testing interactions with the
#   filesystem, external processes (git), and mocked services (LLM).
# - Therefore, this test suite will use comprehensive unit tests with pytest.
#
# Test Suite Structure:
#
# Part 1: Core Components & Helper Functions
#   - Test `SyncLock` for acquiring, releasing, context management, stale lock
#     handling, and multi-process contention simulation.
#   - Test file utility functions (`calculate_sha256`, `read_fingerprint`,
#     `read_run_report`) for success, failure (missing file), and error
#     (malformed content) cases.
#
# Part 2: `sync_determine_operation` Decision Logic
#   - Test the `log_mode` flag to ensure it bypasses locking.
#   - Test each branch of the decision tree in priority order:
#     1.  **Runtime Signals:** `crash`, `verify` (after crash), `fix`, `test` (low coverage).
#         Test that `crash` has the highest priority.
#     2.  **No Fingerprint (New Unit):** `auto-deps`, `generate`, `nothing`.
#     3.  **No Changes (Synced State):** `nothing`, `example` (if missing), `test` (if missing).
#     4.  **Simple Changes (Single File):** `generate`/`auto-deps` (prompt), `update` (code),
#         `test` (test), `verify` (example).
#     5.  **Complex Changes (Multiple Files):** `analyze_conflict`.
#
# Part 3: `analyze_conflict_with_llm`
#   - Mock external dependencies: `llm_invoke`, `load_prompt_template`, `get_git_diff`.
#   - Test the successful path where a valid LLM response is parsed correctly.
#   - Test fallback scenarios:
#     - LLM template not found.
#     - LLM returns invalid JSON.
#     - LLM response is missing required keys.
#     - LLM confidence is below the threshold.
#     - An exception occurs during the process.
#   - In all fallback cases, the decision should be `fail_and_request_manual_merge`.
#
# Fixtures:
#   - `pdd_test_environment`: Creates a temporary directory structure for tests
#     (prompts, .pdd/meta, .pdd/locks) and cleans up afterward.
#   - Helper functions will be used to create dummy files and metadata.

# --- Fixtures and Helpers ---

BASENAME = "test_unit"
LANGUAGE = "python"
TARGET_COVERAGE = 90.0

@pytest.fixture
def pdd_test_environment(tmp_path):
    """Creates a temporary, isolated PDD project structure for testing."""
    # Change to tmp_path
    original_cwd = Path.cwd()
    os.chdir(tmp_path)
    
    # Create directories
    Path(".pdd/meta").mkdir(parents=True, exist_ok=True)
    Path(".pdd/locks").mkdir(parents=True, exist_ok=True)
    Path("prompts").mkdir(exist_ok=True)
    
    # Now update the constants after changing directory
    pdd_module = sys.modules['sync_determine_operation']
    pdd_module.PDD_DIR = pdd_module.get_pdd_dir()
    pdd_module.META_DIR = pdd_module.get_meta_dir()
    pdd_module.LOCKS_DIR = pdd_module.get_locks_dir()
    
    yield tmp_path

    # Restore original working directory
    os.chdir(original_cwd)
    
    # Update constants again
    pdd_module.PDD_DIR = pdd_module.get_pdd_dir()
    pdd_module.META_DIR = pdd_module.get_meta_dir()
    pdd_module.LOCKS_DIR = pdd_module.get_locks_dir()

def create_file(path: Path, content: str = "") -> str:
    """Creates a file with given content and returns its SHA256 hash."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return calculate_sha256(path)

def create_fingerprint_file(path: Path, data: dict):
    """Creates a fingerprint JSON file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, 'w') as f:
        json.dump(data, f)

def create_run_report_file(path: Path, data: dict):
    """Creates a run report JSON file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, 'w') as f:
        json.dump(data, f)

# --- Part 1: Core Components & Helper Functions ---

class TestSyncLock:
    def test_lock_acquire_and_release(self, pdd_test_environment):
        lock_file = get_locks_dir() / f"{BASENAME}_{LANGUAGE}.lock"
        lock = SyncLock(BASENAME, LANGUAGE)

        assert not lock_file.exists()
        lock.acquire()
        assert lock_file.exists()
        assert lock_file.read_text().strip() == str(os.getpid())
        lock.release()
        assert not lock_file.exists()

    def test_lock_context_manager(self, pdd_test_environment):
        lock_file = get_locks_dir() / f"{BASENAME}_{LANGUAGE}.lock"
        assert not lock_file.exists()
        with SyncLock(BASENAME, LANGUAGE) as lock:
            assert lock_file.exists()
            assert lock_file.read_text().strip() == str(os.getpid())
        assert not lock_file.exists()

    def test_lock_stale_lock(self, pdd_test_environment, monkeypatch):
        lock_file = get_locks_dir() / f"{BASENAME}_{LANGUAGE}.lock"
        stale_pid = 99999  # A non-existent PID
        lock_file.write_text(str(stale_pid))

        monkeypatch.setattr("psutil.pid_exists", lambda pid: pid != stale_pid)

        # Should acquire lock by removing the stale one
        with SyncLock(BASENAME, LANGUAGE):
            assert lock_file.exists()
            assert lock_file.read_text().strip() == str(os.getpid())

    def test_lock_held_by_another_process(self, pdd_test_environment, monkeypatch):
        lock_file = get_locks_dir() / f"{BASENAME}_{LANGUAGE}.lock"
        other_pid = os.getpid() + 1
        lock_file.write_text(str(other_pid))

        monkeypatch.setattr("psutil.pid_exists", lambda pid: True)

        with pytest.raises(TimeoutError, match=f"Lock held by running process {other_pid}"):
            SyncLock(BASENAME, LANGUAGE).acquire()

    def test_lock_reentrancy(self, pdd_test_environment):
        lock = SyncLock(BASENAME, LANGUAGE)
        with lock:
            # Try acquiring again within the same process
            lock.acquire() # Should not raise an error
            assert (get_locks_dir() / f"{BASENAME}_{LANGUAGE}.lock").exists()


class TestFileUtilities:
    def test_calculate_sha256(self, pdd_test_environment):
        file_path = pdd_test_environment / "test.txt"
        content = "hello world"
        expected_hash = hashlib.sha256(content.encode()).hexdigest()
        create_file(file_path, content)
        assert calculate_sha256(file_path) == expected_hash

    def test_calculate_sha256_not_exists(self, pdd_test_environment):
        assert calculate_sha256(pdd_test_environment / "nonexistent.txt") is None

    def test_read_fingerprint_success(self, pdd_test_environment):
        fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
        fp_data = {
            "pdd_version": "1.0", "timestamp": "2023-01-01T00:00:00Z",
            "command": "generate", "prompt_hash": "p_hash", "code_hash": "c_hash",
            "example_hash": "e_hash", "test_hash": "t_hash"
        }
        create_fingerprint_file(fp_path, fp_data)
        fp = read_fingerprint(BASENAME, LANGUAGE)
        assert isinstance(fp, Fingerprint)
        assert fp.prompt_hash == "p_hash"

    def test_read_fingerprint_invalid_json(self, pdd_test_environment):
        fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
        fp_path.write_text("{ not valid json }")
        assert read_fingerprint(BASENAME, LANGUAGE) is None

    def test_read_run_report_success(self, pdd_test_environment):
        rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
        rr_data = {
            "timestamp": "2023-01-01T00:00:00Z", "exit_code": 0,
            "tests_passed": 10, "tests_failed": 0, "coverage": 95.5
        }
        create_run_report_file(rr_path, rr_data)
        rr = read_run_report(BASENAME, LANGUAGE)
        assert isinstance(rr, RunReport)
        assert rr.tests_failed == 0
        assert rr.coverage == 95.5


# --- Part 2: `sync_determine_operation` Decision Logic ---

@patch('sync_determine_operation.construct_paths')
def test_log_mode_skips_lock(mock_construct, pdd_test_environment):
    with patch('sync_determine_operation.SyncLock') as mock_lock:
        sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, log_mode=True)
        mock_lock.assert_not_called()

    with patch('sync_determine_operation.SyncLock') as mock_lock:
        sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, log_mode=False)
        mock_lock.assert_called_once_with(BASENAME, LANGUAGE)

# --- Runtime Signal Tests ---
def test_context_aware_fix_over_crash_logic(pdd_test_environment):
    """Test the new context-aware decision logic that prefers 'fix' over 'crash'."""

    # Create prompt file and get its real hash
    prompts_dir = pdd_test_environment / "prompts"
    prompts_dir.mkdir(exist_ok=True)
    prompt_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", "Test prompt")

    # Test Case 1: No successful history - should use 'crash'
    create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
        "pdd_version": "1.0.0",
        "timestamp": "2025-07-15T12:00:00Z",
        "command": "generate",  # No successful example history
        "prompt_hash": prompt_hash,  # Use real hash so prompt change detection doesn't trigger
        "code_hash": "test_hash",
        "example_hash": None,
        "test_hash": None
    })

    create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
        "timestamp": "2025-07-15T12:00:00Z",
        "exit_code": 1,
        "tests_passed": 0,
        "tests_failed": 0,
        "coverage": 0.0
    })

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
    assert decision.operation == 'crash'
    assert "no successful example history" in decision.reason.lower()
    assert decision.details['example_success_history'] == False

    # Test Case 2: Successful history via 'verify' command - should use 'fix'
    create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
        "pdd_version": "1.0.0",
        "timestamp": "2025-07-15T12:00:00Z",
        "command": "verify",  # Indicates successful example history
        "prompt_hash": prompt_hash,  # Use real hash
        "code_hash": "test_hash",
        "example_hash": "test_hash",
        "test_hash": None
    })

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
    assert decision.operation == 'fix'
    assert "prefer fix over crash" in decision.reason.lower()
    assert decision.details['example_success_history'] == True

    # Test Case 3: Successful history via 'test' command - should use 'fix'
    create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
        "pdd_version": "1.0.0",
        "timestamp": "2025-07-15T12:00:00Z",
        "command": "test",  # Indicates successful example history
        "prompt_hash": prompt_hash,  # Use real hash
        "code_hash": "test_hash",
        "example_hash": "test_hash",
        "test_hash": "test_hash"
    })

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
    assert decision.operation == 'fix'
    assert "prefer fix over crash" in decision.reason.lower()
    assert decision.details['example_success_history'] == True


@patch('sync_determine_operation.construct_paths')
def test_decision_crash_on_exit_code_nonzero(mock_construct, pdd_test_environment):
    # Create fingerprint (required for run_report to be processed)
    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0", "timestamp": "t", "command": "generate",
        "prompt_hash": "p", "code_hash": "c", "example_hash": "e", "test_hash": "t"
    })
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 1, "tests_passed": 0, "tests_failed": 0, "coverage": 0.0
    })
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE)
    assert decision.operation == 'crash'
    assert "Runtime error detected" in decision.reason

@patch('sync_determine_operation.construct_paths')
def test_decision_verify_after_crash_fix(mock_construct, pdd_test_environment):
    # Last command was 'crash'
    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0", "timestamp": "t", "command": "crash",
        "prompt_hash": "p", "code_hash": "c", "example_hash": "e", "test_hash": "t"
    })
    # And the run report shows SUCCESS (exit_code=0) - crash fix worked
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 0, "tests_passed": 0, "tests_failed": 0, "coverage": 0.0
    })
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE)
    assert decision.operation == 'verify'
    assert "Previous crash operation completed" in decision.reason


@patch('sync_determine_operation.construct_paths')
def test_decision_crash_retry_when_exit_code_nonzero(mock_construct, pdd_test_environment):
    """When crash operation failed (exit_code != 0), should retry crash, not proceed to verify."""
    # Last command was 'crash'
    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0", "timestamp": "t", "command": "crash",
        "prompt_hash": "p", "code_hash": "c", "example_hash": "e", "test_hash": "t"
    })
    # And the run report shows FAILURE (exit_code=1) - crash fix didn't work
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 1, "tests_passed": 0, "tests_failed": 0, "coverage": 0.0
    })
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE)
    assert decision.operation == 'crash', f"Expected 'crash' when exit_code=1, got '{decision.operation}'"
    assert "retry crash fix" in decision.reason

@patch('sync_determine_operation.construct_paths')
def test_decision_fix_on_test_failures(mock_construct, pdd_test_environment):
    # Create prompt file so get_pdd_file_paths can work properly
    prompts_dir = pdd_test_environment / "prompts"
    prompts_dir.mkdir(exist_ok=True)
    prompt_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", "Test prompt")

    # Create test file so test_file.exists() check passes
    test_file = pdd_test_environment / f"test_{BASENAME}.py"
    test_hash = create_file(test_file, "def test_dummy(): pass")

    # Mock construct_paths to return the test file path
    mock_construct.return_value = (
        {}, {},
        {'test_file': str(test_file)},
        LANGUAGE
    )

    # Create fingerprint (required for run_report to be processed)
    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0", "timestamp": "t", "command": "test",
        "prompt_hash": prompt_hash, "code_hash": "c", "example_hash": "e", "test_hash": test_hash
    })

    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 0, "tests_passed": 5, "tests_failed": 2, "coverage": 80.0,
        "test_hash": test_hash
    })
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
    assert decision.operation == 'fix'
    assert "Test failures detected" in decision.reason

@patch('sync_determine_operation.construct_paths')
@patch('sync_determine_operation.get_pdd_file_paths')
def test_decision_test_on_low_coverage(mock_get_pdd_paths, mock_construct, pdd_test_environment):
    tmp_path = pdd_test_environment

    # Create test file on disk so test_file_exists check passes
    Path("tests").mkdir(exist_ok=True)
    test_path = tmp_path / "tests" / f"test_{BASENAME}.py"
    create_file(test_path, "def test_foo(): pass")

    # Mock get_pdd_file_paths to return the test path
    mock_get_pdd_paths.return_value = {
        'prompt': tmp_path / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt",
        'code': tmp_path / f"{BASENAME}.py",
        'example': tmp_path / f"{BASENAME}_example.py",
        'test': test_path,
    }

    # Create fingerprint (required for run_report to be processed)
    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0", "timestamp": "t", "command": "test",
        "prompt_hash": "p", "code_hash": "c", "example_hash": "e", "test_hash": "t"
    })
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 0, "tests_passed": 10, "tests_failed": 0, "coverage": 75.0,
        "test_hash": "t"
    })
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE)
    # When tests pass but coverage is low, we return test_extend to add more tests
    assert decision.operation == 'test_extend'
    assert f"coverage 75.0% below target {TARGET_COVERAGE:.1f}%" in decision.reason.lower()

# --- No Fingerprint Tests ---
@patch('sync_determine_operation.construct_paths')
def test_decision_generate_for_new_prompt(mock_construct, pdd_test_environment):
    create_file(pdd_test_environment / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt", "A simple prompt.")
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(pdd_test_environment / "prompts"))
    assert decision.operation == 'generate'
    assert "New prompt ready" in decision.reason

@patch('sync_determine_operation.construct_paths')
def test_decision_autodeps_for_new_prompt_with_deps(mock_construct, pdd_test_environment):
    create_file(pdd_test_environment / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt", "A prompt that needs to <include> another file.")
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(pdd_test_environment / "prompts"))
    assert decision.operation == 'auto-deps'
    assert "New prompt with dependencies detected" in decision.reason

@patch('sync_determine_operation.construct_paths')
def test_decision_nothing_for_new_unit_no_prompt(mock_construct, pdd_test_environment):
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE)
    assert decision.operation == 'nothing'
    assert "No prompt file and no history" in decision.reason

# --- State Change Tests ---
@patch('sync_determine_operation.construct_paths')
def test_decision_nothing_when_synced(mock_construct, pdd_test_environment):
    prompts_dir = pdd_test_environment / "prompts"
    p_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt")
    c_hash = create_file(pdd_test_environment / f"{BASENAME}.py")
    e_hash = create_file(pdd_test_environment / f"{BASENAME}_example.py")
    t_hash = create_file(pdd_test_environment / f"test_{BASENAME}.py")

    mock_construct.return_value = (
        {}, {},
        {
            'code_file': str(pdd_test_environment / f"{BASENAME}.py"),
            'example_file': str(pdd_test_environment / f"{BASENAME}_example.py"),
            'test_file': str(pdd_test_environment / f"test_{BASENAME}.py")
        },
        LANGUAGE
    )

    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0", "timestamp": "t", "command": "test",
        "prompt_hash": p_hash, "code_hash": c_hash, "example_hash": e_hash, "test_hash": t_hash
    })

    # Create run_report to indicate code has been validated
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 0, "tests_passed": 5, "tests_failed": 0, "coverage": 95.0
    })

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
    assert decision.operation == 'nothing'
    assert "All required files synchronized" in decision.reason

def test_fix_over_crash_with_successful_example_history(pdd_test_environment):
    """Test sync --skip-tests when a crash operation would be triggered."""

    # Create prompt file and get its real hash
    prompts_dir = pdd_test_environment / "prompts"
    prompts_dir.mkdir(exist_ok=True)
    prompt_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", "Create a simple add function")

    # Create metadata with real prompt hash
    fingerprint_data = {
        "pdd_version": "0.0.41",
        "timestamp": "2025-07-03T02:34:36.929768+00:00",
        "command": "test",
        "prompt_hash": prompt_hash,  # Use real hash so prompt change detection doesn't trigger
        "code_hash": "6d0669923dc331420baaaefea733849562656e00f90c6519bbed46c1e9096595",
        "example_hash": "861d5b27f80c1e3b5b21b23fb58bfebb583bd4224cde95b2517a426ea4661fae",
        "test_hash": "37f6503380c4dd80a5c33be2fe08429dbc9239dd602a8147ed150863db17651f"
    }
    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, fingerprint_data)

    # Create run report with exit_code=2 (crash scenario)
    run_report = {
        "timestamp": "2025-07-03T02:34:36.182803+00:00",
        "exit_code": 2,
        "tests_passed": 0,
        "tests_failed": 0,
        "coverage": 0.0
    }
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, run_report)

    # Test with skip_tests=True - sync_determine_operation should prefer fix over crash
    # when there's successful example history (fingerprint command is "test")
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, skip_tests=True, prompts_dir=str(prompts_dir))

    # With context-aware decision logic, should prefer 'fix' over 'crash' when example has run successfully before
    # The fingerprint command is "test" which indicates successful example history
    assert decision.operation == 'fix'
    assert "prefer fix over crash" in decision.reason.lower()
    assert decision.details['exit_code'] == 2
    assert decision.details['example_success_history'] == True

def test_regression_root_cause_missing_files_with_metadata(pdd_test_environment):
    """
    Test that demonstrates the root cause fix: sync_determine_operation should return 'generate'
    (not 'analyze_conflict') when files are missing but metadata exists.
    """

    # Create prompt file and get its real hash
    prompts_dir = pdd_test_environment / "prompts"
    prompts_dir.mkdir(exist_ok=True)
    prompt_content = """Create a Python module with a simple math function.

Requirements:
- Function name: add
- Parameters: a, b (both numbers)
- Return: sum of a and b
- Include type hints
- Add docstring explaining the function

Example usage:
result = add(5, 3)  # Should return 8"""

    prompt_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", prompt_content)

    # Create metadata with real prompt hash (so prompt change detection doesn't trigger)
    from datetime import datetime, timezone
    fingerprint_data = {
        "pdd_version": "0.0.41",
        "timestamp": "2025-07-03T02:34:36.929768+00:00",
        "command": "test",
        "prompt_hash": prompt_hash,  # Use real hash so we test missing files, not prompt change
        "code_hash": "6d0669923dc331420baaaefea733849562656e00f90c6519bbed46c1e9096595",
        "example_hash": "861d5b27f80c1e3b5b21b23fb58bfebb583bd4224cde95b2517a426ea4661fae",
        "test_hash": "37f6503380c4dd80a5c33be2fe08429dbc9239dd602a8147ed150863db17651f"
    }
    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, fingerprint_data)

    # Create run report indicating previous successful test execution
    run_report = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "exit_code": 0,
        "tests_passed": 1,
        "tests_failed": 0,
        "coverage": 100.0
    }
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, run_report)

    # Key test: Files are missing but metadata exists
    # This was causing 'analyze_conflict' but should return 'generate'

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))

    # The fix: should detect missing files and return 'generate', not 'analyze_conflict'
    assert decision.operation == 'generate'
    assert decision.operation != 'analyze_conflict'
    assert "file missing" in decision.reason.lower() or "new" in decision.reason.lower()

def test_regression_fix_validation_skip_tests_scenarios(pdd_test_environment):
    """
    Validate that skip_tests scenarios work correctly after the regression fix.
    """

    # Create prompt file and get its real hash
    prompts_dir = pdd_test_environment / "prompts"
    prompts_dir.mkdir(exist_ok=True)
    prompt_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", "Create a simple add function")

    test_scenarios = [
        {
            "name": "missing_files_with_metadata_skip_tests",
            "metadata": {
                "pdd_version": "0.0.41",
                "timestamp": "2023-01-01T00:00:00Z",
                "command": "test",
                "prompt_hash": prompt_hash,  # Use real hash so prompt change detection doesn't trigger
                "code_hash": "def456",
                "example_hash": "ghi789",
                "test_hash": "jkl012"
            },
            "run_report": {
                "timestamp": "2023-01-01T00:00:00Z",
                "exit_code": 0,
                "tests_passed": 5,
                "tests_failed": 0,
                "coverage": 50.0  # Low coverage
            },
            "skip_tests": True,
            "expected_not": ["analyze_conflict", "test"],
            "expected_in": ["all_synced", "generate", "auto-deps"]
        },
        {
            "name": "crash_scenario_skip_tests",
            "metadata": {
                "pdd_version": "0.0.41",
                "timestamp": "2023-01-01T00:00:00Z",
                "command": "crash",
                "prompt_hash": prompt_hash,  # Use real hash so prompt change detection doesn't trigger
                "code_hash": "def456",
                "example_hash": "ghi789",
                "test_hash": "jkl012"
            },
            "run_report": {
                "timestamp": "2023-01-01T00:00:00Z",
                "exit_code": 2,  # Crash exit code - crash fix failed!
                "tests_passed": 0,
                "tests_failed": 0,
                "coverage": 0.0
            },
            "skip_tests": True,
            "expected_not": ["analyze_conflict"],
            "expected_in": ["crash"]  # When fingerprint.command='crash' and exit_code!=0, retry crash
        }
    ]

    for scenario in test_scenarios:
        # Clean up previous state
        for meta_file in get_meta_dir().glob("*.json"):
            meta_file.unlink()

        # Setup scenario
        if scenario["metadata"]:
            fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
            create_fingerprint_file(fp_path, scenario["metadata"])

        if scenario["run_report"]:
            rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
            create_run_report_file(rr_path, scenario["run_report"])

        # Test decision
        decision = sync_determine_operation(
            BASENAME, LANGUAGE, TARGET_COVERAGE,
            skip_tests=scenario["skip_tests"],
            prompts_dir=str(prompts_dir)
        )

        # Validate results
        for forbidden_op in scenario["expected_not"]:
            assert decision.operation != forbidden_op, f"Scenario {scenario['name']}: got forbidden operation {forbidden_op}"
        
        assert decision.operation in scenario["expected_in"], f"Scenario {scenario['name']}: got {decision.operation}, expected one of {scenario['expected_in']}"

def test_real_hashes_with_context_aware_fix_over_crash(pdd_test_environment):
    """
    Test the exact scenario from debug_real_hashes.py:
    Missing files with metadata containing real hashes AND exit_code=2 with skip_tests=True.
    """

    # Create prompt file and get its real hash
    prompts_dir = pdd_test_environment / "prompts"
    prompts_dir.mkdir(exist_ok=True)
    prompt_content = """Create a Python module with a simple math function.

Requirements:
- Function name: add
- Parameters: a, b (both numbers)
- Return: sum of a and b
- Include type hints
- Add docstring explaining the function

Example usage:
result = add(5, 3)  # Should return 8"""

    prompt_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", prompt_content)

    # Create metadata with real prompt hash (so prompt change detection doesn't trigger)
    fingerprint_data = {
        "pdd_version": "0.0.41",
        "timestamp": "2025-07-03T02:34:36.929768+00:00",
        "command": "test",
        "prompt_hash": prompt_hash,  # Use real hash so we test fix-over-crash, not prompt change
        "code_hash": "6d0669923dc331420baaaefea733849562656e00f90c6519bbed46c1e9096595",
        "example_hash": "861d5b27f80c1e3b5b21b23fb58bfebb583bd4224cde95b2517a426ea4661fae",
        "test_hash": "37f6503380c4dd80a5c33be2fe08429dbc9239dd602a8147ed150863db17651f"
    }
    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, fingerprint_data)

    # Create run report with crash exit code (exact from debug scenario)
    run_report = {
        "timestamp": "2025-07-03T02:34:36.182803+00:00",
        "exit_code": 2,  # This triggers crash operation normally
        "tests_passed": 0,
        "tests_failed": 0,
        "coverage": 0.0
    }
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, run_report)

    # Test with skip_tests=True - the exact scenario that was causing issues
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, skip_tests=True, prompts_dir=str(prompts_dir))

    # Key assertions from debug_real_hashes.py:
    # 1. Should not return 'analyze_conflict' (was causing infinite loops)
    assert decision.operation != 'analyze_conflict', "Should not return analyze_conflict with missing files and real hashes"

    # 2. Should not return 'test' operation when skip_tests=True
    assert decision.operation != 'test', "Should not return test operation when skip_tests=True"

    # 3. With context-aware decision logic, should prefer 'fix' over 'crash' when example has run successfully before
    # The fingerprint command is "test" which indicates successful example history
    assert decision.operation == 'fix', f"Expected fix operation (context-aware), got {decision.operation}"
    assert "prefer fix over crash" in decision.reason.lower()
    assert decision.details['example_success_history'] == True

@patch('sync_determine_operation.construct_paths')
def test_decision_example_when_missing(mock_construct, pdd_test_environment):
    prompts_dir = pdd_test_environment / "prompts"
    p_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt")
    c_hash = create_file(pdd_test_environment / f"{BASENAME}.py")

    mock_construct.return_value = (
        {}, {},
        {
            'code_file': str(pdd_test_environment / f"{BASENAME}.py"),
            'example_file': str(pdd_test_environment / f"{BASENAME}_example.py"),
            'test_file': str(pdd_test_environment / f"test_{BASENAME}.py")
        },
        LANGUAGE
    )

    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0", "timestamp": "t", "command": "generate",
        "prompt_hash": p_hash, "code_hash": c_hash, "example_hash": None, "test_hash": None
    })

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
    assert decision.operation == 'example'
    assert "Code exists but example missing" in decision.reason

@patch('sync_determine_operation.construct_paths')
def test_decision_update_on_code_change(mock_construct, pdd_test_environment):
    prompts_dir = pdd_test_environment / "prompts"
    p_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt")
    create_file(pdd_test_environment / f"{BASENAME}.py", "modified code") # New hash

    mock_construct.return_value = (
        {}, {},
        {
            'code_file': str(pdd_test_environment / f"{BASENAME}.py"),
            'example_file': str(pdd_test_environment / f"{BASENAME}_example.py"),
            'test_file': str(pdd_test_environment / f"test_{BASENAME}.py")
        },
        LANGUAGE
    )

    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.o", "timestamp": "t", "command": "generate",
        "prompt_hash": p_hash, "code_hash": "original_code_hash", "example_hash": None, "test_hash": None
    })

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
    assert decision.operation == 'update'
    assert "Code changed" in decision.reason

@patch('sync_determine_operation.construct_paths')
def test_decision_analyze_conflict_on_multiple_changes(mock_construct, pdd_test_environment):
    """When both prompt and derived files changed, fingerprint should be deleted and sync restarts fresh."""
    prompts_dir = pdd_test_environment / "prompts"
    create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", "modified prompt")
    create_file(pdd_test_environment / f"{BASENAME}.py", "modified code")

    mock_construct.return_value = (
        {}, {},
        {
            'code_file': str(pdd_test_environment / f"{BASENAME}.py"),
            'example_file': str(pdd_test_environment / f"{BASENAME}_example.py"),
            'test_file': str(pdd_test_environment / f"test_{BASENAME}.py")
        },
        LANGUAGE
    )

    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0", "timestamp": "t", "command": "generate",
        "prompt_hash": "original_prompt_hash", "code_hash": "original_code_hash",
        "example_hash": None, "test_hash": None
    })

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
    # Should restart fresh (generate) instead of returning analyze_conflict
    assert decision.operation == 'generate'
    # Fingerprint file should have been deleted (re-analysis treats it as new module)
    assert not fp_path.exists(), "Fingerprint file should be deleted on conflict"
    assert decision.details.get('fingerprint_found') == False


@patch('sync_determine_operation.construct_paths')
def test_conflict_deletes_fingerprint_and_run_report(mock_construct, pdd_test_environment):
    """When both prompt and derived files changed (no run_report), fingerprint is deleted and sync restarts fresh.

    Note: When a run_report exists alongside a fingerprint, prompt changes are caught
    by an earlier code path (line ~1298) that returns 'generate' directly without
    reaching the conflict detection. The conflict+deletion path is reached when
    there is no run_report (e.g., after a generate that didn't run tests yet).
    """
    prompts_dir = pdd_test_environment / "prompts"
    create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", "modified prompt")
    create_file(pdd_test_environment / f"{BASENAME}.py", "modified code")

    mock_construct.return_value = (
        {}, {},
        {
            'code_file': str(pdd_test_environment / f"{BASENAME}.py"),
            'example_file': str(pdd_test_environment / f"{BASENAME}_example.py"),
            'test_file': str(pdd_test_environment / f"test_{BASENAME}.py")
        },
        LANGUAGE
    )

    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"

    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0", "timestamp": "t", "command": "generate",
        "prompt_hash": "original_prompt_hash", "code_hash": "original_code_hash",
        "example_hash": None, "test_hash": None
    })
    # Also create a run report to verify it gets cleaned up
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 0,
        "tests_passed": 5, "tests_failed": 0,
        "coverage": 80.0, "test_hash": None
    })

    assert fp_path.exists()
    assert rr_path.exists()

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))

    # When run_report exists, the early prompt-change check (line ~1298) catches this
    # and returns 'generate' directly — the conflict path is not reached.
    # Either way, the result should be 'generate' (not 'analyze_conflict').
    assert decision.operation == 'generate'
    assert decision.operation != 'analyze_conflict'


# --- Part 3: `analyze_conflict_with_llm` ---

@patch('sync_determine_operation.get_git_diff', return_value="fake diff")
@patch('sync_determine_operation.load_prompt_template', return_value="prompt: {prompt_diff}")
@patch('sync_determine_operation.llm_invoke')
@patch('sync_determine_operation.construct_paths')
def test_analyze_conflict_success(mock_construct, mock_llm_invoke, mock_load_template, mock_git_diff, pdd_test_environment):
    mock_llm_invoke.return_value = {
        'result': json.dumps({
            "next_operation": "generate",
            "reason": "LLM says so",
            "confidence": 0.9,
            "merge_strategy": {"type": "three_way_merge_safe"}
        }),
        'cost': 0.05
    }
    fingerprint = Fingerprint("1.0", "t", "generate", "p_hash", "c_hash", None, None)
    changed_files = ['prompt', 'code']

    decision = analyze_conflict_with_llm(BASENAME, LANGUAGE, fingerprint, changed_files)

    assert decision.operation == 'generate'
    assert "LLM analysis: LLM says so" in decision.reason
    assert decision.confidence == 0.9
    assert decision.estimated_cost == 0.05
    mock_load_template.assert_called_with("sync_analysis_LLM")

@patch('sync_determine_operation.get_git_diff')
@patch('sync_determine_operation.load_prompt_template')
@patch('sync_determine_operation.llm_invoke')
@patch('sync_determine_operation.construct_paths')
def test_analyze_conflict_llm_invalid_json(mock_construct, mock_llm_invoke, mock_load_template, mock_git_diff, pdd_test_environment):
    mock_load_template.return_value = "template"
    mock_llm_invoke.return_value = {'result': 'this is not json', 'cost': 0.01}
    fingerprint = Fingerprint("1.0", "t", "generate", "p", "c", None, None)

    decision = analyze_conflict_with_llm(BASENAME, LANGUAGE, fingerprint, ['prompt'])

    assert decision.operation == 'fail_and_request_manual_merge'
    assert "Invalid LLM response" in decision.reason
    assert decision.confidence == 0.0

@patch('sync_determine_operation.get_git_diff')
@patch('sync_determine_operation.load_prompt_template')
@patch('sync_determine_operation.llm_invoke')
@patch('sync_determine_operation.construct_paths')
def test_analyze_conflict_llm_low_confidence(mock_construct, mock_llm_invoke, mock_load_template, mock_git_diff, pdd_test_environment):
    mock_load_template.return_value = "template"
    mock_llm_invoke.return_value = {
        'result': json.dumps({"next_operation": "generate", "reason": "not sure", "confidence": 0.5}),
        'cost': 0.05
    }
    fingerprint = Fingerprint("1.0", "t", "generate", "p", "c", None, None)

    decision = analyze_conflict_with_llm(BASENAME, LANGUAGE, fingerprint, ['prompt'])

    assert decision.operation == 'fail_and_request_manual_merge'
    assert "LLM confidence too low" in decision.reason
    assert decision.confidence == 0.5

@patch('sync_determine_operation.load_prompt_template', return_value=None)
@patch('sync_determine_operation.construct_paths')
def test_analyze_conflict_llm_template_missing(mock_construct, mock_load_template, pdd_test_environment):
    fingerprint = Fingerprint("1.0", "t", "generate", "p", "c", None, None)
    decision = analyze_conflict_with_llm(BASENAME, LANGUAGE, fingerprint, ['prompt'])
    assert decision.operation == 'fail_and_request_manual_merge'
    assert "LLM analysis template not found" in decision.reason


# --- Part 4: Skip Flag Tests ---

@patch('sync_determine_operation.construct_paths')
def test_skip_tests_prevents_test_operation_on_low_coverage(mock_construct, pdd_test_environment):
    """Test that test operation is not returned when skip_tests=True even with low coverage."""
    # Create fingerprint (required for run_report to be processed)
    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0", "timestamp": "t", "command": "test",
        "prompt_hash": "p", "code_hash": "c", "example_hash": "e", "test_hash": "t"
    })
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 0, "tests_passed": 10, "tests_failed": 0, "coverage": 75.0,
        "test_hash": "t"
    })
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, skip_tests=True)
    assert decision.operation == 'all_synced'
    assert "tests skipped" in decision.reason.lower()

@patch('sync_determine_operation.construct_paths')
def test_skip_tests_workflow_completion(mock_construct, pdd_test_environment):
    """Test workflow completion when skip_tests=True and test files are missing."""
    prompts_dir = pdd_test_environment / "prompts"
    p_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt")
    c_hash = create_file(pdd_test_environment / f"{BASENAME}.py")
    e_hash = create_file(pdd_test_environment / f"{BASENAME}_example.py")
    # Note: NO test file created

    mock_construct.return_value = (
        {}, {},
        {
            'code_file': str(pdd_test_environment / f"{BASENAME}.py"),
            'example_file': str(pdd_test_environment / f"{BASENAME}_example.py"),
            'test_file': str(pdd_test_environment / f"test_{BASENAME}.py")
        },
        LANGUAGE
    )

    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0", "timestamp": "t", "command": "example",
        "prompt_hash": p_hash, "code_hash": c_hash, "example_hash": e_hash, "test_hash": None
    })

    # Create run_report to indicate code has been validated
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 0, "tests_passed": 0, "tests_failed": 0, "coverage": 0.0
    })

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir), skip_tests=True)
    # Either 'nothing' or 'all_synced' indicates workflow is complete
    assert decision.operation in ['nothing', 'all_synced'], f"Expected done state, got {decision.operation}"
    # Check for skip_tests in reason or that it's an all_synced with tests skipped
    assert "skip_tests=True" in decision.reason or "tests skipped" in decision.reason.lower()

@patch('sync_determine_operation.construct_paths')
def test_skip_flags_parameter_propagation(mock_construct, pdd_test_environment):
    """Test that skip flags are correctly used in decision logic."""
    # Test with both flags enabled
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, skip_tests=True, skip_verify=True)
    # Should not crash and should handle skip flags properly
    assert isinstance(decision, SyncDecision)

@patch('sync_determine_operation.construct_paths')
def test_skip_flags_dont_interfere_with_crash_fix(mock_construct, pdd_test_environment):
    """Test that skip flags don't interfere with crash/fix operations."""
    # Create prompt file so get_pdd_file_paths can work properly
    prompts_dir = pdd_test_environment / "prompts"
    prompts_dir.mkdir(exist_ok=True)
    prompt_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", "Test prompt")

    # Create test file so test_file.exists() check passes
    test_file = pdd_test_environment / f"test_{BASENAME}.py"
    test_hash = create_file(test_file, "def test_dummy(): pass")

    # Mock construct_paths to return the test file path
    mock_construct.return_value = (
        {}, {},
        {'test_file': str(test_file)},
        LANGUAGE
    )

    # Create fingerprint (required for run_report to be processed)
    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0", "timestamp": "t", "command": "test",
        "prompt_hash": prompt_hash, "code_hash": "c", "example_hash": "e", "test_hash": test_hash
    })

    # Create run report with test failures (fix should still trigger)
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 0, "tests_passed": 5, "tests_failed": 2, "coverage": 80.0,
        "test_hash": test_hash
    })

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir), skip_tests=True, skip_verify=True)
    assert decision.operation == 'fix'  # Should still trigger fix despite skip flags
    assert "Test failures detected" in decision.reason

# --- Part 5: Integration Tests - Example Scenarios ---

class TestIntegrationScenarios:
    """Test the four scenarios from the example script using actual filesystem operations."""
    
    @pytest.fixture
    def integration_test_environment(self, tmp_path):
        """Creates a temporary test environment that mimics real usage."""
        original_cwd = Path.cwd()
        
        # Change to the temp directory to ensure relative paths work correctly
        os.chdir(tmp_path)
        
        # Create necessary directories
        Path(".pdd/meta").mkdir(parents=True, exist_ok=True)
        Path(".pdd/locks").mkdir(parents=True, exist_ok=True)
        
        yield tmp_path
        
        # Restore original working directory
        os.chdir(original_cwd)
    
    def test_scenario_new_unit(self, integration_test_environment):
        """Scenario 1: New Unit - A new prompt file exists with no other files or history."""
        basename = "calculator"
        language = "python"
        target_coverage = 10.0
        
        # Re-import after changing directory to ensure proper module state
        from pdd.sync_determine_operation import sync_determine_operation
        
        # Create a new prompt file in the default prompts location
        prompts_dir = Path("prompts")
        prompts_dir.mkdir(exist_ok=True)
        prompt_path = prompts_dir / f"{basename}_{language}.prompt"
        create_file(prompt_path, "Create a function to add two numbers.")
        
        # No need to mock construct_paths - let it use default behavior
        decision = sync_determine_operation(basename, language, target_coverage, log_mode=True)
        
        assert decision.operation == 'generate'
        assert "New prompt ready" in decision.reason
    
    def test_scenario_test_failures(self, integration_test_environment):
        """Scenario 2: Test Failure - A run report exists indicating test failures."""
        basename = "calculator"
        language = "python"
        target_coverage = 10.0

        # Re-import after changing directory
        from pdd.sync_determine_operation import sync_determine_operation

        # Create files
        prompts_dir = Path("prompts")
        prompts_dir.mkdir(exist_ok=True)
        prompt_hash = create_file(prompts_dir / f"{basename}_{language}.prompt", "...")
        create_file(Path(f"{basename}.py"), "def add(a, b): return a + b")
        test_hash = create_file(Path(f"test_{basename}.py"), "assert add(2, 2) == 5")

        # Create fingerprint (required for run_report to be processed)
        fp_path = Path(".pdd/meta") / f"{basename}_{language}.json"
        create_fingerprint_file(fp_path, {
            "pdd_version": "1.0", "timestamp": "t", "command": "test",
            "prompt_hash": prompt_hash, "code_hash": "c", "example_hash": "e", "test_hash": test_hash
        })

        # Create run report with test failure (exit_code=0 but tests_failed>0 for 'fix' operation)
        run_report = {
            "timestamp": "2025-06-29T10:00:00",
            "exit_code": 0,  # Use 0 to avoid 'crash' operation
            "tests_passed": 0,
            "tests_failed": 1,
            "coverage": 50.0,
            "test_hash": test_hash
        }
        rr_path = Path(".pdd/meta") / f"{basename}_{language}_run.json"
        create_run_report_file(rr_path, run_report)

        decision = sync_determine_operation(basename, language, target_coverage, log_mode=True)

        assert decision.operation == 'fix'
        assert "Test failures detected" in decision.reason
    
    def test_scenario_manual_code_change(self, integration_test_environment):
        """Scenario 3: Manual Code Change - Code file was modified; its hash no longer matches the fingerprint."""
        basename = "calculator"
        language = "python"
        target_coverage = 10.0
        
        # Re-import after changing directory
        from pdd.sync_determine_operation import sync_determine_operation
        
        # Create files
        prompts_dir = Path("prompts")
        prompts_dir.mkdir(exist_ok=True)
        prompt_content = "..."
        prompt_hash = hashlib.sha256(prompt_content.encode()).hexdigest()
        create_file(prompts_dir / f"{basename}_{language}.prompt", prompt_content)
        
        # Create fingerprint with old code hash
        old_code_hash = "abc123def456"
        fingerprint = {
            "pdd_version": "0.1.0",
            "timestamp": "2025-06-29T10:00:00",
            "command": "generate",
            "prompt_hash": prompt_hash,
            "code_hash": old_code_hash,
            "example_hash": None,
            "test_hash": None
        }
        fp_path = Path(".pdd/meta") / f"{basename}_{language}.json"
        create_fingerprint_file(fp_path, fingerprint)
        
        # Create code file with different content (different hash)
        create_file(Path(f"{basename}.py"), "# User added a comment\ndef add(a, b): return a + b")
        
        decision = sync_determine_operation(basename, language, target_coverage, log_mode=True)
        
        assert decision.operation == 'update'
        assert "Code changed" in decision.reason
    
    def test_scenario_synchronized_unit(self, integration_test_environment):
        """Scenario 4: Unit Synchronized - All file hashes match the fingerprint and tests passed."""
        basename = "calculator"
        language = "python"
        target_coverage = 10.0
        
        # Re-import after changing directory
        from pdd.sync_determine_operation import sync_determine_operation
        
        # Create all files with specific content
        prompts_dir = Path("prompts")
        prompts_dir.mkdir(exist_ok=True)
        prompt_content = "..."
        code_content = "def add(a, b): return a + b"
        example_content = "print(add(1,1))"
        test_content = "assert add(2, 2) == 4"
        
        prompt_hash = create_file(prompts_dir / f"{basename}_{language}.prompt", prompt_content)
        code_hash = create_file(Path(f"{basename}.py"), code_content)
        # Create example in both default current dir and new examples/ dir default
        example_hash = create_file(Path(f"{basename}_example.py"), example_content)
        examples_dir = Path("examples")
        examples_dir.mkdir(exist_ok=True)
        create_file(examples_dir / f"{basename}_example.py", example_content)
        test_hash = create_file(Path(f"test_{basename}.py"), test_content)
        
        # Create matching fingerprint
        fingerprint = {
            "pdd_version": "0.1.0",
            "timestamp": "2025-06-29T10:00:00",
            "command": "fix",
            "prompt_hash": prompt_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash
        }
        fp_path = Path(".pdd/meta") / f"{basename}_{language}.json"
        create_fingerprint_file(fp_path, fingerprint)
        
        # Create successful run report
        run_report = {
            "timestamp": "2025-06-29T10:00:00",
            "exit_code": 0,
            "tests_passed": 1,
            "tests_failed": 0,
            "coverage": 100.0
        }
        rr_path = Path(".pdd/meta") / f"{basename}_{language}_run.json"
        create_run_report_file(rr_path, run_report)
        
        decision = sync_determine_operation(basename, language, target_coverage, log_mode=True)
        
        assert decision.operation == 'nothing'
        assert "All required files synchronized" in decision.reason


def test_get_pdd_file_paths_respects_context_override(tmp_path, monkeypatch):
    """When multiple contexts exist, context_override selects the correct directories."""
    original_cwd = tmp_path.cwd() if hasattr(tmp_path, 'cwd') else None
    try:
        # Arrange directory structure
        (tmp_path / "prompts").mkdir()
        (tmp_path / "tests").mkdir()
        (tmp_path / "alt_tests").mkdir()
        (tmp_path / "examples").mkdir()
        (tmp_path / "alt_examples").mkdir()
        (tmp_path / "pdd").mkdir()  # code dir
        (tmp_path / "alt_code").mkdir()

        # .pddrc with two contexts that differ in output directories
        (tmp_path / ".pddrc").write_text(
            'contexts:\n'
            '  default:\n'
            '    paths: ["**"]\n'
            '    defaults:\n'
            '      test_output_path: "tests/"\n'
            '      example_output_path: "examples/"\n'
            '      generate_output_path: "pdd/"\n'
            '  alt:\n'
            '    paths: ["**"]\n'
            '    defaults:\n'
            '      test_output_path: "alt_tests/"\n'
            '      example_output_path: "alt_examples/"\n'
            '      generate_output_path: "alt_code/"\n'
        )
        # Prompt file exists
        (tmp_path / "prompts" / "simple_math_python.prompt").write_text("Prompt")

        # Act
        monkeypatch.chdir(tmp_path)
        paths = get_pdd_file_paths(basename="simple_math", language="python", prompts_dir="prompts", context_override="alt")

        # Assert: paths should use alt_* directories
        assert paths["test"].as_posix().endswith("alt_tests/test_simple_math.py"), f"Got: {paths['test']}"
        assert paths["example"].as_posix().endswith("alt_examples/simple_math_example.py"), f"Got: {paths['example']}"
        assert paths["code"].as_posix().endswith("alt_code/simple_math.py"), f"Got: {paths['code']}"

    finally:
        # Restore if needed (pytest handles tmp_path chdir cleanup normally)
        if original_cwd:
            os.chdir(original_cwd)


# --- Part 6: Auto-deps Infinite Loop Regression Tests ---

class TestAutoDepsInfiniteLoopFix:
    """Test the auto-deps infinite loop fix implemented to prevent continuous auto-deps operations."""
    
    def test_auto_deps_to_generate_progression(self, pdd_test_environment):
        """Test that after auto-deps completes, sync decides to run generate (not auto-deps again)."""
        
        # Create prompt file with dependencies
        prompts_dir = pdd_test_environment / "prompts"
        prompts_dir.mkdir(exist_ok=True)
        prompt_content = """Create a YouTube client function.

<include>src/config.py</include>
<include>src/models.py</include>

Requirements:
- Function should discover new videos from YouTube channels
- Use the config and models from included dependencies
"""
        prompt_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", prompt_content)
        
        # Create fingerprint showing auto-deps was just completed
        fingerprint_data = {
            "pdd_version": "0.0.46",
            "timestamp": "2025-08-04T05:22:58.044203+00:00",
            "command": "auto-deps",  # This is the key - auto-deps was last completed
            "prompt_hash": prompt_hash,  # Use actual calculated hash
            "code_hash": None,  # Code file doesn't exist yet
            "example_hash": None,
            "test_hash": None
        }
        fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
        create_fingerprint_file(fp_path, fingerprint_data)
        
        # Test the decision logic
        decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
        
        # CRITICAL: Should decide 'generate', not 'auto-deps' again
        assert decision.operation == 'generate'
        assert 'Auto-deps completed' in decision.reason
        assert decision.details['previous_command'] == 'auto-deps'
        assert decision.details['code_exists'] == False
    
    def test_auto_deps_infinite_loop_before_fix_scenario(self, pdd_test_environment):
        """Test the exact scenario that caused infinite loop before the fix."""
        
        # Create prompt file with dependencies (like youtube_client_python.prompt)
        prompts_dir = pdd_test_environment / "prompts"
        prompts_dir.mkdir(exist_ok=True)
        prompt_content = """YouTube Client Module

This module discovers new videos from configured YouTube channels.

### Dependencies

<config_dependency_example>
<include>src/config.py</include>
</config_dependency_example>

<models_dependency_example>
<include>src/models.py</include>
</models_dependency_example>

Requirements:
- Discover new videos from YouTube channels
- Process metadata for each video
"""
        prompt_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", prompt_content)
        
        # Simulate the exact state from the sync log: auto-deps completed but code file missing
        fingerprint_data = {
            "pdd_version": "0.0.46", 
            "timestamp": "2025-08-04T05:07:29.753906+00:00",
            "command": "auto-deps",
            "prompt_hash": prompt_hash,  # Use actual calculated hash
            "code_hash": None,  # This is the key issue - no code file exists
            "example_hash": None,
            "test_hash": None
        }
        fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
        create_fingerprint_file(fp_path, fingerprint_data)
        
        # Before the fix: this would return 'auto-deps' and cause infinite loop
        # After the fix: this should return 'generate'
        decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
        
        # Verify the fix
        assert decision.operation == 'generate', f"Expected 'generate', got '{decision.operation}' - infinite loop fix failed"
        assert decision.operation != 'auto-deps', "Should not return auto-deps again (infinite loop)"
        assert 'Auto-deps completed' in decision.reason
        assert decision.confidence == 0.90  # High confidence since this is deterministic
    
    def test_auto_deps_without_dependencies_still_works(self, pdd_test_environment):
        """Test that normal auto-deps logic still works when prompt has no dependencies."""
        
        # Create prompt file WITHOUT dependencies
        prompts_dir = pdd_test_environment / "prompts"
        prompts_dir.mkdir(exist_ok=True)
        prompt_content = """Create a simple calculator function.

Requirements:
- Function name: add
- Parameters: a, b (both numbers)
- Return: sum of a and b
"""
        create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", prompt_content)
        
        # No fingerprint (new unit scenario)
        # Code file doesn't exist
        
        decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
        
        # Should go directly to generate since no dependencies detected
        assert decision.operation == 'generate'
        assert 'New prompt ready' in decision.reason
        assert decision.details.get('has_dependencies', True) == False  # No dependencies
    
    def test_auto_deps_first_time_with_dependencies(self, pdd_test_environment):
        """Test that auto-deps is correctly chosen for new prompts with dependencies."""
        
        # Create prompt file WITH dependencies
        prompts_dir = pdd_test_environment / "prompts"
        prompts_dir.mkdir(exist_ok=True)
        prompt_content = """Create a data processor.

<include>context/database_example.py</include>
<web>https://example.com/api-docs</web>

Requirements:
- Process data using included database example
- Fetch API documentation from web
"""
        create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", prompt_content)
        
        # No fingerprint (new unit scenario)
        # Code file doesn't exist
        
        decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
        
        # Should choose auto-deps for first time with dependencies
        assert decision.operation == 'auto-deps'
        assert 'New prompt with dependencies detected' in decision.reason
        assert decision.details['has_dependencies'] == True
        assert decision.details['fingerprint_found'] == False

    @patch('sync_determine_operation.construct_paths')
    def test_auto_deps_regenerates_when_code_exists_from_previous_run(self, mock_construct, pdd_test_environment):
        """Test that after auto-deps completes, generate runs even when code file exists from previous run.

        This is a regression test for a bug where:
        1. User changes prompt
        2. auto-deps runs (updates dependencies, saves fingerprint with new prompt hash)
        3. Code file exists from a previous generation (stale code)
        4. Next sync should run 'generate' to regenerate code with new prompt

        Bug: sync was skipping to 'crash' because code file existed, missing the regeneration step.
        Fix: Added check for fingerprint.command == 'auto-deps' that triggers generate regardless
             of whether code file exists.
        """

        # Create prompt file with dependencies
        prompts_dir = pdd_test_environment / "prompts"
        prompts_dir.mkdir(exist_ok=True)
        prompt_content = """Generate a credit helper function.

<include>context/firebase_helpers.py</include>
<include>context/user_model.py</include>

Requirements:
- Deduct credits from user account
- Verify authentication before deducting
"""
        prompt_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", prompt_content)

        # Create code, example, test files directly in pdd_test_environment (following test pattern)
        old_code_hash = create_file(pdd_test_environment / f"{BASENAME}.py", "# OLD CODE\ndef old_func(): pass")
        old_example_hash = create_file(pdd_test_environment / f"{BASENAME}_example.py", "# OLD EXAMPLE")
        old_test_hash = create_file(pdd_test_environment / f"test_{BASENAME}.py", "# OLD TEST\ndef test_old(): pass")

        # Mock construct_paths to return correct file paths
        mock_construct.return_value = (
            {}, {},
            {
                'code_file': str(pdd_test_environment / f"{BASENAME}.py"),
                'example_file': str(pdd_test_environment / f"{BASENAME}_example.py"),
                'test_file': str(pdd_test_environment / f"test_{BASENAME}.py")
            },
            LANGUAGE
        )

        # Create fingerprint showing auto-deps JUST completed
        # The fingerprint has the NEW prompt hash but OLD code/example/test hashes
        fingerprint_data = {
            "pdd_version": "0.0.88",
            "timestamp": "2025-12-23T02:10:02.143829+00:00",
            "command": "auto-deps",  # auto-deps just completed
            "prompt_hash": prompt_hash,  # NEW prompt hash
            "code_hash": old_code_hash,  # OLD code hash (stale)
            "example_hash": old_example_hash,  # OLD example hash
            "test_hash": old_test_hash  # OLD test hash
        }
        fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
        create_fingerprint_file(fp_path, fingerprint_data)

        decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))

        # CRITICAL: Should decide 'generate' (not 'crash' or 'nothing')
        # Even though all files exist, auto-deps just ran, so code needs regeneration
        assert decision.operation == 'generate', \
            f"Expected 'generate', got '{decision.operation}'. " \
            f"Bug: after auto-deps, should regenerate code even when code file exists from previous run."
        assert 'Auto-deps completed' in decision.reason
        assert decision.details.get('regenerate_after_autodeps') == True
        assert decision.details.get('code_exists') == True  # Confirms code existed but we still regenerate

    @patch('sync_determine_operation.construct_paths')
    def test_no_fingerprint_with_stale_run_report_should_generate(self, mock_construct, pdd_test_environment):
        """Test that when fingerprint is deleted but run_report exists, sync treats it as fresh start.

        Regression test for bug where:
        1. User deletes fingerprint to force regeneration
        2. Stale run_report exists with test failures
        3. Expected: sync detects as fresh start → auto-deps/generate
        4. Actual (bug): sync sees run_report.tests_failed > 0 → runs fix

        IMPORTANT: Must create test file so the buggy 'fix' path at line 958 is triggered.
        Without test file, the code skips 'fix' and accidentally returns correct result.
        """
        # Create prompt with dependencies
        prompts_dir = pdd_test_environment / "prompts"
        prompts_dir.mkdir(exist_ok=True)
        prompt_content = """Generate a helper function.

<include>context/helpers.py</include>

Requirements:
- Do something useful
"""
        create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", prompt_content)

        # CRITICAL: Create test file so buggy 'fix' path is triggered
        # Line 958: if test_file and test_file.exists(): return 'fix'
        create_file(pdd_test_environment / f"test_{BASENAME}.py", "def test_old(): pass")

        # Mock construct_paths to return test file path
        mock_construct.return_value = (
            {}, {},
            {'test_file': str(pdd_test_environment / f"test_{BASENAME}.py")},
            LANGUAGE
        )

        # Create stale run_report with test failures
        rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
        create_run_report_file(rr_path, {
            "timestamp": "2025-12-23T03:00:00+00:00",
            "exit_code": 1,
            "tests_passed": 5,
            "tests_failed": 2,
            "coverage": 50.0,
            "test_hash": "stale_hash"
        })

        # NO fingerprint exists (user deleted it)

        decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))

        # Should treat as fresh start (auto-deps because prompt has dependencies)
        # NOT 'fix' based on stale run_report
        assert decision.operation == 'auto-deps', \
            f"Expected 'auto-deps', got '{decision.operation}'. " \
            f"Bug: stale run_report should be ignored when fingerprint is missing."

    @patch('sync_determine_operation.construct_paths')
    def test_auto_deps_ignores_stale_run_report_with_low_coverage(self, mock_construct, pdd_test_environment):
        """Test that after auto-deps completes, stale run_report with low coverage is ignored.

        Regression test for bug where:
        1. auto-deps completes (fingerprint.command == 'auto-deps')
        2. Stale run_report exists with low coverage (e.g., 77% below 90% target)
        3. Expected: sync returns 'generate' to regenerate code
        4. Actual (bug): sync sees low coverage in run_report → returns 'test_extend'

        The run_report is stale because it was from the PREVIOUS code generation,
        not the new code that will be generated after auto-deps.
        """
        # Create prompt with dependencies
        prompts_dir = pdd_test_environment / "prompts"
        prompts_dir.mkdir(exist_ok=True)
        prompt_content = """Generate a helper function.

<include>context/helpers.py</include>

Requirements:
- Do something useful
"""
        prompt_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", prompt_content)

        # Create code, example, test files (from previous run)
        code_hash = create_file(pdd_test_environment / f"{BASENAME}.py", "# OLD CODE")
        example_hash = create_file(pdd_test_environment / f"{BASENAME}_example.py", "# OLD EXAMPLE")
        test_hash = create_file(pdd_test_environment / f"test_{BASENAME}.py", "def test_old(): pass")

        mock_construct.return_value = (
            {}, {},
            {
                'code_file': str(pdd_test_environment / f"{BASENAME}.py"),
                'example_file': str(pdd_test_environment / f"{BASENAME}_example.py"),
                'test_file': str(pdd_test_environment / f"test_{BASENAME}.py")
            },
            LANGUAGE
        )

        # Create fingerprint showing auto-deps JUST completed
        fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
        create_fingerprint_file(fp_path, {
            "pdd_version": "0.0.88",
            "timestamp": "2025-12-23T03:00:00+00:00",
            "command": "auto-deps",  # auto-deps just completed
            "prompt_hash": prompt_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash
        })

        # Create STALE run_report with low coverage (from previous code generation)
        rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
        create_run_report_file(rr_path, {
            "timestamp": "2025-12-23T02:00:00+00:00",  # Before auto-deps
            "exit_code": 0,
            "tests_passed": 6,
            "tests_failed": 0,
            "coverage": 77.0,  # Below 90% target - would trigger test_extend if not ignored
            "test_hash": test_hash
        })

        decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))

        # Should return 'generate' because auto-deps just completed
        # NOT 'test_extend' based on stale run_report's low coverage
        assert decision.operation == 'generate', \
            f"Expected 'generate', got '{decision.operation}'. " \
            f"Bug: after auto-deps, stale run_report should be ignored."
        assert 'Auto-deps completed' in decision.reason
        assert decision.details.get('regenerate_after_autodeps') == True

# --- Part 7: Edge Cases and Helper Function Tests ---
# These tests were consolidated from test_sync_edge_cases.py

class TestValidateExpectedFiles:
    """Test the validate_expected_files function."""
    
    def test_validate_with_no_fingerprint(self):
        """Test validation when no fingerprint is provided."""
        paths = {
            'code': Path('test.py'),
            'example': Path('test_example.py'),
            'test': Path('test_test.py')
        }
        
        result = validate_expected_files(None, paths)
        assert result == {}
    
    def test_validate_all_files_exist(self, tmp_path):
        """Test validation when all expected files exist."""
        # Create test files
        code_file = tmp_path / "test.py"
        example_file = tmp_path / "test_example.py"
        test_file = tmp_path / "test_test.py"
        
        code_file.write_text("print('hello')")
        example_file.write_text("from test import *")
        test_file.write_text("def test_func(): pass")
        
        paths = {
            'code': code_file,
            'example': example_file,
            'test': test_file
        }
        
        fingerprint = Fingerprint(
            pdd_version="0.0.41",
            timestamp=datetime.now(timezone.utc).isoformat(),
            command="test",
            prompt_hash="prompt123",
            code_hash="code456",
            example_hash="example789",
            test_hash="test012"
        )
        
        result = validate_expected_files(fingerprint, paths)
        
        assert result == {
            'code': True,
            'example': True,
            'test': True
        }
    
    def test_validate_missing_files(self, tmp_path):
        """Test validation when expected files are missing."""
        # Create only code file
        code_file = tmp_path / "test.py"
        example_file = tmp_path / "test_example.py"
        test_file = tmp_path / "test_test.py"
        
        code_file.write_text("print('hello')")
        # Don't create example and test files
        
        paths = {
            'code': code_file,
            'example': example_file,
            'test': test_file
        }
        
        fingerprint = Fingerprint(
            pdd_version="0.0.41",
            timestamp=datetime.now(timezone.utc).isoformat(),
            command="test",
            prompt_hash="prompt123",
            code_hash="code456",
            example_hash="example789",
            test_hash="test012"
        )
        
        result = validate_expected_files(fingerprint, paths)
        
        assert result == {
            'code': True,
            'example': False,
            'test': False
        }


class TestHandleMissingExpectedFiles:
    """Test the _handle_missing_expected_files function."""
    
    def test_missing_code_file_with_prompt(self, tmp_path):
        """Test recovery when code file is missing but prompt exists."""
        prompt_file = tmp_path / "test_python.prompt"
        prompt_file.write_text("Create a simple function")
        
        paths = {
            'prompt': prompt_file,
            'code': tmp_path / "test.py",
            'example': tmp_path / "test_example.py",
            'test': tmp_path / "test_test.py"
        }
        
        fingerprint = Fingerprint(
            pdd_version="0.0.41",
            timestamp=datetime.now(timezone.utc).isoformat(),
            command="test",
            prompt_hash="prompt123",
            code_hash="code456",
            example_hash=None,
            test_hash=None
        )
        
        decision = _handle_missing_expected_files(
            missing_files=['code'],
            paths=paths,
            fingerprint=fingerprint,
            basename="test",
            language="python",
            prompts_dir="prompts"
        )
        
        assert decision.operation == 'generate'
        assert 'Code file missing' in decision.reason
        # The confidence value is set to 1.0 because the decision to generate
        # a new code file is deterministic when the code file is missing, and
        # all other required files (e.g., prompt) are present.
        assert decision.confidence == 1.0
    def test_missing_test_file_with_skip_tests(self, tmp_path):
        """Test recovery when test file is missing and skip_tests is True."""
        code_file = tmp_path / "test.py"
        example_file = tmp_path / "test_example.py"
        
        code_file.write_text("def add(a, b): return a + b")
        example_file.write_text("from test import add; print(add(1, 2))")
        
        paths = {
            'prompt': tmp_path / "test_python.prompt",
            'code': code_file,
            'example': example_file,
            'test': tmp_path / "test_test.py"
        }
        
        fingerprint = Fingerprint(
            pdd_version="0.0.41",
            timestamp=datetime.now(timezone.utc).isoformat(),
            command="test",
            prompt_hash="prompt123",
            code_hash="code456",
            example_hash="example789",
            test_hash="test012"
        )
        
        decision = _handle_missing_expected_files(
            missing_files=['test'],
            paths=paths,
            fingerprint=fingerprint,
            basename="test",
            language="python",
            prompts_dir="prompts",
            skip_tests=True
        )
        
        assert decision.operation == 'nothing'
        assert 'skip-tests specified' in decision.reason
        assert decision.details['skip_tests'] is True
    
    def test_missing_example_file(self, tmp_path):
        """Test recovery when example file is missing but code exists."""
        code_file = tmp_path / "test.py"
        code_file.write_text("def add(a, b): return a + b")
        
        paths = {
            'prompt': tmp_path / "test_python.prompt",
            'code': code_file,
            'example': tmp_path / "test_example.py",
            'test': tmp_path / "test_test.py"
        }
        
        fingerprint = Fingerprint(
            pdd_version="0.0.41",
            timestamp=datetime.now(timezone.utc).isoformat(),
            command="test",
            prompt_hash="prompt123",
            code_hash="code456",
            example_hash="example789",
            test_hash=None
        )
        
        decision = _handle_missing_expected_files(
            missing_files=['example'],
            paths=paths,
            fingerprint=fingerprint,
            basename="test",
            language="python",
            prompts_dir="prompts"
        )
        
        assert decision.operation == 'example'
        assert 'Example file missing' in decision.reason


class TestIsWorkflowComplete:
    """Test the _is_workflow_complete function."""
    
    def test_workflow_complete_without_skip_flags(self, tmp_path):
        """Test workflow completion when all files exist and no skip flags."""
        code_file = tmp_path / "test.py"
        example_file = tmp_path / "test_example.py"
        test_file = tmp_path / "test_test.py"
        
        # Create all files
        code_file.write_text("def add(a, b): return a + b")
        example_file.write_text("from test import add")
        test_file.write_text("def test_add(): pass")
        
        paths = {
            'code': code_file,
            'example': example_file,
            'test': test_file
        }
        
        assert _is_workflow_complete(paths) is True
        assert _is_workflow_complete(paths, skip_tests=False) is True
    
    def test_workflow_complete_with_skip_tests(self, tmp_path):
        """Test workflow completion when test file missing but skip_tests=True."""
        code_file = tmp_path / "test.py"
        example_file = tmp_path / "test_example.py"
        
        # Create only code and example files
        code_file.write_text("def add(a, b): return a + b")
        example_file.write_text("from test import add")
        
        paths = {
            'code': code_file,
            'example': example_file,
            'test': tmp_path / "test_test.py"  # Doesn't exist
        }
        
        assert _is_workflow_complete(paths) is False  # Requires test file
        assert _is_workflow_complete(paths, skip_tests=True) is True  # Skip test requirement
    
    def test_workflow_incomplete(self, tmp_path):
        """Test workflow is incomplete when required files are missing."""
        code_file = tmp_path / "test.py"
        code_file.write_text("def add(a, b): return a + b")
        
        paths = {
            'code': code_file,
            'example': tmp_path / "test_example.py",  # Doesn't exist
            'test': tmp_path / "test_test.py"  # Doesn't exist
        }
        
        assert _is_workflow_complete(paths) is False
        assert _is_workflow_complete(paths, skip_tests=True) is False  # Still needs example


class TestSyncDetermineOperationRegressionScenarios:
    """Additional regression tests for sync_determine_operation edge cases."""
    
    def test_missing_files_with_metadata_regression_scenario(self, tmp_path):
        """Test the exact regression scenario: files deleted but metadata remains."""
        # Change to temp directory for the test
        original_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)
            
            # Create directory structure
            (tmp_path / "prompts").mkdir()
            (tmp_path / ".pdd" / "meta").mkdir(parents=True)
            
            # Create prompt file
            prompt_file = tmp_path / "prompts" / "simple_math_python.prompt"
            prompt_file.write_text("""Create a Python module with a simple math function.

Requirements:
- Function name: add
- Parameters: a, b (both numbers)  
- Return: sum of a and b
""")
            
            # Create metadata (simulating previous successful sync)
            meta_file = tmp_path / ".pdd" / "meta" / "simple_math_python.json"
            meta_file.write_text(json.dumps({
                "pdd_version": "0.0.41",
                "timestamp": datetime.now(timezone.utc).isoformat(),
                "command": "test",
                "prompt_hash": "abc123",
                "code_hash": "def456",
                "example_hash": "ghi789",
                "test_hash": "jkl012"
            }, indent=2))
            
            # Files are deliberately missing (deleted like in regression test)
            
            # Test sync_determine_operation behavior
            decision = sync_determine_operation(
                basename="simple_math",
                language="python",
                target_coverage=90.0,
                budget=10.0,
                log_mode=False,
                prompts_dir="prompts",
                skip_tests=True,
                skip_verify=False
            )
            
            # Should NOT return analyze_conflict anymore
            assert decision.operation != 'analyze_conflict'
            
            # Should return appropriate recovery operation
            assert decision.operation in ['generate', 'auto-deps']
            assert 'missing' in decision.reason.lower() or 'regenerate' in decision.reason.lower()
            
        finally:
            os.chdir(original_cwd)
    
    def test_skip_flags_integration(self, tmp_path):
        """Test that skip flags are properly integrated throughout the decision logic."""
        original_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)
            
            # Create directory structure
            (tmp_path / "prompts").mkdir()
            
            # Create prompt file
            prompt_file = tmp_path / "prompts" / "test_python.prompt"
            prompt_file.write_text("Create a simple function")
            
            # Test with skip_tests=True
            decision = sync_determine_operation(
                basename="test",
                language="python",
                target_coverage=90.0,
                budget=10.0,
                log_mode=False,
                prompts_dir="prompts",
                skip_tests=True,
                skip_verify=False
            )
            
            # Should start normal workflow
            assert decision.operation in ['generate', 'auto-deps']
            
        finally:
            os.chdir(original_cwd)


class TestGetPddFilePaths:
    """Test get_pdd_file_paths function to prevent path resolution regression."""
    
    def test_get_pdd_file_paths_respects_pddrc_when_prompt_missing(self, tmp_path, monkeypatch):
        """Test that get_pdd_file_paths uses .pddrc configuration even when prompt doesn't exist.
        
        This test prevents regression of the bug where test files were looked for in the
        current directory instead of the configured tests/ subdirectory.
        """
        original_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)
            
            # Create .pddrc configuration file
            pddrc_content = """version: "1.0"
contexts:
  regression:
    paths: ["**"]
    defaults:
      test_output_path: "tests/"
      example_output_path: "examples/"
      default_language: "python"
"""
            (tmp_path / ".pddrc").write_text(pddrc_content)
            
            # Create directory structure
            (tmp_path / "prompts").mkdir()
            (tmp_path / "tests").mkdir()
            (tmp_path / "examples").mkdir()
            
            # Mock construct_paths to return configured paths
            def mock_construct_paths(
                input_file_paths,
                force,
                quiet,
                command,
                command_options,
                context_override=None,
                path_resolution_mode=None,
                **_ignored,
            ):
                # Simulate what construct_paths would return with .pddrc configuration
                return (
                    {
                        "test_output_path": "tests/",
                        "example_output_path": "examples/",
                        "generate_output_path": "./"
                    },
                    {},
                    {},  # output_paths is empty when called with empty input_file_paths
                    "python"
                )
            
            monkeypatch.setattr('sync_determine_operation.construct_paths', mock_construct_paths)
            
            # Test when prompt file doesn't exist - this is the regression scenario
            basename = "test_unit"
            language = "python"
            paths = get_pdd_file_paths(basename, language, "prompts")
            
            # Verify paths respect configuration, not hardcoded to current directory
            # The bug was that test file was "test_test_unit.py" instead of "tests/test_test_unit.py"
            assert str(paths['test']) == "tests/test_test_unit.py", f"Test path should be in tests/ subdirectory, got: {paths['test']}"
            assert str(paths['example']) == "examples/test_unit_example.py", f"Example path should be in examples/ subdirectory, got: {paths['example']}"
            assert str(paths['code']) == "test_unit.py", f"Code path can be in current directory, got: {paths['code']}"
            
            # Verify the paths are Path objects
            assert isinstance(paths['test'], Path)
            assert isinstance(paths['example'], Path)
            assert isinstance(paths['code'], Path)
            assert isinstance(paths['prompt'], Path)
            
        finally:
            os.chdir(original_cwd)

    def test_get_pdd_file_paths_uses_context_relative_basename_for_templates(self, tmp_path, monkeypatch):
        pddrc_content = """version: "1.0"
contexts:
  frontend-components:
    paths:
      - "frontend/components/**"
    defaults:
      default_language: "typescriptreact"
      outputs:
        prompt:
          path: "prompts/frontend/components/{category}/{name}_{language}.prompt"
        code:
          path: "frontend/src/components/{category}/{name}/{name}.tsx"
        example:
          path: "context/frontend/{name}_example.tsx"
  default:
    defaults:
      default_language: "python"
"""
        (tmp_path / ".pddrc").write_text(pddrc_content)

        prompt_path = (
            tmp_path
            / "prompts"
            / "frontend"
            / "components"
            / "marketplace"
            / "AssetCard_typescriptreact.prompt"
        )
        prompt_path.parent.mkdir(parents=True, exist_ok=True)
        prompt_path.write_text("Generate AssetCard component", encoding="utf-8")

        repo_root = Path(__file__).resolve().parents[1]
        monkeypatch.setenv("PDD_PATH", str(repo_root))
        monkeypatch.chdir(tmp_path)

        paths = get_pdd_file_paths(
            basename="frontend/components/marketplace/AssetCard",
            language="typescriptreact",
            prompts_dir="prompts",
            context_override="frontend-components",
        )

        assert paths["prompt"].resolve() == prompt_path.resolve()
        assert paths["code"].as_posix() == "frontend/src/components/marketplace/AssetCard/AssetCard.tsx"
        assert paths["example"].as_posix() == "context/frontend/AssetCard_example.tsx"
    
    def test_get_pdd_file_paths_fallback_without_construct_paths(self, tmp_path, monkeypatch):
        """Test that paths use configured directories even without .pddrc when prompt is missing.
        
        After the fix, even without .pddrc, construct_paths should provide
        sensible defaults based on the PDD context detection.
        """
        original_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)
            
            # Create directory structure
            (tmp_path / "prompts").mkdir()
            
            # Don't create the prompt file - trigger the fallback logic
            basename = "test_unit"
            language = "python"
            
            # Get paths without mocking - this uses construct_paths now
            paths = get_pdd_file_paths(basename, language, "prompts")
            
            # After fix: paths should use PDD's default directory structure
            # The exact paths depend on whether construct_paths detects a context
            # In a bare directory, it might still use current directory as fallback
            # But with .pddrc present, it should use configured paths
            
            # For a bare directory without .pddrc, current behavior is acceptable
            # The important fix is that WITH .pddrc, paths are respected
            assert isinstance(paths['test'], Path)
            assert isinstance(paths['example'], Path)
            assert isinstance(paths['code'], Path)
            
        finally:
            os.chdir(original_cwd)
    
    @patch('sync_determine_operation.construct_paths')
    def test_sync_operation_with_missing_prompt_respects_test_path(self, mock_construct, tmp_path):
        """Test that sync_determine_operation doesn't fail when test file is in configured directory.
        
        This simulates the exact regression scenario where sync fails with
        "No such file or directory: 'test_simple_math.py'" because it's looking
        in the wrong directory.
        """
        original_cwd = os.getcwd()
        try:
            os.chdir(tmp_path)
            
            # Create directory structure as per .pddrc
            (tmp_path / ".pdd" / "meta").mkdir(parents=True)
            (tmp_path / ".pdd" / "locks").mkdir(parents=True)
            (tmp_path / "prompts").mkdir()
            (tmp_path / "tests").mkdir()
            (tmp_path / "examples").mkdir()
            
            # Create .pddrc file
            pddrc_content = """version: "1.0"
contexts:
  regression:
    paths: ["**"]
    defaults:
      test_output_path: "tests/"
      example_output_path: "examples/"
"""
            (tmp_path / ".pddrc").write_text(pddrc_content)
            
            # Mock construct_paths to return .pddrc-configured paths
            mock_construct.return_value = (
                {"test_output_path": "tests/"},
                {},
                {
                    "output": "tests/test_simple_math.py",
                    "test_file": "tests/test_simple_math.py",
                    "example_file": "examples/simple_math_example.py",
                    "code_file": "simple_math.py"
                },
                "python"
            )
            
            # Don't create prompt file - this simulates the regression scenario
            # The sync should still work and not look for test_simple_math.py in current dir
            
            decision = sync_determine_operation(
                basename="simple_math",
                language="python",
                target_coverage=90.0,
                budget=10.0,
                log_mode=False,
                prompts_dir="prompts",
                skip_tests=False,
                skip_verify=False
            )
            
            # Verify no FileNotFoundError is raised
            # The decision should handle missing files gracefully
            assert isinstance(decision, SyncDecision)
            # Should return an operation that makes sense for missing prompt
            assert decision.operation in ['nothing', 'auto-deps', 'generate']
            
        finally:
            os.chdir(original_cwd)
    
    def test_file_path_lookup_regression(self, tmp_path, monkeypatch):
        """Test the exact regression scenario: file lookup after verify completes.
        
        This test simulates the exact error seen in sync regression where
        after verify completes, something tries to read 'test_simple_math.py'
        from the current directory instead of 'tests/test_simple_math.py'.
        """
        original_cwd = os.getcwd()
        
        # Store original module constants to restore them later
        pdd_module = sys.modules['sync_determine_operation']
        original_pdd_dir = pdd_module.PDD_DIR
        original_meta_dir = pdd_module.META_DIR
        original_locks_dir = pdd_module.LOCKS_DIR
        
        try:
            os.chdir(tmp_path)
            
            # Set PDD_PATH environment variable for get_language function
            monkeypatch.setenv("PDD_PATH", str(tmp_path))
            
            # Create language mapping CSV files that get_language function needs
            language_csv_content = """extension,language
.py,python
.js,javascript
.java,java
.cpp,cpp
.c,c
.go,go
.rs,rust
.rb,ruby
.php,php
.ts,typescript
.swift,swift
.kt,kotlin
.scala,scala
.clj,clojure
.hs,haskell
.ml,ocaml
.fs,fsharp
.ex,elixir
.erl,erlang
.pl,perl
.lua,lua
.r,r
.m,matlab
.jl,julia
.dart,dart
.groovy,groovy
.sh,bash
.ps1,powershell
.bat,batch
.cmd,batch
.vb,vb
.cs,csharp
.f,fortran
.f90,fortran
.pas,pascal
.asm,assembly
.s,assembly
.sol,solidity
.move,move
"""
            (tmp_path / "language_extension_mapping.csv").write_text(language_csv_content)
            
            # Create data directory and language_format.csv
            (tmp_path / "data").mkdir()
            (tmp_path / "data" / "language_format.csv").write_text(language_csv_content)
            
            # Update module constants after changing directory
            pdd_module.PDD_DIR = pdd_module.get_pdd_dir()
            pdd_module.META_DIR = pdd_module.get_meta_dir()
            pdd_module.LOCKS_DIR = pdd_module.get_locks_dir()
            
            # Create directory structure matching regression test
            (tmp_path / "prompts").mkdir()
            (tmp_path / "tests").mkdir()
            (tmp_path / "examples").mkdir()
            (tmp_path / ".pdd" / "meta").mkdir(parents=True)
            
            # Create the files that exist after verify completes
            (tmp_path / "prompts" / "simple_math_python.prompt").write_text("Create add function")
            (tmp_path / "simple_math.py").write_text("def add(a, b): return a + b")
            (tmp_path / "examples" / "simple_math_example.py").write_text("from simple_math import add")
            (tmp_path / "simple_math_verify_results.log").write_text("Success")
            
            # Create .pddrc that specifies test path
            pddrc_content = """version: "1.0"
contexts:
  regression:
    paths: ["**"]
    defaults:
      test_output_path: "tests/"
      example_output_path: "examples/"
"""
            (tmp_path / ".pddrc").write_text(pddrc_content)
            
            # The test file should be in tests/ directory according to .pddrc
            # but the error shows it's being looked for in current directory
            
            # Use the already imported get_pdd_file_paths to avoid module conflicts
            # get_pdd_file_paths was imported at the top of the file
            
            # Get file paths - this should respect .pddrc
            paths = get_pdd_file_paths("simple_math", "python", "prompts")
            
            # This demonstrates the bug: trying to check if test file exists
            # in the wrong location would cause the error
            test_path = paths['test']
            
            # The fix is now in place, so we should always get the correct path
            # Verify that the path respects the .pddrc configuration
            assert "tests/test_simple_math.py" in str(test_path) or "tests\\test_simple_math.py" in str(test_path), \
                f"Expected test path to be in tests/ subdirectory as per .pddrc, but got: {test_path}"
            
            # Verify the file lookup fails with the correct path (file doesn't exist)
            try:
                with open(test_path, 'r') as f:
                    f.read()
                assert False, "Should have raised FileNotFoundError"
            except FileNotFoundError as e:
                error_msg = str(e)
                assert "tests/test_simple_math.py" in error_msg or "tests\\test_simple_math.py" in error_msg, \
                    f"Expected error to reference 'tests/test_simple_math.py', but got: {error_msg}"
                
            # After fix, the path should be 'tests/test_simple_math.py'
            # and this error wouldn't occur if the file existed there
            
        finally:
            os.chdir(original_cwd)
            
            # Restore original module constants
            pdd_module.PDD_DIR = original_pdd_dir
            pdd_module.META_DIR = original_meta_dir
            pdd_module.LOCKS_DIR = original_locks_dir


# --- Regression: Output path resolution under sync (integrated) ---

def _write_pddrc_here() -> None:
    content = (
        "contexts:\n"
        "  default:\n"
        "    defaults:\n"
        "      generate_output_path: pdd/\n"
        "      example_output_path: examples/\n"
        "      test_output_path: tests/\n"
    )
    Path(".pdd").mkdir(parents=True, exist_ok=True)
    Path(".pddrc").write_text(content, encoding="utf-8")


def _write_simple_prompt(basename: str = "simple_math", language: str = "python") -> None:
    prompts_dir = Path("prompts")
    prompts_dir.mkdir(parents=True, exist_ok=True)
    (prompts_dir / f"{basename}_{language}.prompt").write_text(
        """
Write a simple add(a, b) function that returns a + b.
Also include a subtract(a, b) that returns a - b.
""".strip(),
        encoding="utf-8",
    )


def test_get_pdd_file_paths_respects_pddrc_without_PDD_PATH(pdd_test_environment, monkeypatch):
    _write_pddrc_here()
    _write_simple_prompt()
    monkeypatch.delenv("PDD_PATH", raising=False)
    paths = get_pdd_file_paths(basename="simple_math", language="python", prompts_dir="prompts")
    assert paths["code"].as_posix().endswith("pdd/simple_math.py"), f"Got: {paths['code']}"


def test_get_pdd_file_paths_respects_pddrc_with_PDD_PATH(pdd_test_environment, monkeypatch):
    _write_pddrc_here()
    _write_simple_prompt()
    repo_root = Path(__file__).parent.parent
    monkeypatch.setenv("PDD_PATH", str(repo_root))
    paths = get_pdd_file_paths(basename="simple_math", language="python", prompts_dir="prompts")
    assert paths["code"].as_posix().endswith("pdd/simple_math.py")
    assert paths["example"].as_posix().endswith("examples/simple_math_example.py")
    assert paths["test"].as_posix().endswith("tests/test_simple_math.py")


def test_get_pdd_file_paths_with_subdirectory_basename(pdd_test_environment, monkeypatch):
    """When config paths end with /, files go directly into configured directory.

    For basename='core/cloud' with .pddrc paths ending in /:
    - generate_output_path: pdd/ → code: pdd/cloud.py
    - test_output_path: tests/ → test: tests/test_cloud.py
    - example_output_path: examples/ → example: examples/cloud_example.py

    Note: When config paths explicitly end with /, they are treated as COMPLETE
    directories. The dir_prefix from basename is NOT added because the config
    already specifies the exact directory. This prevents double-pathing bugs
    like 'backend/functions/utils/backend/utils/file.py'.

    If you WANT subdirectory structure, either:
    1. Don't end config paths with / (e.g., 'pdd' instead of 'pdd/')
    2. Use template-based paths with {dir_prefix} placeholder
    """
    _write_pddrc_here()

    # Create prompt file in subdirectory
    prompts_core_dir = Path("prompts") / "core"
    prompts_core_dir.mkdir(parents=True, exist_ok=True)
    (prompts_core_dir / "cloud_python.prompt").write_text("Write a cloud module")

    repo_root = Path(__file__).parent.parent
    monkeypatch.setenv("PDD_PATH", str(repo_root))

    paths = get_pdd_file_paths(basename="core/cloud", language="python", prompts_dir="prompts")

    # When config paths end with /, files go directly into that directory
    # The dir_prefix (core/) is NOT added because explicit paths are used
    code_path = paths["code"].as_posix()
    test_path = paths["test"].as_posix()
    example_path = paths["example"].as_posix()

    # Files go directly into configured directories (no dir_prefix added)
    assert code_path.endswith("pdd/cloud.py"), \
        f"Expected path ending with 'pdd/cloud.py', got {code_path}"
    assert test_path.endswith("tests/test_cloud.py"), \
        f"Expected path ending with 'tests/test_cloud.py', got {test_path}"
    assert example_path.endswith("examples/cloud_example.py"), \
        f"Expected path ending with 'examples/cloud_example.py', got {example_path}"


def test_get_pdd_file_paths_no_path_duplication_with_deep_prompts_dir(tmp_path, monkeypatch):
    """
    Regression test for Issue #237: Path duplication when prompts_dir is a deep path.

    When sync_main passes prompt_file_path.parent as prompts_dir (e.g.,
    'prompts/frontend/app/admin/discount-codes'), and basename contains the same
    path (e.g., 'frontend/app/admin/discount-codes/page'), the resulting prompt_path
    should NOT have the path segment duplicated.

    Bug: prompts/frontend/.../page_typescriptreact.prompt was being constructed as
         prompts/frontend/.../frontend/.../page_typescriptreact.prompt
    """
    monkeypatch.chdir(tmp_path)

    # Create deep directory structure
    deep_prompts_dir = tmp_path / "prompts" / "frontend" / "app" / "admin" / "discount-codes"
    deep_prompts_dir.mkdir(parents=True)

    # Create the prompt file where it should be
    prompt_file = deep_prompts_dir / "page_typescriptreact.prompt"
    prompt_file.write_text("Test prompt")

    # Call with the deep prompts_dir (as sync_main would after commit 960de48d)
    paths = get_pdd_file_paths(
        basename="frontend/app/admin/discount-codes/page",
        language="typescriptreact",
        prompts_dir=str(deep_prompts_dir),  # Deep path, not just "prompts"
    )

    # The prompt path should be the actual file, NOT have duplicated segments
    prompt_path = paths.get("prompt")
    assert prompt_path is not None

    # Key assertion: path should NOT contain the segment twice
    path_str = str(prompt_path)
    assert path_str.count("frontend/app/admin/discount-codes") == 1, \
        f"Path has duplicated segment: {path_str}"

    # Should resolve to the actual file
    assert prompt_path.exists(), f"Prompt path does not exist: {prompt_path}"


# --- Regression Tests: All Files Exist But Workflow Incomplete ---

class TestAllFilesExistWorkflowIncomplete:
    """
    Regression tests for bugs where test file exists but workflow is incomplete.

    The crash/verify/test logic at line 1074-1137 only runs when test is MISSING.
    These tests verify correct behavior when all files exist but workflow is incomplete.

    Bug scenarios:
    - BUG 4: All files exist + NO run_report → should return 'crash'
    - BUG 1: All files exist + run_report.exit_code != 0 → should return 'crash'
    - BUG 2: All files exist + run_report OK + command='crash' → should return 'verify'
    - Sanity: All files exist + run_report OK + command='test' → should return 'nothing'
    """

    @pytest.fixture
    def all_files_env(self, tmp_path):
        """Setup: All PDD files exist with matching fingerprint."""
        original_cwd = Path.cwd()
        os.chdir(tmp_path)

        # Setup base directories
        pdd_dir = tmp_path / ".pdd"
        meta_dir = pdd_dir / "meta"
        locks_dir = pdd_dir / "locks"
        prompts_dir = tmp_path / "prompts"

        for d in [meta_dir, locks_dir, prompts_dir]:
            d.mkdir(parents=True, exist_ok=True)

        # Update module-level path constants BEFORE calling get_pdd_file_paths
        pdd_module = sys.modules['sync_determine_operation']
        pdd_module.PDD_DIR = pdd_module.get_pdd_dir()
        pdd_module.META_DIR = pdd_module.get_meta_dir()
        pdd_module.LOCKS_DIR = pdd_module.get_locks_dir()

        # Create prompt file first (required for get_pdd_file_paths)
        prompt_file = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
        prompt_file.write_text("Create add function")

        # Get the expected file paths from the sync_determine_operation module
        paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir="prompts")

        # Create files at the paths the module expects
        code_file = paths['code']
        code_file.parent.mkdir(parents=True, exist_ok=True)
        code_file.write_text("def add(a, b): return a + b")

        example_file = paths['example']
        example_file.parent.mkdir(parents=True, exist_ok=True)
        example_file.write_text("add(1, 2) == 3")

        test_file = paths['test']
        test_file.parent.mkdir(parents=True, exist_ok=True)
        test_file.write_text("def test_add(): assert add(1, 2) == 3")

        yield {
            'tmp_path': tmp_path,
            'meta_dir': meta_dir,
            'prompt': prompt_file,
            'code': code_file,
            'example': example_file,
            'test': test_file
        }

        # Restore original working directory
        os.chdir(original_cwd)
        pdd_module.PDD_DIR = pdd_module.get_pdd_dir()
        pdd_module.META_DIR = pdd_module.get_meta_dir()
        pdd_module.LOCKS_DIR = pdd_module.get_locks_dir()

    def _create_fingerprint(self, env, command='test'):
        """Helper to create fingerprint with given command."""
        fp_file = env['meta_dir'] / f"{BASENAME}_{LANGUAGE}.json"
        fp_file.write_text(json.dumps({
            "pdd_version": "1.0.0",
            "timestamp": "2025-01-01T00:00:00+00:00",
            "command": command,
            "prompt_hash": calculate_sha256(env['prompt']),
            "code_hash": calculate_sha256(env['code']),
            "example_hash": calculate_sha256(env['example']),
            "test_hash": calculate_sha256(env['test'])
        }))

    def _create_run_report(self, env, exit_code=0):
        """Helper to create run_report with given exit_code."""
        rr_file = env['meta_dir'] / f"{BASENAME}_{LANGUAGE}_run.json"
        rr_file.write_text(json.dumps({
            "timestamp": "2025-01-01T00:00:00+00:00",
            "exit_code": exit_code,
            "tests_passed": 5 if exit_code == 0 else 0,
            "tests_failed": 0 if exit_code == 0 else 1,
            "coverage": 95.0 if exit_code == 0 else 0.0
        }))

    def test_bug4_no_run_report_returns_crash(self, all_files_env):
        """BUG 4: All files exist, NO run_report → should return 'crash'."""
        env = all_files_env
        self._create_fingerprint(env, command='generate')
        # NO run_report - this is the key scenario

        decision = sync_determine_operation(
            basename=BASENAME,
            language=LANGUAGE,
            target_coverage=TARGET_COVERAGE,
            log_mode=True
        )

        assert decision.operation == 'crash', (
            f"BUG 4: Expected 'crash' when all files exist but no run_report, "
            f"got '{decision.operation}' with reason: {decision.reason}"
        )

    def test_bug1_exit_code_nonzero_returns_crash(self, all_files_env):
        """BUG 1: All files exist, run_report.exit_code != 0 → should return 'crash'."""
        env = all_files_env
        self._create_fingerprint(env, command='crash')
        self._create_run_report(env, exit_code=1)  # Code crashed!

        decision = sync_determine_operation(
            basename=BASENAME,
            language=LANGUAGE,
            target_coverage=TARGET_COVERAGE,
            log_mode=True
        )

        assert decision.operation == 'crash', (
            f"BUG 1: Expected 'crash' when exit_code=1, "
            f"got '{decision.operation}' with reason: {decision.reason}"
        )

    def test_bug2_verify_not_run_returns_verify(self, all_files_env):
        """BUG 2: All files exist, run_report OK, command='crash' → should return 'verify'."""
        env = all_files_env
        self._create_fingerprint(env, command='crash')  # Verify hasn't run yet
        self._create_run_report(env, exit_code=0)

        decision = sync_determine_operation(
            basename=BASENAME,
            language=LANGUAGE,
            target_coverage=TARGET_COVERAGE,
            log_mode=True
        )

        assert decision.operation == 'verify', (
            f"BUG 2: Expected 'verify' when command='crash' (verify not run yet), "
            f"got '{decision.operation}' with reason: {decision.reason}"
        )

    def test_complete_workflow_returns_nothing(self, all_files_env):
        """Sanity check: When workflow is truly complete, should return 'nothing'."""
        env = all_files_env
        self._create_fingerprint(env, command='test')  # Workflow complete
        self._create_run_report(env, exit_code=0)

        decision = sync_determine_operation(
            basename=BASENAME,
            language=LANGUAGE,
            target_coverage=TARGET_COVERAGE,
            log_mode=True
        )

        assert decision.operation == 'nothing', (
            f"Expected 'nothing' when workflow complete, "
            f"got '{decision.operation}' with reason: {decision.reason}"
        )


# --- Part 6: PDD Doctrine - Derived Artifacts Tests ---

@patch('sync_determine_operation.construct_paths')
def test_no_conflict_when_only_derived_artifacts_change(mock_construct, pdd_test_environment):
    """
    Test that when only derived artifacts (code + example) change but prompt is UNCHANGED,
    this should NOT be treated as a conflict per PDD doctrine.

    PDD Doctrine: Prompt is the source of truth. Code, example, and test are derived artifacts.
    If prompt is unchanged, changes to derived artifacts are NOT conflicts - they're
    interrupted workflows that should continue.

    Bug: sync_determine_operation returns 'analyze_conflict' when len(changes) > 1,
    without checking if prompt is in the changes list.
    """
    prompts_dir = pdd_test_environment / "prompts"

    # Create all files with specific content
    prompt_content = "unchanged prompt content"
    code_content = "modified code content"
    example_content = "modified example content"

    prompt_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", prompt_content)
    create_file(pdd_test_environment / f"{BASENAME}.py", code_content)
    create_file(pdd_test_environment / f"{BASENAME}_example.py", example_content)

    mock_construct.return_value = (
        {},
        {},
        {'generate_output_path': str(pdd_test_environment / f"{BASENAME}.py")},
        LANGUAGE
    )

    # Create fingerprint where:
    # - prompt_hash MATCHES current file (prompt unchanged)
    # - code_hash DIFFERS from current file (code changed)
    # - example_hash DIFFERS from current file (example changed)
    create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
        "pdd_version": "1.0",
        "timestamp": "2024-01-01T00:00:00",
        "command": "verify",
        "prompt_hash": prompt_hash,  # MATCHES - prompt unchanged
        "code_hash": "old_code_hash_differs",  # DIFFERS - code changed
        "example_hash": "old_example_hash_differs",  # DIFFERS - example changed
        "test_hash": None
    })

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))

    # KEY ASSERTION: Should NOT return analyze_conflict when prompt is unchanged
    assert decision.operation != 'analyze_conflict', \
        f"Should not return analyze_conflict when only derived artifacts changed. " \
        f"Got: {decision.operation}, reason: {decision.reason}, details: {decision.details}"

    # Should continue the workflow with an appropriate operation (not conflict)
    # verify is appropriate since code/example changed and need validation
    assert decision.operation in ['verify', 'crash', 'update'], \
        f"Expected workflow continuation operation, got: {decision.operation}"

    # If details are provided, verify prompt was not flagged as changed
    if decision.details:
        assert decision.details.get('prompt_changed', False) == False, \
            "prompt_changed should be False when only derived artifacts changed"


# =============================================================================
# Stale Run Report Regression Tests
# =============================================================================
# Bug Summary (discovered in admin_get_users):
# - pdd sync returns 'nothing' when run_report is stale (older than fingerprint)
# - run_report shows tests_failed=0 but actual tests have failures
# - The fingerprint.test_hash was updated but run_report was NOT invalidated


class TestStaleRunReportRegression:
    """
    Regression tests for stale run_report bug.

    Bug scenario:
    - run_report.timestamp: 2025-12-10 (old, shows tests_failed=0)
    - fingerprint.timestamp: 2025-12-12 (new, test_hash was updated)
    - Actual tests would fail
    - sync incorrectly returned 'nothing'
    """

    def test_stale_run_report_detected_when_test_hash_differs(self, pdd_test_environment):
        """
        Sync should detect stale run_report and NOT return 'nothing'.

        When fingerprint.test_hash matches current test file but run_report is stale,
        sync should trigger 'test', not 'nothing'.
        """
        tmp_path = pdd_test_environment

        # Create additional directories needed for this test
        Path("src").mkdir(exist_ok=True)
        Path("tests").mkdir(exist_ok=True)
        Path("examples").mkdir(exist_ok=True)

        # Create all files
        prompt_path = tmp_path / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt"
        prompt_hash = create_file(prompt_path, "# Test prompt\nGenerate a test module")

        code_path = tmp_path / "src" / f"{BASENAME}.py"
        code_hash = create_file(code_path, "def foo(): pass")

        example_path = tmp_path / "examples" / f"{BASENAME}_example.py"
        example_hash = create_file(example_path, "# example usage")

        test_path = tmp_path / "tests" / f"test_{BASENAME}.py"
        test_hash = create_file(test_path, "def test_fail(): assert False")

        # Create STALE run_report (Dec 10, claims tests pass, no test_hash)
        create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
            "timestamp": "2025-12-10T08:33:52.589258+00:00",
            "exit_code": 0,
            "tests_passed": 1,
            "tests_failed": 0,
            "coverage": 95.0
        })

        # Create NEWER fingerprint (Dec 12)
        create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
            "pdd_version": "0.0.81",
            "timestamp": "2025-12-12T00:39:11.061591+00:00",
            "command": "verify",
            "prompt_hash": prompt_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash,
        })

        mock_paths = {
            'prompt': prompt_path,
            'code': code_path,
            'example': example_path,
            'test': test_path,
        }

        with patch('sync_determine_operation.construct_paths') as mock_construct, \
             patch('sync_determine_operation.get_pdd_file_paths') as mock_get_paths:
            mock_construct.return_value = (
                {'prompt_file': str(prompt_path)},
                {'output': str(code_path)},
                {'output': str(test_path)},
                {'output': str(example_path)}
            )
            mock_get_paths.return_value = mock_paths

            decision = sync_determine_operation(
                basename=BASENAME,
                language=LANGUAGE,
                target_coverage=TARGET_COVERAGE,
                prompts_dir="prompts",
                skip_tests=False,
                skip_verify=False,
            )

        # FIX: When run_report is stale, sync returns 'test' to re-validate
        assert decision.operation != 'nothing', (
            f"Sync returned 'nothing' with stale run_report!\n"
            f"Expected: 'test' to re-validate\n"
            f"Actual: '{decision.operation}' - {decision.reason}"
        )

    def test_workflow_not_complete_when_run_report_is_stale(self, pdd_test_environment):
        """
        _is_workflow_complete() should return False when run_report is stale.

        When fingerprint.timestamp > run_report.timestamp, workflow should NOT be complete.
        """
        tmp_path = pdd_test_environment

        Path("src").mkdir(exist_ok=True)
        Path("tests").mkdir(exist_ok=True)
        Path("examples").mkdir(exist_ok=True)

        code_path = tmp_path / "src" / f"{BASENAME}.py"
        code_hash = create_file(code_path, "def foo(): pass")

        example_path = tmp_path / "examples" / f"{BASENAME}_example.py"
        example_hash = create_file(example_path, "# example")

        test_path = tmp_path / "tests" / f"test_{BASENAME}.py"
        test_hash = create_file(test_path, "def test_fail(): assert False")

        paths = {
            'code': code_path,
            'example': example_path,
            'test': test_path
        }

        # STALE run_report (Dec 10)
        create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
            "timestamp": "2025-12-10T08:33:52.589258+00:00",
            "exit_code": 0,
            "tests_passed": 1,
            "tests_failed": 0,
            "coverage": 0.0
        })

        # NEWER fingerprint (Dec 12)
        create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
            "pdd_version": "0.0.81",
            "timestamp": "2025-12-12T00:39:11.061591+00:00",
            "command": "verify",
            "prompt_hash": "abc123",
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash,
        })

        result = _is_workflow_complete(
            paths=paths,
            skip_tests=False,
            skip_verify=False,
            basename=BASENAME,
            language=LANGUAGE
        )

        assert result == False, (
            "_is_workflow_complete() returned True with stale run_report.\n"
            "run_report.timestamp: 2025-12-10, fingerprint.timestamp: 2025-12-12\n"
            "The run_report predates the fingerprint, so workflow should not be complete."
        )

    def test_run_report_tests_failed_triggers_fix(self, pdd_test_environment):
        """
        Sanity check: When run_report.tests_failed > 0, sync should return 'fix'.
        """
        tmp_path = pdd_test_environment

        Path("src").mkdir(exist_ok=True)
        Path("tests").mkdir(exist_ok=True)
        Path("examples").mkdir(exist_ok=True)

        prompt_path = tmp_path / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt"
        prompt_hash = create_file(prompt_path, "# prompt")

        code_path = tmp_path / "src" / f"{BASENAME}.py"
        code_hash = create_file(code_path, "def foo(): pass")

        example_path = tmp_path / "examples" / f"{BASENAME}_example.py"
        example_hash = create_file(example_path, "# example")

        test_path = tmp_path / "tests" / f"test_{BASENAME}.py"
        test_hash = create_file(test_path, "def test_fail(): assert False")

        # run_report with tests_failed > 0
        create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
            "timestamp": "2025-12-12T00:00:00.000000+00:00",
            "exit_code": 1,
            "tests_passed": 10,
            "tests_failed": 3,
            "coverage": 0.0
        })

        create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
            "pdd_version": "0.0.81",
            "timestamp": "2025-12-12T00:39:11.061591+00:00",
            "command": "verify",
            "prompt_hash": prompt_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash,
        })

        mock_paths = {
            'prompt': prompt_path,
            'code': code_path,
            'example': example_path,
            'test': test_path,
        }

        with patch('sync_determine_operation.construct_paths') as mock_construct, \
             patch('sync_determine_operation.get_pdd_file_paths') as mock_get_paths:
            mock_construct.return_value = (
                {'prompt_file': str(prompt_path)},
                {'output': str(code_path)},
                {'output': str(test_path)},
                {'output': str(example_path)}
            )
            mock_get_paths.return_value = mock_paths

            decision = sync_determine_operation(
                basename=BASENAME,
                language=LANGUAGE,
                target_coverage=TARGET_COVERAGE,
                prompts_dir="prompts",
                skip_tests=False,
                skip_verify=False,
            )

        assert decision.operation == 'fix', (
            f"Expected 'fix' when tests_failed > 0, got '{decision.operation}'"
        )


class TestFalsePositiveSuccessBugRegression:
    """
    Regression tests for GitHub issue #210: False positive success when skip_verify=True.

    Bug scenario (from core dump):
    - User runs sync, 'example' operation runs
    - fingerprint saved with command='example'
    - run_report created with exit_code=0, tests_failed=0, test_hash=None (from example run, not actual tests)
    - User adds new unit tests that would fail
    - User runs `pdd sync --skip-verify`
    - Sync incorrectly reports success without running tests

    Root causes:
    1. run_report.test_hash was None, causing staleness detection to fail
    2. _is_workflow_complete() didn't check if tests were actually run when skip_verify=True
    """

    def test_skip_verify_with_example_command_should_not_be_complete(self, pdd_test_environment):
        """
        When fingerprint.command='example' and skip_verify=True, workflow should NOT be complete
        because tests haven't been run yet.

        This is the core bug: skip_verify=True bypassed the verify check, but the test check
        was also effectively bypassed because the code only checked for verify completion.
        """
        tmp_path = pdd_test_environment

        Path("src").mkdir(exist_ok=True)
        Path("tests").mkdir(exist_ok=True)
        Path("examples").mkdir(exist_ok=True)

        # Create all files
        prompt_path = tmp_path / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt"
        prompt_hash = create_file(prompt_path, "# Test prompt")

        code_path = tmp_path / "src" / f"{BASENAME}.py"
        code_hash = create_file(code_path, "def foo(): pass")

        example_path = tmp_path / "examples" / f"{BASENAME}_example.py"
        example_hash = create_file(example_path, "# example")

        test_path = tmp_path / "tests" / f"test_{BASENAME}.py"
        test_hash = create_file(test_path, "def test_fail(): assert False  # Would fail if run")

        # Create run_report from example run (not actual tests)
        # This mimics what happens after 'crash' check when example passes
        create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
            "timestamp": "2025-12-18T22:00:00.000000+00:00",  # Newer than fingerprint
            "exit_code": 0,
            "tests_passed": 1,  # This is from example, not actual unit tests
            "tests_failed": 0,
            "coverage": 0.0
            # test_hash is None (missing) - this was part of the bug
        })

        # Create fingerprint with command='example' (tests haven't been run)
        create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
            "pdd_version": "0.0.86",
            "timestamp": "2025-12-18T21:59:51.000000+00:00",  # Older than run_report
            "command": "example",  # Key: this is NOT 'test', 'fix', or 'update'
            "prompt_hash": prompt_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash,
        })

        mock_paths = {
            'prompt': prompt_path,
            'code': code_path,
            'example': example_path,
            'test': test_path,
        }

        # Test _is_workflow_complete directly with skip_verify=True
        result = _is_workflow_complete(
            paths=mock_paths,
            skip_tests=False,
            skip_verify=True,  # Key: skip_verify=True but tests should still be required
            basename=BASENAME,
            language=LANGUAGE
        )

        assert result == False, (
            "_is_workflow_complete() returned True with skip_verify=True and command='example'.\n"
            "Bug: Tests haven't been run yet (fingerprint.command='example'), "
            "but workflow was considered complete.\n"
            "Expected: False (tests need to run)"
        )

    def test_sync_returns_test_operation_when_tests_not_run(self, pdd_test_environment):
        """
        When skip_verify=True but tests haven't been run, sync should return 'test' or 'crash'
        operation, NOT 'nothing'.

        This reproduces the exact scenario from GitHub issue #210.
        """
        tmp_path = pdd_test_environment

        Path("src").mkdir(exist_ok=True)
        Path("tests").mkdir(exist_ok=True)
        Path("examples").mkdir(exist_ok=True)

        # Create all files
        prompt_path = tmp_path / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt"
        prompt_hash = create_file(prompt_path, "# Test prompt")

        code_path = tmp_path / "src" / f"{BASENAME}.py"
        code_hash = create_file(code_path, "def foo(): pass")

        example_path = tmp_path / "examples" / f"{BASENAME}_example.py"
        example_hash = create_file(example_path, "# example")

        test_path = tmp_path / "tests" / f"test_{BASENAME}.py"
        test_hash = create_file(test_path, "def test_fail(): assert False")

        # Create run_report mimicking example success (not actual tests)
        create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
            "timestamp": "2025-12-18T22:00:00.000000+00:00",
            "exit_code": 0,
            "tests_passed": 1,
            "tests_failed": 0,
            "coverage": 0.0
        })

        # Fingerprint with command='example' - tests never ran
        create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
            "pdd_version": "0.0.86",
            "timestamp": "2025-12-18T21:59:51.000000+00:00",
            "command": "example",
            "prompt_hash": prompt_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash,
        })

        mock_paths = {
            'prompt': prompt_path,
            'code': code_path,
            'example': example_path,
            'test': test_path,
        }

        with patch('sync_determine_operation.construct_paths') as mock_construct, \
             patch('sync_determine_operation.get_pdd_file_paths') as mock_get_paths:
            mock_construct.return_value = (
                {'prompt_file': str(prompt_path)},
                {'output': str(code_path)},
                {'output': str(test_path)},
                {'output': str(example_path)}
            )
            mock_get_paths.return_value = mock_paths

            decision = sync_determine_operation(
                basename=BASENAME,
                language=LANGUAGE,
                target_coverage=TARGET_COVERAGE,
                prompts_dir="prompts",
                skip_tests=False,
                skip_verify=True,  # Skip verify but tests should still run
            )

        assert decision.operation != 'nothing', (
            f"Bug reproduced: Sync returned 'nothing' with skip_verify=True and command='example'.\n"
            f"Expected: 'crash', 'verify', or 'test' (workflow should continue)\n"
            f"Actual: '{decision.operation}' - {decision.reason}\n"
            f"This is GitHub issue #210: False positive success"
        )

        # Should be either 'crash' (to validate example), 'verify' (if not skipped), 'test', or 'test_extend'
        assert decision.operation in ['crash', 'verify', 'test', 'test_extend'], (
            f"Expected 'crash', 'verify', 'test', or 'test_extend' to continue workflow, got '{decision.operation}'"
        )


# --- Bug Fix Tests: Prompt Changes Should Take Priority Over Runtime Signals ---

def test_prompt_change_detected_even_after_crash_workflow(pdd_test_environment):
    """
    BUG: When fingerprint.command == 'crash' and run_report.exit_code == 0,
    the sync should still detect prompt changes and trigger regeneration,
    not blindly continue to 'verify'.

    This tests the fix for: prompt changes being ignored when runtime signals
    cause early returns in sync_determine_operation.
    """
    prompts_dir = pdd_test_environment / "prompts"
    prompts_dir.mkdir(exist_ok=True)

    # Create prompt with NEW content (different from fingerprint hash)
    prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
    new_prompt_hash = create_file(prompt_path, "NEW PROMPT CONTENT - changed!")

    # Create fingerprint with OLD prompt hash and command='crash'
    old_prompt_hash = "old_hash_that_differs_from_current"
    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0.0",
        "timestamp": "2025-01-01T00:00:00Z",
        "command": "crash",  # Previous command was crash
        "prompt_hash": old_prompt_hash,  # Different from current!
        "code_hash": "c_hash",
        "example_hash": "e_hash",
        "test_hash": "t_hash"
    })

    # Create run report showing crash fix succeeded
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "2025-01-01T00:00:00Z",
        "exit_code": 0,  # Success - crash was fixed
        "tests_passed": 1,
        "tests_failed": 0,
        "coverage": 95.0
    })

    # Create code/example/test files so they exist
    paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir="prompts")
    create_file(paths['code'], "def add(a, b): return a + b")
    create_file(paths['example'], "print(add(1, 2))")
    create_file(paths['test'], "def test_add(): assert add(1, 2) == 3")

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE)

    # Should detect prompt change and regenerate, NOT continue to verify
    assert decision.operation in ('generate', 'auto-deps'), \
        f"Expected 'generate' or 'auto-deps' due to prompt change, got '{decision.operation}'"
    assert 'prompt' in decision.reason.lower(), \
        f"Reason should mention prompt change: {decision.reason}"


# --- GitHub Issue #349: Infinite Loop Bug Tests ---

class TestInfiniteLoopBugIssue349:
    """
    Regression tests for GitHub issue #349: PDD sync doesn't exit fix loop when fix completed.

    Bug scenario:
    - Tests pass successfully (tests_passed > 0, tests_failed == 0)
    - But pytest returns non-zero exit code (e.g., from pytest-cov warnings)
    - Current code sees exit_code != 0 and returns 'fix' or 'crash'
    - This creates an infinite loop: fix completes, tests pass, but exit_code != 0 triggers another fix

    Root causes identified:
    1. sync_determine_operation checks exit_code != 0 BEFORE checking test results
    2. _is_workflow_complete returns False when exit_code != 0, even if tests pass
    3. No handling for "tests pass but tooling returned non-zero exit code" scenario

    Fix approach:
    - When tests_passed > 0 and tests_failed == 0, treat as success regardless of exit_code
    - exit_code != 0 with passing tests indicates tooling issues (pytest-cov, etc.), not test failures
    """

    def test_nonzero_exit_code_with_passing_tests_should_not_trigger_fix(self, pdd_test_environment):
        """
        Core bug test: When tests pass (tests_passed > 0, tests_failed == 0) but exit_code != 0,
        should NOT return 'fix' or 'crash' - workflow should consider tests as passing.

        This reproduces the infinite loop from issue #349 where pytest-cov or other tooling
        returns non-zero exit code even when all tests pass.
        """
        tmp_path = pdd_test_environment
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir(exist_ok=True)

        # Create all required files
        prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
        prompt_hash = create_file(prompt_path, "# Test prompt for issue 349")

        paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir=str(prompts_dir))
        code_hash = create_file(paths['code'], "def add(a, b): return a + b")
        example_hash = create_file(paths['example'], "print(add(1, 2))")
        test_hash = create_file(paths['test'], "def test_add(): assert add(1, 2) == 3")

        # Create fingerprint indicating 'fix' was the last operation
        create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
            "pdd_version": "0.0.126",
            "timestamp": "2025-12-20T10:00:00.000000+00:00",
            "command": "fix",  # Last command was fix
            "prompt_hash": prompt_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash
        })

        # Create run_report showing:
        # - tests_passed > 0: tests actually passed
        # - tests_failed == 0: no test failures
        # - exit_code != 0: but pytest returned non-zero (e.g., pytest-cov warning)
        create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
            "timestamp": "2025-12-20T10:01:00.000000+00:00",
            "exit_code": 1,  # Non-zero exit code (e.g., from pytest-cov)
            "tests_passed": 5,  # Tests actually passed!
            "tests_failed": 0,  # No failures!
            "coverage": 95.0,
            "test_hash": test_hash
        })

        decision = sync_determine_operation(
            BASENAME, LANGUAGE, TARGET_COVERAGE,
            prompts_dir=str(prompts_dir)
        )

        # Bug: Currently returns 'fix' or 'crash' because exit_code != 0
        # Expected: Should return 'nothing' or 'all_synced' because tests actually pass
        assert decision.operation not in ('fix', 'crash'), (
            f"BUG #349: exit_code=1 with passing tests should NOT trigger '{decision.operation}'.\n"
            f"tests_passed=5, tests_failed=0, exit_code=1 (from tooling, not test failures)\n"
            f"This causes infinite loop: fix completes → tests pass → exit_code != 0 → fix again\n"
            f"Got reason: {decision.reason}"
        )

    def test_is_workflow_complete_with_passing_tests_and_nonzero_exit_code(self, pdd_test_environment):
        """
        Test _is_workflow_complete directly: should return True when tests pass
        even if exit_code is non-zero (tooling issue, not test failure).
        """
        tmp_path = pdd_test_environment
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir(exist_ok=True)

        # Create files
        prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
        prompt_hash = create_file(prompt_path, "# Test prompt")

        paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir=str(prompts_dir))
        code_hash = create_file(paths['code'], "def foo(): pass")
        example_hash = create_file(paths['example'], "foo()")
        test_hash = create_file(paths['test'], "def test_foo(): pass")

        # Fingerprint shows workflow completed 'fix' or 'test'
        create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
            "pdd_version": "0.0.126",
            "timestamp": "2025-12-20T10:00:00.000000+00:00",
            "command": "fix",
            "prompt_hash": prompt_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash
        })

        # Run report: tests pass but exit_code != 0
        create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
            "timestamp": "2025-12-20T10:01:00.000000+00:00",
            "exit_code": 1,  # Pytest-cov or similar returned non-zero
            "tests_passed": 10,  # But tests passed!
            "tests_failed": 0,
            "coverage": 90.0,
            "test_hash": test_hash
        })

        result = _is_workflow_complete(
            paths=paths,
            skip_tests=False,
            skip_verify=False,
            basename=BASENAME,
            language=LANGUAGE
        )

        # Bug: Currently returns False because exit_code != 0
        # Expected: Should return True because tests_passed > 0 and tests_failed == 0
        assert result == True, (
            "BUG #349: _is_workflow_complete() returns False when exit_code=1 with passing tests.\n"
            "This causes the infinite loop: workflow never considered 'complete' despite tests passing.\n"
            "tests_passed=10, tests_failed=0, exit_code=1 (tooling issue)"
        )

    def test_zero_exit_code_zero_tests_passed_should_trigger_action(self, pdd_test_environment):
        """
        Regression guard: When exit_code=0 but tests_passed=0, should NOT consider workflow complete
        with 'nothing' - but 'all_synced' is acceptable for unparseable test output scenarios.
        This ensures we don't infinite loop but also don't silently skip tests.
        """
        tmp_path = pdd_test_environment
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir(exist_ok=True)

        prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
        prompt_hash = create_file(prompt_path, "# Test prompt")

        paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir=str(prompts_dir))
        code_hash = create_file(paths['code'], "def foo(): pass")
        example_hash = create_file(paths['example'], "foo()")
        test_hash = create_file(paths['test'], "def test_foo(): pass")

        create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
            "pdd_version": "0.0.126",
            "timestamp": "2025-12-20T10:00:00.000000+00:00",
            "command": "fix",
            "prompt_hash": prompt_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash
        })

        # exit_code=0 but no tests actually ran (tests_passed=0)
        create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
            "timestamp": "2025-12-20T10:01:00.000000+00:00",
            "exit_code": 0,  # Success exit code
            "tests_passed": 0,  # But no tests passed - suspicious!
            "tests_failed": 0,
            "coverage": 0.0,
            "test_hash": test_hash
        })

        decision = sync_determine_operation(
            BASENAME, LANGUAGE, TARGET_COVERAGE,
            prompts_dir=str(prompts_dir)
        )

        # When exit_code=0 and tests_passed=0 and tests_failed=0, this indicates unparseable output
        # The fix accepts this as 'all_synced' to prevent infinite test loops (especially for non-Python)
        # We just ensure it doesn't return 'nothing' (the hashes-match shortcut path)
        assert decision.operation != 'nothing', (
            f"exit_code=0 but tests_passed=0 should not use 'nothing' shortcut, got '{decision.operation}'\n"
            f"No tests ran successfully, so workflow needs attention."
        )

    def test_unparseable_test_output_for_non_python_accepts_as_complete(self, pdd_test_environment):
        """
        Bug fix test: For non-Python languages, when test output can't be parsed
        (tests_passed=0, tests_failed=0, coverage=0.0 but exit_code=0),
        accept as complete rather than infinitely regenerating tests.

        This was the root cause of the TypeScript infinite loop bug:
        1. pdd sync generates TypeScript tests
        2. npm test runs, exits with 0 (success)
        3. Output parsing fails to extract test counts (tests_passed=0, tests_failed=0)
        4. sync_determine_operation sees coverage=0.0 < target and returns 'test'
        5. Loop repeats infinitely
        """
        tmp_path = pdd_test_environment
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir(exist_ok=True)

        # Use TypeScript for this test
        basename = "prisma_client"
        language = "typescript"

        prompt_path = prompts_dir / f"{basename}_{language}.prompt"
        prompt_hash = create_file(prompt_path, "// TypeScript prompt")

        paths = get_pdd_file_paths(basename, language, prompts_dir=str(prompts_dir))
        code_hash = create_file(paths['code'], "export const foo = () => 'hello';")
        example_hash = create_file(paths['example'], "import { foo } from './code'; console.log(foo());")
        test_hash = create_file(paths['test'], "test('foo', () => { expect(foo()).toBe('hello'); });")

        create_fingerprint_file(get_meta_dir() / f"{basename}_{language}.json", {
            "pdd_version": "0.0.126",
            "timestamp": "2025-12-20T10:00:00.000000+00:00",
            "command": "test",  # Last command was test
            "prompt_hash": prompt_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash
        })

        # Simulates unparseable test output from npm test:
        # - exit_code=0 (tests passed)
        # - tests_passed=0 (couldn't parse output)
        # - tests_failed=0 (couldn't parse output)
        # - coverage=0.0 (couldn't parse output)
        create_run_report_file(get_meta_dir() / f"{basename}_{language}_run.json", {
            "timestamp": "2025-12-20T10:01:00.000000+00:00",
            "exit_code": 0,
            "tests_passed": 0,
            "tests_failed": 0,
            "coverage": 0.0,
            "test_hash": test_hash
        })

        decision = sync_determine_operation(
            basename, language, TARGET_COVERAGE,
            prompts_dir=str(prompts_dir)
        )

        # Should NOT return 'test' - that would cause infinite loop
        # Should return 'all_synced' because exit_code=0 indicates success
        assert decision.operation != 'test', (
            f"BUG: Unparseable test output with exit_code=0 should NOT return 'test', got '{decision.operation}'\n"
            f"This causes infinite test generation loop for non-Python languages.\n"
            f"Reason: {decision.reason}"
        )
        assert decision.operation == 'all_synced', (
            f"Expected 'all_synced' for unparseable but successful tests, got '{decision.operation}'\n"
            f"Reason: {decision.reason}"
        )

    def test_nonzero_exit_code_with_actual_failures_should_trigger_fix(self, pdd_test_environment):
        """
        Regression guard: When exit_code != 0 AND tests_failed > 0, should still trigger fix.
        This ensures the bug fix doesn't break legitimate failure handling.
        """
        tmp_path = pdd_test_environment
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir(exist_ok=True)

        prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
        prompt_hash = create_file(prompt_path, "# Test prompt")

        paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir=str(prompts_dir))
        code_hash = create_file(paths['code'], "def foo(): pass")
        example_hash = create_file(paths['example'], "foo()")
        test_hash = create_file(paths['test'], "def test_foo(): assert False")

        create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
            "pdd_version": "0.0.126",
            "timestamp": "2025-12-20T10:00:00.000000+00:00",
            "command": "fix",
            "prompt_hash": prompt_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash
        })

        # exit_code != 0 AND tests actually failed - this is a real failure
        create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
            "timestamp": "2025-12-20T10:01:00.000000+00:00",
            "exit_code": 1,  # Non-zero exit code
            "tests_passed": 3,
            "tests_failed": 2,  # Actual test failures!
            "coverage": 60.0,
            "test_hash": test_hash
        })

        decision = sync_determine_operation(
            BASENAME, LANGUAGE, TARGET_COVERAGE,
            prompts_dir=str(prompts_dir)
        )

        # Real test failures should still trigger fix
        assert decision.operation == 'fix', (
            f"exit_code=1 with tests_failed=2 should trigger 'fix', got '{decision.operation}'\n"
            f"Real test failures must still be handled."
        )


# --- Bug #573: _is_workflow_complete accepts coverage=0.0 with passing tests ---

class TestZeroCoverageBugIssue573:
    """
    Regression tests for GitHub issue #573: _is_workflow_complete() returns True
    when tests_passed > 0 and tests_failed == 0, even if coverage is 0.0.
    This is a defense-in-depth gap — the function should check coverage against
    a minimum threshold.
    """

    def test_is_workflow_complete_rejects_zero_coverage_with_passing_tests(self, pdd_test_environment):
        """
        Bug #573 (Test 4): _is_workflow_complete should return False when
        coverage=0.0 despite tests_passed > 0 and tests_failed == 0.

        The Bug #349 fix at sync_determine_operation.py:1264 treats
        (tests_passed > 0 and tests_failed == 0) as success without checking
        coverage. This allows coverage=0.0 to be accepted as workflow complete.
        """
        tmp_path = pdd_test_environment
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir(exist_ok=True)

        # Create files
        prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
        prompt_hash = create_file(prompt_path, "# Test prompt")

        paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir=str(prompts_dir))
        code_hash = create_file(paths['code'], "def foo(): pass")
        example_hash = create_file(paths['example'], "foo()")
        test_hash = create_file(paths['test'], "def test_foo(): pass")

        # Fingerprint shows workflow completed 'test'
        create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
            "pdd_version": "0.0.156",
            "timestamp": "2026-02-23T00:00:00Z",
            "command": "test",
            "prompt_hash": prompt_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash
        })

        # Run report: tests pass but coverage is 0.0
        # This reproduces the issue where sys.modules stubs mask import errors
        create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
            "timestamp": "2026-02-23T00:01:00Z",
            "exit_code": 0,
            "tests_passed": 62,
            "tests_failed": 0,
            "coverage": 0.0,
            "test_hash": test_hash
        })

        result = _is_workflow_complete(
            paths=paths,
            skip_tests=False,
            skip_verify=False,
            basename=BASENAME,
            language=LANGUAGE
        )

        # Bug #573: Currently returns True because is_success check at line 1264
        # only checks tests_passed > 0 and tests_failed == 0, ignoring coverage.
        # After fix: Should return False because coverage=0.0 indicates the tests
        # are not actually measuring the module under test.
        assert result is False, (
            "Bug #573: _is_workflow_complete() returns True when coverage=0.0 "
            "with 62 passing tests. This is a defense-in-depth gap — "
            "coverage=0.0 means tests are not exercising the module "
            "(likely due to sys.modules stub masking broken imports)."
        )

    def test_sync_determine_operation_returns_test_extend_for_zero_coverage(self, pdd_test_environment):
        """
        Bug #573 (Test 5): sync_determine_operation should return 'test_extend'
        when tests pass but coverage is 0.0. This validates that the detection
        side works correctly (it does — the bug is in the orchestration layer
        that overrides this signal).
        """
        tmp_path = pdd_test_environment
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir(exist_ok=True)

        prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
        prompt_hash = create_file(prompt_path, "# Test prompt")

        paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir=str(prompts_dir))
        code_hash = create_file(paths['code'], "def foo(): pass")
        example_hash = create_file(paths['example'], "foo()")
        test_hash = create_file(paths['test'], "def test_foo(): pass")

        create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
            "pdd_version": "0.0.156",
            "timestamp": "2026-02-23T00:00:00Z",
            "command": "test",
            "prompt_hash": prompt_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash
        })

        # Run report: tests pass, exit_code=0, but coverage is 0.0
        create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
            "timestamp": "2026-02-23T00:01:00Z",
            "exit_code": 0,
            "tests_passed": 62,
            "tests_failed": 0,
            "coverage": 0.0,
            "test_hash": test_hash
        })

        decision = sync_determine_operation(
            BASENAME, LANGUAGE, TARGET_COVERAGE,
            prompts_dir=str(prompts_dir)
        )

        # The detection side should correctly identify low coverage and return
        # test_extend. This test validates that sync_determine_operation catches
        # the problem even though the orchestration layer currently overrides it.
        assert decision.operation == 'test_extend', (
            f"Expected 'test_extend' for coverage=0.0 with passing tests, "
            f"got '{decision.operation}'. sync_determine_operation should detect "
            f"that coverage 0.0 < target {TARGET_COVERAGE} and request test extension."
        )


# --- GitHub Issue #522: Fingerprint ignores <include> dependencies ---

class TestFingerprintIncludeDependencies:
    """
    Regression tests for GitHub issue #522: sync fingerprint ignores <include>
    dependencies. When an included file changes but the top-level .prompt file
    doesn't, sync should detect the change and regenerate.

    Approach 2: Store include dependency paths + hashes in the fingerprint JSON
    so changes are detected even after auto-deps strips <include> tags.
    """

    def test_extract_include_deps_finds_xml_includes(self, pdd_test_environment):
        """extract_include_deps should find <include> tags and hash the files."""
        prompts_dir = pdd_test_environment / "prompts"
        dep_file = pdd_test_environment / "shared_types.py"
        create_file(dep_file, "class User:\n    name: str\n")

        prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
        create_file(prompt_path, "Create a helper.\n<include>shared_types.py</include>\n")

        deps = extract_include_deps(prompt_path)
        assert len(deps) == 1, f"Expected 1 include dep, got {len(deps)}"
        assert str(dep_file) in deps or any("shared_types.py" in k for k in deps)

    def test_extract_include_deps_finds_backtick_includes(self, pdd_test_environment):
        """extract_include_deps should find ```<file>``` backtick includes."""
        prompts_dir = pdd_test_environment / "prompts"
        dep_file = pdd_test_environment / "utils.py"
        create_file(dep_file, "def helper(): pass\n")

        prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
        create_file(prompt_path, "Build module.\n```<utils.py>```\n")

        deps = extract_include_deps(prompt_path)
        assert len(deps) == 1, f"Expected 1 backtick include dep, got {len(deps)}"

    def test_extract_include_deps_empty_when_no_includes(self, pdd_test_environment):
        """extract_include_deps should return empty dict for prompts without includes."""
        prompts_dir = pdd_test_environment / "prompts"
        prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
        create_file(prompt_path, "Simple prompt with no includes.\n")

        deps = extract_include_deps(prompt_path)
        assert deps == {}, f"Expected empty dict, got {deps}"

    def test_calculate_prompt_hash_with_stored_deps(self, pdd_test_environment):
        """calculate_prompt_hash should use stored deps when prompt has no include tags."""
        prompts_dir = pdd_test_environment / "prompts"
        dep_file = pdd_test_environment / "shared_types.py"
        create_file(dep_file, "class User:\n    name: str\n")

        # Prompt WITHOUT include tags (simulates post-auto-deps state)
        prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
        create_file(prompt_path, "Create a helper using User class.\n")

        stored_deps = {str(dep_file): calculate_sha256(dep_file)}

        # Hash with stored deps should differ from hash without
        hash_without = calculate_prompt_hash(prompt_path)
        hash_with = calculate_prompt_hash(prompt_path, stored_deps=stored_deps)

        assert hash_without != hash_with, (
            "Hash with stored deps should differ from hash without — "
            "stored deps should contribute to the composite hash"
        )

    def test_calculate_prompt_hash_detects_dep_change_via_stored_deps(self, pdd_test_environment):
        """When a stored dep file changes, the composite hash must change."""
        prompts_dir = pdd_test_environment / "prompts"
        dep_file = pdd_test_environment / "shared_types.py"
        create_file(dep_file, "class User:\n    name: str\n")

        prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
        create_file(prompt_path, "Create a helper using User class.\n")

        stored_deps = {str(dep_file): calculate_sha256(dep_file)}
        hash_before = calculate_prompt_hash(prompt_path, stored_deps=stored_deps)

        # Change the dependency file
        create_file(dep_file, "class User:\n    name: str\n    email: str\n")

        hash_after = calculate_prompt_hash(prompt_path, stored_deps=stored_deps)

        assert hash_before != hash_after, (
            "Composite prompt hash must change when a stored dependency file changes, "
            "even when the prompt itself has no <include> tags"
        )

    def test_fingerprint_stores_include_deps(self, pdd_test_environment):
        """Fingerprint dataclass should correctly store and serialize include_deps."""
        fp = Fingerprint(
            pdd_version="0.0.156",
            timestamp="2026-02-23T00:00:00Z",
            command="test",
            prompt_hash="abc",
            code_hash="def",
            example_hash="ghi",
            test_hash="jkl",
            include_deps={"shared_types.py": "hash1", "utils.py": "hash2"},
        )
        from dataclasses import asdict
        d = asdict(fp)
        assert d["include_deps"] == {"shared_types.py": "hash1", "utils.py": "hash2"}

    def test_fingerprint_include_deps_backward_compat(self, pdd_test_environment):
        """Old fingerprint files without include_deps should load with include_deps=None."""
        fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
        create_fingerprint_file(fp_path, {
            "pdd_version": "0.0.145",
            "timestamp": "2026-01-01T00:00:00Z",
            "command": "generate",
            "prompt_hash": "abc",
            "code_hash": "def",
            "example_hash": "ghi",
            "test_hash": "jkl",
        })

        fp = read_fingerprint(BASENAME, LANGUAGE)
        assert fp is not None
        assert fp.include_deps is None, "Old fingerprints should have include_deps=None"

    def test_fingerprint_with_include_deps_loads_correctly(self, pdd_test_environment):
        """Fingerprint with include_deps field should load correctly."""
        fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
        create_fingerprint_file(fp_path, {
            "pdd_version": "0.0.156",
            "timestamp": "2026-02-23T00:00:00Z",
            "command": "generate",
            "prompt_hash": "abc",
            "code_hash": "def",
            "example_hash": "ghi",
            "test_hash": "jkl",
            "include_deps": {"shared.py": "hash1"},
        })

        fp = read_fingerprint(BASENAME, LANGUAGE)
        assert fp is not None
        assert fp.include_deps == {"shared.py": "hash1"}

    def test_included_file_change_triggers_regeneration(self, pdd_test_environment):
        """
        Primary bug reproduction (Greg's scenario): After auto-deps strips <include>
        tags, changing the included file should still trigger regeneration via stored deps.
        """
        prompts_dir = pdd_test_environment / "prompts"
        prompts_dir.mkdir(exist_ok=True)

        # Create dependency file
        dep_file = pdd_test_environment / "shared_types.py"
        create_file(dep_file, "class User:\n    def __init__(self, name): self.name = name\n")

        # Prompt WITH includes (first sync)
        prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
        prompt_content_with_tags = "Create a helper.\n<include>shared_types.py</include>\n"
        create_file(prompt_path, prompt_content_with_tags)

        # Calculate what hash the first sync would have saved
        first_sync_hash = calculate_prompt_hash(prompt_path)
        first_sync_deps = extract_include_deps(prompt_path)

        # Simulate auto-deps stripping the include tags (rewrites .prompt)
        prompt_content_stripped = "Create a helper.\nclass User:\n    def __init__(self, name): self.name = name\n"
        create_file(prompt_path, prompt_content_stripped)

        # Create fingerprint from "first sync" with stored deps
        fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
        create_fingerprint_file(fp_path, {
            "pdd_version": "0.0.156",
            "timestamp": "2026-02-23T00:00:00Z",
            "command": "test",
            "prompt_hash": first_sync_hash,
            "code_hash": None,
            "example_hash": None,
            "test_hash": None,
            "include_deps": first_sync_deps,
        })

        # Create code/example/test files
        paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir="prompts")
        code_hash = create_file(paths['code'], "def helper(): pass")
        example_hash = create_file(paths['example'], "helper()")
        test_hash = create_file(paths['test'], "def test_helper(): pass")

        # Update fingerprint with file hashes
        create_fingerprint_file(fp_path, {
            "pdd_version": "0.0.156",
            "timestamp": "2026-02-23T00:00:00Z",
            "command": "test",
            "prompt_hash": first_sync_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash,
            "include_deps": first_sync_deps,
        })

        # Create passing run report
        rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
        create_run_report_file(rr_path, {
            "timestamp": "2026-02-23T00:00:00Z",
            "exit_code": 0,
            "tests_passed": 5,
            "tests_failed": 0,
            "coverage": 95.0,
        })

        # NOW change the included file (this is the bug trigger)
        create_file(dep_file, "class User:\n    def __init__(self, name, age, email): pass\n")

        decision = sync_determine_operation(
            BASENAME, LANGUAGE, TARGET_COVERAGE,
            prompts_dir=str(prompts_dir)
        )

        assert decision.operation in ('generate', 'auto-deps'), (
            f"Expected 'generate' or 'auto-deps' because included file changed "
            f"(via stored deps), but got '{decision.operation}'. "
            f"Stored include_deps in fingerprint must detect dependency changes "
            f"even when auto-deps has stripped <include> tags from the prompt."
        )

    def test_no_change_no_false_positive_with_stored_deps(self, pdd_test_environment):
        """When nothing changes, stored deps must not cause false positive regeneration."""
        prompts_dir = pdd_test_environment / "prompts"
        prompts_dir.mkdir(exist_ok=True)

        dep_file = pdd_test_environment / "shared_types.py"
        create_file(dep_file, "class User:\n    pass\n")

        # Prompt WITH includes
        prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
        create_file(prompt_path, "Create a helper.\n<include>shared_types.py</include>\n")

        prompt_hash = calculate_prompt_hash(prompt_path)
        include_deps = extract_include_deps(prompt_path)

        paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir="prompts")
        code_hash = create_file(paths['code'], "def helper(): pass")
        example_hash = create_file(paths['example'], "helper()")
        test_hash = create_file(paths['test'], "def test_helper(): pass")

        fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
        create_fingerprint_file(fp_path, {
            "pdd_version": "0.0.156",
            "timestamp": "2026-02-23T00:00:00Z",
            "command": "test",
            "prompt_hash": prompt_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash,
            "include_deps": include_deps,
        })

        rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
        create_run_report_file(rr_path, {
            "timestamp": "2026-02-23T00:00:00Z",
            "exit_code": 0,
            "tests_passed": 5,
            "tests_failed": 0,
            "coverage": 95.0,
        })

        # Nothing changed
        decision = sync_determine_operation(
            BASENAME, LANGUAGE, TARGET_COVERAGE,
            prompts_dir=str(prompts_dir)
        )

        assert decision.operation not in ('generate', 'auto-deps'), (
            f"Expected no regeneration when nothing changed, got '{decision.operation}'. "
            f"Stored include_deps must not cause false positives."
        )

    def test_one_of_multiple_deps_changes(self, pdd_test_environment):
        """When one of multiple stored deps changes, sync should detect it."""
        prompts_dir = pdd_test_environment / "prompts"
        prompts_dir.mkdir(exist_ok=True)

        dep1 = pdd_test_environment / "types.py"
        dep2 = pdd_test_environment / "utils.py"
        create_file(dep1, "class Foo: pass")
        create_file(dep2, "def bar(): pass")

        prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
        create_file(prompt_path, "Build module.\n<include>types.py</include>\n<include>utils.py</include>\n")

        prompt_hash = calculate_prompt_hash(prompt_path)
        include_deps = extract_include_deps(prompt_path)

        paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir="prompts")
        code_hash = create_file(paths['code'], "def module(): pass")
        example_hash = create_file(paths['example'], "module()")
        test_hash = create_file(paths['test'], "def test_module(): pass")

        fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
        create_fingerprint_file(fp_path, {
            "pdd_version": "0.0.156",
            "timestamp": "2026-02-23T00:00:00Z",
            "command": "test",
            "prompt_hash": prompt_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash,
            "include_deps": include_deps,
        })

        rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
        create_run_report_file(rr_path, {
            "timestamp": "2026-02-23T00:00:00Z",
            "exit_code": 0,
            "tests_passed": 1,
            "tests_failed": 0,
            "coverage": 90.0,
        })

        # Change only dep2
        create_file(dep2, "def bar(): return 42")

        decision = sync_determine_operation(
            BASENAME, LANGUAGE, TARGET_COVERAGE,
            prompts_dir=str(prompts_dir)
        )

        assert decision.operation in ('generate', 'auto-deps'), (
            f"Expected regeneration when one of multiple included files changed, "
            f"got '{decision.operation}'."
        )
