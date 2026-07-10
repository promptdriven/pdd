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
    is_test_extend_disabled,
    validate_expected_files,
    _handle_missing_expected_files,
    _is_workflow_complete,
    get_pdd_file_paths,
    _safe_architecture_prompt_filename,
    _contained_architecture_code_path,
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


def _write_complete_unit_with_fingerprint(tmp_path: Path) -> dict:
    """Create a complete synced Python unit and return its paths."""
    paths = {
        "prompt": tmp_path / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt",
        "code": tmp_path / f"{BASENAME}.py",
        "example": tmp_path / "examples" / f"{BASENAME}_example.py",
        "test": tmp_path / "tests" / f"test_{BASENAME}.py",
    }
    prompt_hash = create_file(paths["prompt"], "Generate a simple function.\n")
    code_hash = create_file(paths["code"], "def value():\n    return 1\n")
    example_hash = create_file(paths["example"], "from test_unit import value\nprint(value())\n")
    test_hash = create_file(paths["test"], "from test_unit import value\nndef test_value():\n    assert value() == 1\n")
    create_fingerprint_file(
        get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json",
        {
            "pdd_version": "test",
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "command": "fix",
            "prompt_hash": prompt_hash,
            "code_hash": code_hash,
            "example_hash": example_hash,
            "test_hash": test_hash,
            "test_files": {paths["test"].name: test_hash},
            "include_deps": {},
        },
    )
    create_run_report_file(
        get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json",
        {
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "exit_code": 0,
            "tests_passed": 1,
            "tests_failed": 0,
            "coverage": 100.0,
            "test_hash": test_hash,
            "test_files": {paths["test"].name: test_hash},
        },
    )
    return paths

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
    create_file(test_file, "def test_x(): pass\n")

    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0", "timestamp": "t", "command": "test",
        "prompt_hash": prompt_hash, "code_hash": "c", "example_hash": "e", "test_hash": "t"
    })
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 1, "tests_passed": 0, "tests_failed": 3, "coverage": 50.0
    })
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
    assert decision.operation == 'fix'
    assert "Test failures detected" in decision.reason