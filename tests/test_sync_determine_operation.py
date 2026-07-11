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
    _find_prompt_file,
    UnsafePromptPathError,
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
    test_hash = create_file(paths["test"], "from test_unit import value\n\ndef test_value():\n    assert value() == 1\n")
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

    # Create test file and code file on disk so existence checks pass
    Path("tests").mkdir(exist_ok=True)
    test_path = tmp_path / "tests" / f"test_{BASENAME}.py"
    create_file(test_path, "def test_foo(): pass")
    code_path = tmp_path / f"{BASENAME}.py"
    create_file(code_path, "def foo(): pass")

    # Mock get_pdd_file_paths to return the test path
    mock_get_pdd_paths.return_value = {
        'prompt': tmp_path / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt",
        'code': code_path,
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


@patch('sync_determine_operation.construct_paths')
@patch('sync_determine_operation.get_pdd_file_paths')
def test_decision_pr_scope_guard_suppresses_python_low_coverage_test_extend(
    mock_get_pdd_paths,
    mock_construct,
    pdd_test_environment,
    monkeypatch,
):
    """#1403: PDD_DISABLE_TEST_EXTEND converts Python coverage growth into a no-op."""
    tmp_path = pdd_test_environment
    Path("tests").mkdir(exist_ok=True)
    test_path = tmp_path / "tests" / f"test_{BASENAME}.py"
    create_file(test_path, "def test_foo(): pass")
    code_path = tmp_path / f"{BASENAME}.py"
    create_file(code_path, "def foo(): pass")

    mock_get_pdd_paths.return_value = {
        'prompt': tmp_path / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt",
        'code': code_path,
        'example': tmp_path / f"{BASENAME}_example.py",
        'test': test_path,
    }
    create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
        "pdd_version": "1.0", "timestamp": "t", "command": "test",
        "prompt_hash": "p", "code_hash": "c", "example_hash": "e", "test_hash": "t"
    })
    create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
        "timestamp": "t", "exit_code": 0, "tests_passed": 62, "tests_failed": 0,
        "coverage": 0.0, "test_hash": "t"
    })

    monkeypatch.setenv("PDD_DISABLE_TEST_EXTEND", "1")
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE)

    assert decision.operation == 'all_synced'
    assert decision.details['test_extend_skipped'] is True
    assert decision.details['skip_reason'] == 'PDD_DISABLE_TEST_EXTEND'
    assert decision.details['current_coverage'] == 0.0


@patch('sync_determine_operation.construct_paths')
@patch('sync_determine_operation.get_pdd_file_paths')
def test_decision_test_extend_default_still_runs_without_pr_scope_guard(
    mock_get_pdd_paths,
    mock_construct,
    pdd_test_environment,
    monkeypatch,
):
    """#1403 regression guard: normal pdd sync still chooses test_extend when the flag is absent."""
    tmp_path = pdd_test_environment
    Path("tests").mkdir(exist_ok=True)
    test_path = tmp_path / "tests" / f"test_{BASENAME}.py"
    create_file(test_path, "def test_foo(): pass")
    code_path = tmp_path / f"{BASENAME}.py"
    create_file(code_path, "def foo(): pass")

    mock_get_pdd_paths.return_value = {
        'prompt': tmp_path / "prompts" / f"{BASENAME}_{LANGUAGE}.prompt",
        'code': code_path,
        'example': tmp_path / f"{BASENAME}_example.py",
        'test': test_path,
    }
    create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
        "pdd_version": "1.0", "timestamp": "t", "command": "test",
        "prompt_hash": "p", "code_hash": "c", "example_hash": "e", "test_hash": "t"
    })
    create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
        "timestamp": "t", "exit_code": 0, "tests_passed": 62, "tests_failed": 0,
        "coverage": 0.0, "test_hash": "t"
    })

    monkeypatch.delenv("PDD_DISABLE_TEST_EXTEND", raising=False)
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE)

    assert decision.operation == 'test_extend'
    assert decision.details['extend_tests'] is True


@pytest.mark.parametrize(
    "value,expected",
    [
        ("1", True), ("true", True), ("TRUE", True), ("Yes", True), ("on", True),
        ("  on  ", True),
        ("0", False), ("false", False), ("no", False), ("off", False), ("", False),
        ("maybe", False),
    ],
)
def test_test_extend_disabled_truthiness(value, expected, monkeypatch):
    """#1403: only 1/true/yes/on (case-insensitive, trimmed) enable the guard;
    falsey values (incl. '0'/'false') must leave test_extend enabled."""
    monkeypatch.setenv("PDD_DISABLE_TEST_EXTEND", value)
    assert is_test_extend_disabled() is expected


def test_test_extend_disabled_unset_is_false(monkeypatch):
    """#1403: with the flag unset the guard is inactive (default behavior)."""
    monkeypatch.delenv("PDD_DISABLE_TEST_EXTEND", raising=False)
    assert is_test_extend_disabled() is False

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

def test_regression_missing_code_with_low_coverage_run_report(pdd_test_environment):
    """
    Regression test for commit be50e49ee: when run_report has coverage=0.0 and
    tests_passed=1 but code file is missing, sync should return 'generate' not 'test'.
    The bug was that the test-file-existence check didn't also verify the code file
    exists, causing cmd_test_main to fail with FileNotFoundError on the missing source.
    """
    prompts_dir = pdd_test_environment / "prompts"
    prompts_dir.mkdir(exist_ok=True)
    prompt_hash = create_file(
        prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", "Create a simple add function"
    )

    fingerprint_data = {
        "pdd_version": "0.0.168",
        "timestamp": "2026-03-07T07:26:01Z",
        "command": "test",
        "prompt_hash": prompt_hash,
        "code_hash": "abc",
        "example_hash": "def",
        "test_hash": "ghi",
    }
    create_fingerprint_file(
        get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", fingerprint_data
    )

    run_report = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "exit_code": 0,
        "tests_passed": 1,
        "tests_failed": 0,
        "coverage": 0.0,
        "test_hash": "ghi",
    }
    create_run_report_file(
        get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", run_report
    )

    # Source files NOT created — simulating deletion / stale metadata
    decision = sync_determine_operation(
        BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir)
    )
    assert decision.operation == 'generate', (
        f"Expected 'generate' but got '{decision.operation}': {decision.reason}"
    )

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
    """When prompt and derived files changed, sync must return an explicit conflict."""
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
    assert decision.operation == 'fail_and_request_manual_merge'
    assert decision.details.get('classification') == 'CONFLICT'
    assert decision.details.get('changed_files') == ['prompt', 'code']
    assert fp_path.exists(), "Conflict classification must not delete metadata"


@patch('sync_determine_operation.construct_paths')
def test_log_mode_conflict_analysis_keeps_metadata(mock_construct, pdd_test_environment):
    """Read-only analysis must not delete metadata for prompt+derived conflicts."""
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
    rr_path.write_text("not json", encoding="utf-8")

    decision = sync_determine_operation(
        BASENAME,
        LANGUAGE,
        TARGET_COVERAGE,
        prompts_dir=str(prompts_dir),
        log_mode=True,
    )

    assert decision.operation == 'fail_and_request_manual_merge'
    assert decision.details.get('classification') == 'CONFLICT'
    assert decision.details.get('read_only') is True
    assert fp_path.exists()
    assert rr_path.exists()


@patch('sync_determine_operation.construct_paths')
def test_conflict_preserves_fingerprint_and_run_report(mock_construct, pdd_test_environment):
    """Prompt+derived co-edits must not delete metadata or pick a winner."""
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

    assert decision.operation == 'fail_and_request_manual_merge'
    assert decision.details.get('classification') == 'CONFLICT'
    assert decision.operation != 'analyze_conflict'
    assert fp_path.exists()
    assert rr_path.exists()


def test_prompt_code_coedit_conflict_with_real_paths_preserves_metadata(pdd_test_environment):
    """Critical #1932/#1929 closure: prompt+code co-edit is CONFLICT, not deletion."""
    paths = _write_complete_unit_with_fingerprint(pdd_test_environment)
    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    before_fp = fp_path.read_text(encoding="utf-8")

    paths["prompt"].write_text("Generate a changed function.\n", encoding="utf-8")
    paths["code"].write_text("def value():\n    return 2\n", encoding="utf-8")

    decision = sync_determine_operation(
        BASENAME,
        LANGUAGE,
        TARGET_COVERAGE,
        prompts_dir=str(pdd_test_environment / "prompts"),
    )

    assert decision.operation == "fail_and_request_manual_merge"
    assert decision.details["classification"] == "CONFLICT"
    assert set(decision.details["changed_files"]) == {"prompt", "code"}
    assert fp_path.read_text(encoding="utf-8") == before_fp
    assert paths["prompt"].read_text(encoding="utf-8") == "Generate a changed function.\n"


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
def test_sync_determine_operation_respects_skip_flags_before_run_report(mock_construct, pdd_test_environment):
    """Test that skip flags prevent crash/fix recommendations based on cached failing run reports."""
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

    # Create run report with test failures
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 0, "tests_passed": 5, "tests_failed": 2, "coverage": 80.0,
        "test_hash": test_hash
    })

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir), skip_tests=True, skip_verify=True)
    assert decision.operation == 'all_synced'  # Should NOT trigger fix because skip flags are active
    assert "tests skipped" in decision.reason.lower()

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


def test_get_pdd_file_paths_architecture_filepath_uses_basename_context(tmp_path, monkeypatch):
    """Architecture filepaths should resolve example/test dirs from the module context."""
    monkeypatch.chdir(tmp_path)

    (tmp_path / "prompts").mkdir()
    (tmp_path / "pdd").mkdir()
    (tmp_path / "context").mkdir()
    (tmp_path / "context_tests").mkdir()
    (tmp_path / "examples").mkdir()
    (tmp_path / "tests").mkdir()
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)

    (tmp_path / ".pddrc").write_text(
        'contexts:\n'
        '  default:\n'
        '    paths: ["**"]\n'
        '    defaults:\n'
        '      test_output_path: "tests/"\n'
        '      example_output_path: "examples/"\n'
        '      generate_output_path: "src/"\n'
        '  pdd_cli:\n'
        '    paths: ["pdd/**"]\n'
        '    defaults:\n'
        '      test_output_path: "context_tests/"\n'
        '      example_output_path: "context"\n'
        '      generate_output_path: "pdd/"\n'
    )
    (tmp_path / "architecture.json").write_text(json.dumps({
        "modules": [{
            "filename": "agentic_architecture_python.prompt",
            "filepath": "pdd/agentic_architecture.py",
        }]
    }))

    paths = get_pdd_file_paths("agentic_architecture", "python", "prompts")

    assert paths["code"] == tmp_path / "pdd" / "agentic_architecture.py"
    assert paths["example"] == tmp_path / "context" / "agentic_architecture_example.py"
    assert paths["test"] == tmp_path / "context_tests" / "test_agentic_architecture.py"


def _write_nested_architecture_project(
    root: Path,
    *,
    prompts_dir: str,
    architecture_filename: str,
    architecture_filepath: str,
) -> None:
    prompt_dir = root / prompts_dir
    prompt_dir.mkdir(parents=True)
    (prompt_dir / "credits_Python.prompt").write_text(
        "% endpoint test mixin for the credits endpoints\n",
        encoding="utf-8",
    )
    (root / ".pdd" / "meta").mkdir(parents=True)
    (root / ".pdd" / "locks").mkdir(parents=True)
    (root / ".pddrc").write_text(
        'contexts:\n'
        '  backend:\n'
        f'    paths: ["backend/**", "{prompts_dir}/**"]\n'
        '    defaults:\n'
        f'      prompts_dir: "{prompts_dir}"\n'
        '      generate_output_path: "backend/functions/"\n'
        '      outputs:\n'
        '        code:\n'
        '          path: "backend/functions/{name}.py"\n'
        '        example:\n'
        '          path: "custom_usage/{name}_usage.py"\n'
        '        test:\n'
        '          path: "custom_specs/{name}_spec.py"\n',
        encoding="utf-8",
    )
    (root / "architecture.json").write_text(
        json.dumps({
            "modules": [{
                "filename": architecture_filename,
                "filepath": architecture_filepath,
            }]
        }),
        encoding="utf-8",
    )


def test_get_pdd_file_paths_matches_prompt_root_symlink_alias(tmp_path, monkeypatch):
    """A trusted prompt-root symlink keeps architecture ownership identity."""
    monkeypatch.chdir(tmp_path)
    _write_nested_architecture_project(
        tmp_path,
        prompts_dir="pdd/prompts",
        architecture_filename="credits_Python.prompt",
        architecture_filepath="backend/tests/endpoint_tests/tests/credits.py",
    )
    try:
        (tmp_path / "prompts").symlink_to("pdd/prompts", target_is_directory=True)
    except OSError:
        pytest.skip("directory symlinks are unavailable")

    paths = get_pdd_file_paths(
        "credits",
        "python",
        prompts_dir="prompts",
        context_override="backend",
    )

    assert paths["code"].resolve(strict=False) == (
        tmp_path / "backend" / "tests" / "endpoint_tests" / "tests" / "credits.py"
    ).resolve(strict=False)


def test_get_pdd_file_paths_architecture_filepath_with_custom_prompt_root_and_outputs(
    tmp_path,
    monkeypatch,
):
    """A custom prompt root resolves from one architecture lookup."""
    import sync_determine_operation as sync_determine_module

    monkeypatch.chdir(tmp_path)
    real_code = tmp_path / "backend" / "tests" / "endpoint_tests" / "tests" / "credits.py"
    real_code.parent.mkdir(parents=True)
    real_code.write_text("class CreditsTestsMixin:\n    pass\n", encoding="utf-8")
    _write_nested_architecture_project(
        tmp_path,
        prompts_dir="specs/backend",
        architecture_filename="backend/credits_Python.prompt",
        architecture_filepath="backend/tests/endpoint_tests/tests/credits.py",
    )
    architecture_lookups = 0
    original_lookup = sync_determine_module._get_filepath_from_architecture

    def counting_lookup(*args, **kwargs):
        nonlocal architecture_lookups
        architecture_lookups += 1
        return original_lookup(*args, **kwargs)

    monkeypatch.setattr(
        sync_determine_module,
        "_get_filepath_from_architecture",
        counting_lookup,
    )

    paths = get_pdd_file_paths(
        "credits",
        "python",
        prompts_dir="specs/backend",
        context_override="backend",
    )

    assert paths["code"] == real_code
    assert paths["example"] == tmp_path / "custom_usage" / "credits_usage.py"
    assert paths["test"] == tmp_path / "custom_specs" / "credits_spec.py"
    assert architecture_lookups == 1


def test_get_pdd_file_paths_matches_canonical_filepath_derived_architecture_filename(
    tmp_path,
    monkeypatch,
):
    """Issue #617 normalized filenames can differ from the physical prompt path."""
    monkeypatch.chdir(tmp_path)
    real_code = tmp_path / "backend" / "tests" / "endpoint_tests" / "tests" / "credits.py"
    real_code.parent.mkdir(parents=True)
    real_code.write_text("class CreditsTestsMixin:\n    pass\n", encoding="utf-8")
    _write_nested_architecture_project(
        tmp_path,
        prompts_dir="prompts/backend",
        architecture_filename="backend/tests/endpoint_tests/tests/credits_Python.prompt",
        architecture_filepath="backend/tests/endpoint_tests/tests/credits.py",
    )

    def fail_recursive_scan(*_args, **_kwargs):
        pytest.fail("canonical architecture ownership must not scan the prompt tree")

    monkeypatch.setattr(Path, "rglob", fail_recursive_scan)

    paths = get_pdd_file_paths(
        "credits",
        "python",
        prompts_dir="prompts/backend",
        context_override="backend",
    )

    assert paths["code"] == real_code


def test_get_pdd_file_paths_does_not_borrow_nested_same_leaf_architecture_entry(
    tmp_path,
    monkeypatch,
):
    """A flat prompt cannot inherit a nested sibling's architecture filepath."""
    monkeypatch.chdir(tmp_path)
    _write_nested_architecture_project(
        tmp_path,
        prompts_dir="prompts/backend",
        architecture_filename="backend/utils/credits_Python.prompt",
        architecture_filepath="backend/functions/utils/credits.py",
    )
    nested_prompt = tmp_path / "prompts" / "backend" / "utils" / "credits_Python.prompt"
    nested_prompt.parent.mkdir(parents=True)
    nested_prompt.write_text("% nested credits helper\n", encoding="utf-8")
    nested_code = tmp_path / "backend" / "functions" / "utils" / "credits.py"
    nested_code.parent.mkdir(parents=True)
    nested_code.write_text("def nested_credits():\n    pass\n", encoding="utf-8")

    flat_paths = get_pdd_file_paths(
        "credits",
        "python",
        prompts_dir="prompts/backend",
        context_override="backend",
    )
    nested_paths = get_pdd_file_paths(
        "credits",
        "python",
        prompts_dir="prompts/backend/utils",
        context_override="backend",
    )

    assert flat_paths["code"].resolve() == (
        tmp_path / "backend" / "functions" / "credits.py"
    ).resolve()
    assert nested_paths["code"] == nested_code


def test_get_pdd_file_paths_does_not_borrow_sibling_context_architecture_entry(
    tmp_path,
    monkeypatch,
):
    """A narrowed backend root cannot inherit a frontend prompt's module."""
    monkeypatch.chdir(tmp_path)
    _write_nested_architecture_project(
        tmp_path,
        prompts_dir="prompts/backend",
        architecture_filename="frontend/credits_Python.prompt",
        architecture_filepath="frontend/credits.py",
    )
    frontend_prompt = tmp_path / "prompts" / "frontend" / "credits_Python.prompt"
    frontend_prompt.parent.mkdir(parents=True)
    frontend_prompt.write_text("% frontend credits\n", encoding="utf-8")

    paths = get_pdd_file_paths(
        "credits",
        "python",
        prompts_dir="prompts/backend",
        context_override="backend",
    )

    assert paths["code"].resolve(strict=False) == (
        tmp_path / "backend" / "functions" / "credits.py"
    ).resolve(strict=False)


def test_get_pdd_file_paths_does_not_borrow_stale_sibling_context_entry(
    tmp_path,
    monkeypatch,
):
    """A deleted sibling prompt's surviving architecture row must not be borrowed.

    Regression: when the frontend prompt no longer exists, its ``frontend`` entry
    has no physical owner. The same-leaf ``backend`` prompt must still fall back to
    its own configured output, never inherit the foreign module's ``frontend``
    filepath and silently overwrite another context's code.
    """
    monkeypatch.chdir(tmp_path)
    _write_nested_architecture_project(
        tmp_path,
        prompts_dir="prompts/backend",
        architecture_filename="frontend/credits_Python.prompt",
        architecture_filepath="frontend/credits.py",
    )
    # NOTE: the frontend prompt is intentionally NOT created — the entry is stale.

    paths = get_pdd_file_paths(
        "credits",
        "python",
        prompts_dir="prompts/backend",
        context_override="backend",
    )

    assert paths["code"].resolve(strict=False) == (
        tmp_path / "backend" / "functions" / "credits.py"
    ).resolve(strict=False)
    assert paths["code"].resolve(strict=False) != (
        tmp_path / "frontend" / "credits.py"
    ).resolve(strict=False)


def test_get_pdd_file_paths_does_not_alias_prompt_named_module_by_filepath_stem(
    tmp_path,
    monkeypatch,
):
    """A billing prompt whose code stem is credits remains the billing module."""
    monkeypatch.chdir(tmp_path)
    _write_nested_architecture_project(
        tmp_path,
        prompts_dir="prompts/backend",
        architecture_filename="frontend/billing_Python.prompt",
        architecture_filepath="frontend/credits.py",
    )

    paths = get_pdd_file_paths(
        "credits",
        "python",
        prompts_dir="prompts/backend",
        context_override="backend",
    )

    assert paths["code"].resolve(strict=False) == (
        tmp_path / "backend" / "functions" / "credits.py"
    ).resolve(strict=False)


@pytest.mark.parametrize(
    "unsafe_filepath",
    ["../../outside.py", "/tmp/pdd-sync-outside.py", "..\\..\\outside.py"],
)
def test_get_pdd_file_paths_rejects_unsafe_architecture_filepath(
    tmp_path,
    monkeypatch,
    unsafe_filepath,
):
    """Architecture metadata cannot make sync write outside the project."""
    monkeypatch.chdir(tmp_path)
    _write_nested_architecture_project(
        tmp_path,
        prompts_dir="prompts/backend",
        architecture_filename="backend/credits_Python.prompt",
        architecture_filepath=unsafe_filepath,
    )

    paths = get_pdd_file_paths(
        "credits",
        "python",
        prompts_dir="prompts/backend",
        context_override="backend",
    )

    assert paths["code"].resolve(strict=False) == (
        tmp_path / "backend" / "functions" / "credits.py"
    ).resolve(strict=False)


@pytest.mark.parametrize(
    "unsafe_filename",
    [
        "../../credits_Python.prompt",
        "/tmp/credits_Python.prompt",
        "..\\..\\credits_Python.prompt",
    ],
)
def test_get_pdd_file_paths_rejects_unsafe_architecture_filename(
    tmp_path,
    monkeypatch,
    unsafe_filename,
):
    """Architecture prompt identities cannot probe outside the prompt root."""
    monkeypatch.chdir(tmp_path)
    _write_nested_architecture_project(
        tmp_path,
        prompts_dir="prompts/backend",
        architecture_filename=unsafe_filename,
        architecture_filepath="backend/tests/endpoint_tests/tests/credits.py",
    )

    paths = get_pdd_file_paths(
        "credits",
        "python",
        prompts_dir="prompts/backend",
        context_override="backend",
    )

    assert paths["code"].resolve(strict=False) == (
        tmp_path / "backend" / "functions" / "credits.py"
    ).resolve(strict=False)


@pytest.mark.parametrize(
    "drive_filename",
    [
        "D:/credits_Python.prompt",
        "D:credits_Python.prompt",
        "C:/nested/credits_Python.prompt",
    ],
)
def test_safe_architecture_prompt_filename_rejects_windows_drive(drive_filename):
    """Drive-qualified prompt metadata is POSIX-relative but escapes on Windows.

    ``PurePosixPath`` treats ``D:/x`` as relative, so the earlier absolute/`..`
    checks pass it through; joining it on Windows yields a drive-relative path
    outside ``prompts_root``. The validator must reject it on every platform.
    """
    assert _safe_architecture_prompt_filename(drive_filename) is None


@pytest.mark.parametrize(
    "drive_filepath",
    [
        "D:/credits.py",
        "D:credits.py",
        "C:/nested/credits.py",
    ],
)
def test_contained_architecture_code_path_rejects_windows_drive(tmp_path, drive_filepath):
    """Drive-qualified output metadata must not resolve to a code path."""
    assert _contained_architecture_code_path(tmp_path, drive_filepath) is None


def test_get_pdd_file_paths_rejects_unsafe_filename_when_prompt_is_missing(
    tmp_path,
    monkeypatch,
):
    """A missing internal prompt cannot make discovery follow an external hint."""
    monkeypatch.chdir(tmp_path)
    external_dir = tmp_path.parent / f"{tmp_path.name}-external-prompts"
    external_dir.mkdir()
    external_prompt = external_dir / "credits_Python.prompt"
    external_prompt.write_text("% external prompt\n", encoding="utf-8")
    _write_nested_architecture_project(
        tmp_path,
        prompts_dir="prompts/backend",
        architecture_filename=str(external_prompt),
        architecture_filepath="backend/tests/endpoint_tests/tests/credits.py",
    )
    (tmp_path / "prompts" / "backend" / "credits_Python.prompt").unlink()

    unsafe_filenames = (
        str(external_prompt),
        f"../../../{external_dir.name}/credits_Python.prompt",
    )
    for unsafe_filename in unsafe_filenames:
        (tmp_path / "architecture.json").write_text(
            json.dumps({
                "modules": [{
                    "filename": unsafe_filename,
                    "filepath": "backend/tests/endpoint_tests/tests/credits.py",
                }]
            }),
            encoding="utf-8",
        )

        paths = get_pdd_file_paths(
            "credits",
            "python",
            prompts_dir="prompts/backend",
            context_override="backend",
        )

        assert paths["prompt"].resolve(strict=False) != external_prompt.resolve()
        assert paths["prompt"].resolve(strict=False).is_relative_to(
            (tmp_path / "prompts" / "backend").resolve()
        )
        assert paths["code"].resolve(strict=False) == (
            tmp_path / "backend" / "functions" / "credits.py"
        ).resolve(strict=False)


def test_get_pdd_file_paths_rejects_symlink_prompt_discovery_escape(
    tmp_path,
    monkeypatch,
):
    """Architecture prompt discovery cannot escape through a directory symlink."""
    monkeypatch.chdir(tmp_path)
    external_dir = tmp_path.parent / f"{tmp_path.name}-external-symlink-prompts"
    external_dir.mkdir()
    external_prompt = external_dir / "credits_Python.prompt"
    external_prompt.write_text("% external prompt\n", encoding="utf-8")
    _write_nested_architecture_project(
        tmp_path,
        prompts_dir="prompts/backend",
        architecture_filename="linked/credits_Python.prompt",
        architecture_filepath="backend/tests/endpoint_tests/tests/credits.py",
    )
    internal_prompt = tmp_path / "prompts" / "backend" / "credits_Python.prompt"
    internal_prompt.unlink()
    try:
        (tmp_path / "prompts" / "backend" / "linked").symlink_to(
            external_dir,
            target_is_directory=True,
        )
    except OSError:
        pytest.skip("directory symlinks are unavailable")

    paths = get_pdd_file_paths(
        "credits",
        "python",
        prompts_dir="prompts/backend",
        context_override="backend",
    )

    assert paths["prompt"].resolve(strict=False) != external_prompt.resolve()
    assert paths["code"].resolve(strict=False) == (
        tmp_path / "backend" / "functions" / "credits.py"
    ).resolve(strict=False)


def test_get_pdd_file_paths_rejects_same_leaf_file_symlink_discovery_escape(
    tmp_path,
    monkeypatch,
):
    """Recursive discovery must not return a same-leaf FILE symlink that escapes root.

    The directory-symlink test above does not cover this route: ``rglob`` does not
    descend into symlinked directories, but it DOES yield a file symlink, and
    ``is_file()`` follows the link. Architecture names a safe-but-missing prompt so
    resolution falls through to the recursive scan (Step 3c / Step 4); a same-leaf
    in-root file symlink points outside the repo. Returning it would let an update
    write through the link and overwrite the external file.
    """
    monkeypatch.chdir(tmp_path)
    external_dir = tmp_path.parent / f"{tmp_path.name}-external-file-symlink"
    external_dir.mkdir()
    external_prompt = external_dir / "credits_Python.prompt"
    external_prompt.write_text("% external prompt (must not be written through)\n", encoding="utf-8")
    _write_nested_architecture_project(
        tmp_path,
        prompts_dir="prompts/backend",
        architecture_filename="missing/credits_Python.prompt",
        architecture_filepath="backend/tests/endpoint_tests/tests/credits.py",
    )
    # Remove the real internal prompt so discovery must fall through to recursion.
    (tmp_path / "prompts" / "backend" / "credits_Python.prompt").unlink()
    nested = tmp_path / "prompts" / "backend" / "sub"
    nested.mkdir()
    try:
        (nested / "credits_Python.prompt").symlink_to(external_prompt)
    except OSError:
        pytest.skip("file symlinks are unavailable")

    with pytest.raises(UnsafePromptPathError, match="resolves outside prompts root"):
        get_pdd_file_paths(
            "credits",
            "python",
            prompts_dir="prompts/backend",
            context_override="backend",
        )

    assert external_prompt.read_text(encoding="utf-8") == (
        "% external prompt (must not be written through)\n"
    )


def test_get_pdd_file_paths_context_isolation_holds_from_parent_cwd(
    tmp_path,
    monkeypatch,
):
    """Context territory must hold when resolution runs outside the project CWD.

    Sync is frequently driven from a parent/sibling directory with an absolute
    prompts root. The territory guard must anchor its ``.pddrc`` lookup at the
    project (``architecture.json``'s directory), not the process CWD — a CWD-based
    lookup finds no ``.pddrc`` and fails open, re-opening the stale sibling-context
    borrow it exists to block.
    """
    project = tmp_path / "project"
    project.mkdir()
    _write_nested_architecture_project(
        project,
        prompts_dir="prompts/backend",
        architecture_filename="frontend/credits_Python.prompt",
        architecture_filepath="frontend/credits.py",
    )
    # No frontend prompt is created — the entry is stale.
    monkeypatch.chdir(tmp_path)  # PARENT of the project; no .pddrc here.
    abs_prompts = str((project / "prompts" / "backend").resolve())

    paths = get_pdd_file_paths(
        "credits",
        "python",
        prompts_dir=abs_prompts,
        context_override="backend",
    )

    code = paths["code"].resolve(strict=False).as_posix()
    assert not code.endswith("frontend/credits.py")
    assert code.endswith("backend/functions/credits.py")


def test_find_prompt_file_direct_fast_path_rejects_escaping_symlink(tmp_path):
    """The direct/case-insensitive fast path must not return an escaping symlink.

    The exact expected prompt (``prompts/backend/credits_Python.prompt``) can itself
    be a file symlink to a target outside the root. `_find_prompt_file` must not
    return it — otherwise a later update opens it with ``"w"`` and truncates the
    external file. Containment must gate Step 1 too, not only recursive candidates.
    """
    prompts_root = tmp_path / "prompts" / "backend"
    prompts_root.mkdir(parents=True)
    external_dir = tmp_path / "outside"
    external_dir.mkdir()
    external = external_dir / "credits_Python.prompt"
    external.write_text("% external (must not be written through)\n", encoding="utf-8")
    try:
        (prompts_root / "credits_Python.prompt").symlink_to(external)
    except OSError:
        pytest.skip("file symlinks are unavailable")

    with pytest.raises(UnsafePromptPathError, match="resolves outside prompts root"):
        _find_prompt_file(
            "credits", "python", prompts_root, tmp_path / "architecture.json"
        )


def test_find_prompt_file_preserves_in_root_symlink_alias(tmp_path):
    """An in-root symlink alias (target inside the root) must still resolve."""
    prompts_root = tmp_path / "prompts"
    prompts_root.mkdir()
    real = prompts_root / "real_credits_Python.prompt"
    real.write_text("% real in-root prompt\n", encoding="utf-8")
    try:
        (prompts_root / "credits_Python.prompt").symlink_to(real)
    except OSError:
        pytest.skip("file symlinks are unavailable")

    result = _find_prompt_file("credits", "python", prompts_root, tmp_path / "architecture.json")

    assert result is not None
    assert Path(result).resolve().is_relative_to(prompts_root.resolve())


def test_get_pdd_file_paths_broad_root_context_selection_from_parent_cwd(
    tmp_path,
    monkeypatch,
):
    """Same-leaf prompts in sibling contexts must resolve by requested context, not CWD.

    With a broad, project-level prompts root, two contexts owning a same-leaf prompt,
    and resolution driven from the project's parent directory, `_find_prompt_file`
    must load the context prefix (anchored at the prompts root, not the CWD) so the
    Step-4 tie-break picks the requested context — not the shallowest/lexicographic
    first match (backend).
    """
    project = tmp_path / "project"
    for ctx in ("backend", "frontend"):
        d = project / "prompts" / ctx
        d.mkdir(parents=True)
        (d / "credits_Python.prompt").write_text(f"% {ctx} credits\n", encoding="utf-8")
    (project / ".pdd" / "meta").mkdir(parents=True)
    (project / ".pdd" / "locks").mkdir(parents=True)
    (project / ".pddrc").write_text(
        "contexts:\n"
        "  backend:\n    paths: [\"backend/**\", \"prompts/backend/**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts/backend\"\n"
        "      generate_output_path: \"backend/functions/\"\n"
        "  frontend:\n    paths: [\"frontend/**\", \"prompts/frontend/**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts/frontend\"\n"
        "      generate_output_path: \"frontend/src/\"\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)  # PARENT of the project.
    abs_prompts = str((project / "prompts").resolve())  # BROAD root spanning both contexts.

    paths = get_pdd_file_paths(
        "credits",
        "python",
        prompts_dir=abs_prompts,
        context_override="frontend",
    )

    resolved = paths["prompt"].resolve(strict=False).as_posix()
    assert "/prompts/frontend/" in resolved
    assert "/prompts/backend/" not in resolved


def test_get_pdd_file_paths_parses_architecture_once(tmp_path, monkeypatch):
    """Prompt discovery and code-path selection must share ONE architecture snapshot.

    Parsing architecture.json separately per phase opens a window where an atomic
    rewrite between phases pairs a prompt from the old registry with a code target
    from the new one (torn pair). The nested prompt below forces the architecture
    hint (Step 3) AND the code-path lookup, both of which previously reparsed the
    file; a single snapshot means exactly one parse.
    """
    import sync_determine_operation as sync_determine_module

    monkeypatch.chdir(tmp_path)
    pdir = tmp_path / "prompts" / "backend" / "deep"
    pdir.mkdir(parents=True)
    (pdir / "credits_Python.prompt").write_text("% nested credits\n", encoding="utf-8")
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)
    (tmp_path / ".pddrc").write_text(
        "contexts:\n  backend:\n    paths: [\"backend/**\", \"prompts/backend/**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts/backend\"\n"
        "      generate_output_path: \"backend/functions/\"\n"
        "      outputs:\n        code:\n          path: \"backend/functions/{name}.py\"\n",
        encoding="utf-8",
    )
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [
            {"filename": "deep/credits_Python.prompt", "filepath": "backend/functions/credits.py"}
        ]}),
        encoding="utf-8",
    )

    parses = {"n": 0}
    original = sync_determine_module.extract_modules

    def counting(arch):
        parses["n"] += 1
        return original(arch)

    monkeypatch.setattr(sync_determine_module, "extract_modules", counting)

    paths = get_pdd_file_paths(
        "credits",
        "python",
        prompts_dir="prompts/backend",
        context_override="backend",
    )

    assert parses["n"] == 1
    assert paths["prompt"].resolve(strict=False).as_posix().endswith(
        "prompts/backend/deep/credits_Python.prompt"
    )
    assert paths["code"].resolve(strict=False).as_posix().endswith(
        "backend/functions/credits.py"
    )


def _write_two_context_pddrc(root):
    (root / ".pdd" / "meta").mkdir(parents=True)
    (root / ".pdd" / "locks").mkdir(parents=True)
    (root / ".pddrc").write_text(
        "contexts:\n"
        "  backend:\n    paths: [\"backend/**\", \"prompts/backend/**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts/backend\"\n"
        "      generate_output_path: \"backend/functions/\"\n"
        "      outputs:\n        code:\n          path: \"backend/functions/{name}.py\"\n"
        "  frontend:\n    paths: [\"frontend/**\", \"prompts/frontend/**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts/frontend\"\n"
        "      generate_output_path: \"frontend/src/\"\n",
        encoding="utf-8",
    )


def test_get_pdd_file_paths_arch_hint_respects_context_from_broad_root(tmp_path, monkeypatch):
    """A broad-root backend resolution must not borrow a sibling frontend arch row.

    With the project-level prompts root, `_find_prompt_file`'s architecture hint runs
    a bare-leaf lookup. If it ignores context ownership it returns the frontend row's
    prompt (and code) via the direct join, before the context-aware recursive fallback
    runs — so `pdd sync credits` in the backend context overwrites frontend/credits.py.
    The hint must reject a row whose filepath is outside the resolving context.
    """
    for ctx in ("backend", "frontend"):
        d = tmp_path / "prompts" / ctx
        d.mkdir(parents=True)
        (d / "credits_Python.prompt").write_text(f"% {ctx} credits\n", encoding="utf-8")
    _write_two_context_pddrc(tmp_path)
    # Only a frontend row exists (no backend row => no ambiguity error).
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [
            {"filename": "frontend/credits_Python.prompt", "filepath": "frontend/credits.py"}
        ]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "credits", "python",
        prompts_dir=str((tmp_path / "prompts").resolve()),
        context_override="backend",
    )

    assert "/prompts/backend/" in paths["prompt"].resolve(strict=False).as_posix()
    assert not paths["code"].resolve(strict=False).as_posix().endswith("frontend/credits.py")


def test_get_pdd_file_paths_unsafe_same_leaf_row_does_not_block_valid_module(tmp_path, monkeypatch):
    """An unsafe same-leaf architecture row must not raise AmbiguousModuleError.

    A valid ``foo_Python.prompt`` row plus an unsafe ``../../foo_Python.prompt`` row
    share the leaf ``foo``. The unsafe row is rejected before generation; it must also
    be excluded from ambiguity counting, otherwise its collision with the valid row
    blocks a legitimate module instead of resolving to the safe target.
    """
    (tmp_path / "prompts").mkdir()
    (tmp_path / "prompts" / "foo_Python.prompt").write_text("% foo\n", encoding="utf-8")
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)
    (tmp_path / ".pddrc").write_text(
        "contexts:\n  default:\n    paths: [\"**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts\"\n      generate_output_path: \"src/\"\n",
        encoding="utf-8",
    )
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [
            {"filename": "foo_Python.prompt", "filepath": "src/foo.py"},
            {"filename": "../../foo_Python.prompt", "filepath": "escaped/foo.py"},
        ]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths("foo", "python", prompts_dir="prompts")  # must NOT raise

    assert paths["code"].resolve(strict=False).as_posix().endswith("src/foo.py")


def test_get_pdd_file_paths_null_filename_uses_architecture_filepath(tmp_path, monkeypatch):
    """A module with ``"filename": null`` must resolve to its architecture filepath.

    Coercing the null filename avoids ``None.lower()`` (an AttributeError the broad
    fallback swallows into a cwd-relative default); the module is then matched by its
    filepath stem and resolves to the architecture-declared ``src/foo.py``.
    """
    (tmp_path / "prompts").mkdir()
    (tmp_path / "prompts" / "foo_Python.prompt").write_text("% foo\n", encoding="utf-8")
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)
    (tmp_path / ".pddrc").write_text(
        "contexts:\n  default:\n    paths: [\"**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts\"\n      generate_output_path: \"src/\"\n",
        encoding="utf-8",
    )
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [{"filename": None, "filepath": "src/foo.py"}]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths("foo", "python", prompts_dir="prompts")

    assert paths["code"].resolve(strict=False).as_posix().endswith("src/foo.py")


def test_get_pdd_file_paths_flat_legacy_row_respects_context_territory(tmp_path, monkeypatch):
    """A FLAT legacy same-leaf row must not bypass context ownership.

    The leaf-match and filepath-stem borrows already apply territory, but the
    basename+language match loop did not. A stale sibling row with a flat
    ``credits_Python.prompt`` filename pointing at ``frontend/credits.py`` could be
    borrowed by a backend resolution, overwriting sibling-context code.
    """
    (tmp_path / "prompts" / "backend").mkdir(parents=True)
    (tmp_path / "prompts" / "backend" / "credits_Python.prompt").write_text("% backend\n", encoding="utf-8")
    _write_two_context_pddrc(tmp_path)
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [
            {"filename": "credits_Python.prompt", "filepath": "frontend/credits.py"}
        ]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "credits", "python",
        prompts_dir=str((tmp_path / "prompts").resolve()),
        context_override="backend",
    )

    assert not paths["code"].resolve(strict=False).as_posix().endswith("frontend/credits.py")


def test_get_pdd_file_paths_canonical_target_resolves_from_parent_cwd(tmp_path, monkeypatch):
    """A path-qualified canonical target must resolve when run from a parent CWD.

    `_get_filepath_from_architecture` re-detected the context and stripped the
    basename prefix via a CWD-based `.pddrc` lookup. From the project's parent with an
    absolute prompts root, that missed the context, so the canonical
    ``backend/services/foo.py`` row failed to align with ``backend/foo`` and resolution
    fell back to the default ``backend/functions/foo.py``. The lookup must anchor at
    the project and prefer the resolved context.
    """
    project = tmp_path / "project"
    (project / "prompts" / "backend").mkdir(parents=True)
    (project / "prompts" / "backend" / "foo_Python.prompt").write_text("% backend foo\n", encoding="utf-8")
    _write_two_context_pddrc(project)
    (project / "architecture.json").write_text(
        json.dumps({"modules": [
            {"filename": "backend/services/foo_Python.prompt", "filepath": "backend/services/foo.py"}
        ]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)  # PARENT of the project.

    paths = get_pdd_file_paths(
        "backend/foo", "python",
        prompts_dir=str((project / "prompts").resolve()),
        context_override="backend",
    )

    assert paths["code"].resolve(strict=False).as_posix().endswith("backend/services/foo.py")


@pytest.mark.parametrize(
    "unsafe_filepath",
    ["../../outside/foo.py", "/tmp/pdd-outside-foo.py", "D:/outside/foo.py"],
)
def test_get_pdd_file_paths_unsafe_filepath_row_does_not_block_valid_module(
    tmp_path, monkeypatch, unsafe_filepath
):
    """An unsafe OUTPUT path on a same-filename row must not cause false ambiguity.

    A valid ``foo_Python.prompt -> src/foo.py`` row plus a same-filename row targeting
    an unsafe filepath (absolute, ``..``, or Windows drive) must not read as two
    distinct targets — the unsafe row is rejected before generation and must be
    excluded from ambiguity counting so the valid module still resolves.
    """
    (tmp_path / "prompts").mkdir()
    (tmp_path / "prompts" / "foo_Python.prompt").write_text("% foo\n", encoding="utf-8")
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)
    (tmp_path / ".pddrc").write_text(
        "contexts:\n  default:\n    paths: [\"**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts\"\n      generate_output_path: \"src/\"\n",
        encoding="utf-8",
    )
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [
            {"filename": "foo_Python.prompt", "filepath": "src/foo.py"},
            {"filename": "foo_Python.prompt", "filepath": unsafe_filepath},
        ]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths("foo", "python", prompts_dir="prompts")  # must NOT raise

    assert paths["code"].resolve(strict=False).as_posix().endswith("src/foo.py")


def test_get_pdd_file_paths_context_inferred_from_parent_cwd_without_override(tmp_path, monkeypatch):
    """Context must be inferable from a parent CWD even with NO explicit override.

    ``_resolve_context_name_for_basename`` searched from the process CWD, so a
    path-qualified ``backend/foo`` run from the project's parent (no override) failed to
    detect the backend context and missed the canonical ``backend/services/foo.py``,
    falling back to ``backend/functions/foo.py``. The lookup must anchor at the prompts
    root.
    """
    project = tmp_path / "project"
    (project / "prompts" / "backend").mkdir(parents=True)
    (project / "prompts" / "backend" / "foo_Python.prompt").write_text("% foo\n", encoding="utf-8")
    _write_two_context_pddrc(project)
    (project / "architecture.json").write_text(
        json.dumps({"modules": [
            {"filename": "backend/services/foo_Python.prompt", "filepath": "backend/services/foo.py"}
        ]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)  # PARENT; note: NO context_override below.

    paths = get_pdd_file_paths(
        "backend/foo", "python", prompts_dir=str((project / "prompts").resolve()),
    )

    assert paths["code"].resolve(strict=False).as_posix().endswith("backend/services/foo.py")


def test_get_pdd_file_paths_custom_root_finds_existing_prompt_from_parent_cwd(tmp_path, monkeypatch):
    """Custom-root prompt discovery must strip the context prefix from a parent CWD.

    `_find_prompt_file` built its basename candidates and did prefix stripping via a
    CWD-based `.pddrc` lookup. From a parent CWD with a custom prompt root, the context
    prefix was not stripped, so an existing ``specs/services/utils/foo_Python.prompt``
    was missed and a duplicated ``specs/services/backend/utils/foo_Python.prompt`` was
    returned (risking a duplicate prompt). The anchor must reach candidate building.
    """
    project = tmp_path / "project"
    (project / "specs" / "services" / "utils").mkdir(parents=True)
    existing = project / "specs" / "services" / "utils" / "foo_Python.prompt"
    existing.write_text("% existing\n", encoding="utf-8")
    (project / ".pdd" / "meta").mkdir(parents=True)
    (project / ".pdd" / "locks").mkdir(parents=True)
    (project / ".pddrc").write_text(
        "contexts:\n  backend:\n    paths: [\"backend/**\", \"specs/services/**\"]\n"
        "    defaults:\n      prompts_dir: \"specs/services\"\n"
        "      generate_output_path: \"backend/functions/\"\n",
        encoding="utf-8",
    )
    (project / "architecture.json").write_text(json.dumps({"modules": []}), encoding="utf-8")
    monkeypatch.chdir(tmp_path)  # PARENT.

    paths = get_pdd_file_paths(
        "backend/utils/foo", "python",
        prompts_dir=str((project / "specs" / "services").resolve()),
        context_override="backend",
    )

    assert paths["prompt"].resolve(strict=False) == existing.resolve()


def test_get_pdd_file_paths_example_test_templates_not_duplicated_from_parent_cwd(tmp_path, monkeypatch):
    """Example/test artifact paths must not duplicate the context prefix from a parent CWD.

    ``construct_paths_basename`` was stripped via a CWD-based `.pddrc` lookup, so from a
    parent CWD a path-qualified ``backend/foo`` kept its ``backend/`` prefix and produced
    ``backend/examples/backend/foo_example.py``. Anchoring the strip yields the
    configured, non-duplicated paths.
    """
    project = tmp_path / "project"
    (project / "prompts" / "backend").mkdir(parents=True)
    (project / "prompts" / "backend" / "foo_Python.prompt").write_text("% foo\n", encoding="utf-8")
    (project / ".pdd" / "meta").mkdir(parents=True)
    (project / ".pdd" / "locks").mkdir(parents=True)
    # Exact example/test TEMPLATES with {category}: the category is the basename's
    # directory part, which duplicates the `backend/` prefix if the basename is not
    # stripped to `foo` (which requires the CWD-independent .pddrc anchor).
    (project / ".pddrc").write_text(
        "contexts:\n  backend:\n    paths: [\"backend/**\", \"prompts/backend/**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts/backend\"\n"
        "      generate_output_path: \"backend/functions/\"\n"
        "      outputs:\n"
        "        example:\n          path: \"backend/examples/{category}/{name}_example.py\"\n"
        "        test:\n          path: \"backend/tests/{category}/test_{name}.py\"\n",
        encoding="utf-8",
    )
    (project / "architecture.json").write_text(
        json.dumps({"modules": [
            {"filename": "backend/foo_Python.prompt", "filepath": "backend/functions/foo.py"}
        ]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)  # PARENT.

    paths = get_pdd_file_paths(
        "backend/foo", "python", prompts_dir=str((project / "prompts").resolve()),
        context_override="backend",
    )

    assert "examples/backend/" not in paths["example"].resolve(strict=False).as_posix()
    assert "tests/backend/" not in paths["test"].resolve(strict=False).as_posix()


def test_architecture_module_choices_defers_containment_to_matches(tmp_path, monkeypatch):
    """Ambiguity counting must not filesystem-resolve every module's filepath.

    Containment resolution is O(filesystem) and must run only for the handful of rows
    whose filename/stem actually matches the requested basename, not for every module —
    otherwise a large architecture makes each lookup many times slower.
    """
    import sync_determine_operation as sync_determine_module

    modules = [
        {"filename": f"m{i}_Python.prompt", "filepath": f"src/m{i}.py"} for i in range(300)
    ]
    modules.append({"filename": "foo_Python.prompt", "filepath": "src/foo.py"})
    (tmp_path / "architecture.json").write_text(json.dumps({"modules": modules}), encoding="utf-8")

    calls = {"n": 0}
    original = sync_determine_module._contained_architecture_code_path

    def counting(project_root, filepath):
        calls["n"] += 1
        return original(project_root, filepath)

    monkeypatch.setattr(sync_determine_module, "_contained_architecture_code_path", counting)

    choices = sync_determine_module._architecture_module_choices(
        tmp_path / "architecture.json", "foo", "python", modules=modules
    )

    assert choices == ["src/foo.py"]
    assert calls["n"] <= 5  # only the matching row(s), not all 301 modules.


def test_get_pdd_file_paths_new_module_outputs_under_subproject_from_parent_cwd(tmp_path, monkeypatch):
    """A NEW module's outputs must resolve under the subproject, not the parent CWD.

    The missing-prompt branch called construct_paths with no anchoring input and
    forced ``path_resolution_mode="cwd"``, so from the project's parent the code/test
    paths resolved under the parent (``<parent>/backend/foo.py``). Passing the prompt
    path as a hint lets construct_paths find the subproject ``.pddrc`` and resolve
    against it.
    """
    project = tmp_path / "project"
    (project / "prompts" / "backend").mkdir(parents=True)  # NOTE: no foo prompt (new module)
    _write_two_context_pddrc(project)
    (project / "architecture.json").write_text(json.dumps({"modules": []}), encoding="utf-8")
    monkeypatch.chdir(tmp_path)  # PARENT.

    paths = get_pdd_file_paths(
        "foo", "python",
        prompts_dir=str((project / "prompts" / "backend").resolve()),
        context_override="backend",
    )

    code = paths["code"].resolve(strict=False)
    assert str(code).startswith(str(project.resolve()))
    assert code.as_posix().endswith("backend/functions/foo.py")


def test_get_pdd_file_paths_non_architecture_templates_not_duplicated_from_parent_cwd(tmp_path, monkeypatch):
    """Existing-prompt template paths (no architecture entry) must not duplicate the prefix.

    The non-architecture template branch recomputed the basename without the project
    anchor, so from a parent CWD a `{category}` template duplicated the context prefix
    (`backend/examples/backend/foo_example.py`).
    """
    project = tmp_path / "project"
    (project / "prompts" / "backend").mkdir(parents=True)
    (project / "prompts" / "backend" / "foo_Python.prompt").write_text("% foo\n", encoding="utf-8")
    (project / ".pdd" / "meta").mkdir(parents=True)
    (project / ".pdd" / "locks").mkdir(parents=True)
    (project / ".pddrc").write_text(
        "contexts:\n  backend:\n    paths: [\"backend/**\", \"prompts/backend/**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts/backend\"\n"
        "      generate_output_path: \"backend/functions/\"\n"
        "      outputs:\n"
        "        example:\n          path: \"backend/examples/{category}/{name}_example.py\"\n"
        "        test:\n          path: \"backend/tests/{category}/test_{name}.py\"\n",
        encoding="utf-8",
    )
    # No architecture entry for foo — exercise the non-architecture template branch.
    (project / "architecture.json").write_text(json.dumps({"modules": []}), encoding="utf-8")
    monkeypatch.chdir(tmp_path)  # PARENT.

    paths = get_pdd_file_paths(
        "backend/foo", "python", prompts_dir=str((project / "prompts").resolve()),
        context_override="backend",
    )

    assert "examples/backend/" not in paths["example"].resolve(strict=False).as_posix()
    assert "tests/backend/" not in paths["test"].resolve(strict=False).as_posix()


def test_get_pdd_file_paths_proven_owner_honored_for_shared_target(tmp_path, monkeypatch):
    """A PROVEN-owner architecture row keeps a shared, no-context code target.

    When an architecture row's physical prompt owner IS the resolved prompt (proven,
    explicit mapping), its authoritative code target must be honored even when it lies
    outside the context's own globs — as long as it belongs to NO sibling context
    (an intentionally shared path). Territory only guards heuristic borrows.
    """
    (tmp_path / "prompts" / "backend").mkdir(parents=True)
    (tmp_path / "prompts" / "backend" / "foo_Python.prompt").write_text("% foo\n", encoding="utf-8")
    _write_two_context_pddrc(tmp_path)
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [
            {"filename": "backend/foo_Python.prompt", "filepath": "shared/foo.py"}
        ]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "foo", "python", prompts_dir="prompts/backend", context_override="backend",
    )

    assert paths["code"].resolve(strict=False).as_posix().endswith("shared/foo.py")


def test_get_pdd_file_paths_proven_owner_still_rejects_sibling_context_target(tmp_path, monkeypatch):
    """The proven-owner exception must NOT extend to a SIBLING context's territory.

    A stale flat row (`credits_Python.prompt` -> `frontend/credits.py`) leaf-collides
    with the backend prompt and thus proves ownership, but its target is owned by the
    frontend context — it must still be rejected, or backend sync overwrites frontend
    code. This locks in the round-5 behavior against the round-7 proven-owner relaxation.
    """
    (tmp_path / "prompts" / "backend").mkdir(parents=True)
    (tmp_path / "prompts" / "backend" / "credits_Python.prompt").write_text("% backend\n", encoding="utf-8")
    _write_two_context_pddrc(tmp_path)
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [
            {"filename": "credits_Python.prompt", "filepath": "frontend/credits.py"}
        ]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "credits", "python", prompts_dir=str((tmp_path / "prompts").resolve()),
        context_override="backend",
    )

    assert not paths["code"].resolve(strict=False).as_posix().endswith("frontend/credits.py")


def test_get_pdd_file_paths_existing_prompt_template_anchored_from_parent_cwd(tmp_path, monkeypatch):
    """An EXISTING prompt's template outputs must anchor at the subproject too.

    Round 7 anchored only the missing-prompt template branch; the existing-prompt
    branch still returned project-relative paths, so from a parent CWD an existing
    prompt's example/test resolved under the parent.
    """
    project = tmp_path / "project"
    (project / "prompts" / "backend").mkdir(parents=True)
    (project / "prompts" / "backend" / "foo_Python.prompt").write_text("% foo\n", encoding="utf-8")
    (project / ".pdd" / "meta").mkdir(parents=True)
    (project / ".pdd" / "locks").mkdir(parents=True)
    (project / ".pddrc").write_text(
        "contexts:\n  backend:\n    paths: [\"backend/**\", \"prompts/backend/**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts/backend\"\n"
        "      generate_output_path: \"backend/functions/\"\n"
        "      outputs:\n"
        "        example:\n          path: \"backend/examples/{name}_example.py\"\n"
        "        test:\n          path: \"backend/tests/test_{name}.py\"\n",
        encoding="utf-8",
    )
    (project / "architecture.json").write_text(json.dumps({"modules": []}), encoding="utf-8")
    monkeypatch.chdir(tmp_path)  # PARENT.

    paths = get_pdd_file_paths(
        "backend/foo", "python", prompts_dir=str((project / "prompts").resolve()),
        context_override="backend",
    )

    assert str(paths["example"].resolve(strict=False)).startswith(str(project.resolve()))
    assert str(paths["test"].resolve(strict=False)).startswith(str(project.resolve()))


def test_get_pdd_file_paths_absolute_sibling_output_path_still_isolates(tmp_path, monkeypatch):
    """A sibling context with an ABSOLUTE output path must still own its code.

    `_filepath_matches_context` compared raw config prefixes against the project-relative
    architecture value, so an absolute `generate_output_path` never matched and the
    sibling context stopped owning its code — a stale flat row targeting `frontend/`
    was then accepted by a backend resolution. Absolute config paths are now
    re-expressed relative to the project before comparison.
    """
    (tmp_path / "prompts" / "backend").mkdir(parents=True)
    (tmp_path / "prompts" / "backend" / "credits_Python.prompt").write_text("% backend\n", encoding="utf-8")
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)
    abs_frontend = (tmp_path / "frontend").resolve().as_posix()
    # Frontend's relative paths do NOT cover frontend/credits.py; only its ABSOLUTE
    # generate_output_path does.
    (tmp_path / ".pddrc").write_text(
        "contexts:\n"
        "  backend:\n    paths: [\"backend/**\", \"prompts/backend/**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts/backend\"\n"
        "      generate_output_path: \"backend/functions/\"\n"
        "  frontend:\n    paths: [\"frontend/src/**\"]\n"
        f"    defaults:\n      prompts_dir: \"prompts/frontend\"\n      generate_output_path: \"{abs_frontend}/\"\n",
        encoding="utf-8",
    )
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [
            {"filename": "credits_Python.prompt", "filepath": "frontend/credits.py"}
        ]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "credits", "python", prompts_dir=str((tmp_path / "prompts").resolve()),
        context_override="backend",
    )

    assert not paths["code"].resolve(strict=False).as_posix().endswith("frontend/credits.py")


def test_get_pdd_file_paths_flat_hint_selects_requested_context_prompt(tmp_path, monkeypatch):
    """A legacy FLAT architecture hint must resolve the prompt in the REQUESTED context.

    When a flat architecture filename matches the same leaf in two context subdirs,
    `_resolve_prompt_path_from_architecture` sorted the recursive matches without
    context and returned the shallowest/lexicographic first — so a `frontend` request
    got the `backend` prompt while code resolved under `frontend` (a torn pair). The
    recursive search now prefers the resolving context's prefix.
    """
    for ctx in ("backend", "frontend"):
        d = tmp_path / "prompts" / ctx
        d.mkdir(parents=True)
        (d / "credits_Python.prompt").write_text(f"% {ctx}\n", encoding="utf-8")
    _write_two_context_pddrc(tmp_path)
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [
            {"filename": "credits_Python.prompt", "filepath": "frontend/credits.py"}
        ]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "credits", "python", prompts_dir=str((tmp_path / "prompts").resolve()),
        context_override="frontend",
    )

    resolved = paths["prompt"].resolve(strict=False).as_posix()
    assert "/prompts/frontend/" in resolved
    assert "/prompts/backend/" not in resolved


def test_get_pdd_file_paths_exact_flat_row_respects_sibling_territory(tmp_path, monkeypatch):
    """An exact flat filename row cannot redirect a narrowed root to sibling code."""
    backend_prompts = tmp_path / "prompts" / "backend"
    backend_prompts.mkdir(parents=True)
    (backend_prompts / "credits_Python.prompt").write_text("% backend\n", encoding="utf-8")
    _write_two_context_pddrc(tmp_path)
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [
            {"filename": "credits_Python.prompt", "filepath": "frontend/credits.py"}
        ]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "credits", "python", prompts_dir="prompts/backend", context_override="backend",
    )

    assert paths["code"].resolve(strict=False) == (
        tmp_path / "backend" / "functions" / "credits.py"
    ).resolve(strict=False)


def test_get_pdd_file_paths_context_prefix_matches_path_components(tmp_path, monkeypatch):
    """The backend context must not select a lexicographically earlier a-backend prompt."""
    for context in ("a-backend", "backend"):
        prompt_dir = tmp_path / "prompts" / context
        prompt_dir.mkdir(parents=True)
        (prompt_dir / "credits_Python.prompt").write_text(
            f"% {context}\n", encoding="utf-8"
        )
    _write_two_context_pddrc(tmp_path)
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [
            {"filename": "credits_Python.prompt", "filepath": "backend/functions/credits.py"}
        ]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "credits", "python", prompts_dir="prompts", context_override="backend",
    )

    resolved = paths["prompt"].resolve(strict=False).as_posix()
    assert "/prompts/backend/" in resolved
    assert "/prompts/a-backend/" not in resolved


def test_get_pdd_file_paths_absolute_sibling_prompt_root_establishes_owner(
    tmp_path,
    monkeypatch,
):
    """Contained absolute sibling prompt roots participate in ownership discovery."""
    backend_root = tmp_path / "apps" / "backend" / "specs"
    frontend_root = tmp_path / "apps" / "frontend" / "specs"
    backend_root.mkdir(parents=True)
    (frontend_root / "frontend").mkdir(parents=True)
    (backend_root / "credits_Python.prompt").write_text("% backend\n", encoding="utf-8")
    (frontend_root / "frontend" / "credits_Python.prompt").write_text(
        "% frontend\n", encoding="utf-8"
    )
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)
    (tmp_path / ".pddrc").write_text(
        "contexts:\n"
        "  backend:\n    paths: [\"backend/**\"]\n"
        f"    defaults:\n      prompts_dir: \"{backend_root.as_posix()}\"\n"
        "      generate_output_path: \"backend/generated/\"\n"
        "  frontend:\n    paths: [\"frontend/**\"]\n"
        f"    defaults:\n      prompts_dir: \"{frontend_root.as_posix()}\"\n"
        "      generate_output_path: \"frontend/generated/\"\n",
        encoding="utf-8",
    )
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [{
            "filename": "frontend/credits_Python.prompt",
            "filepath": "backend/foreign/credits.py",
        }]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "credits", "python", prompts_dir=str(backend_root), context_override="backend",
    )

    assert paths["code"].resolve(strict=False) == (
        tmp_path / "backend" / "generated" / "credits.py"
    ).resolve(strict=False)
    assert not paths["code"].resolve(strict=False).as_posix().endswith(
        "backend/foreign/credits.py"
    )


def test_get_pdd_file_paths_repo_root_output_still_rejects_sibling_target(
    tmp_path,
    monkeypatch,
):
    """A repo-root current output cannot override explicit sibling ownership."""
    backend_prompts = tmp_path / "prompts" / "backend"
    backend_prompts.mkdir(parents=True)
    (backend_prompts / "credits_Python.prompt").write_text("% backend\n", encoding="utf-8")
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)
    (tmp_path / ".pddrc").write_text(
        "contexts:\n"
        "  backend:\n    paths: [\"prompts/backend/**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts/backend\"\n"
        "      generate_output_path: \"./\"\n"
        "  frontend:\n    paths: [\"frontend/**\", \"prompts/frontend/**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts/frontend\"\n"
        "      generate_output_path: \"frontend/\"\n",
        encoding="utf-8",
    )
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [{
            "filename": "credits_Python.prompt",
            "filepath": "frontend/credits.py",
        }]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "credits", "python", prompts_dir="prompts/backend", context_override="backend",
    )

    assert not paths["code"].resolve(strict=False).as_posix().endswith(
        "frontend/credits.py"
    )


def test_get_pdd_file_paths_custom_context_prefix_is_relative_to_active_root(
    tmp_path,
    monkeypatch,
):
    """A custom broad root scopes context matches by its root-relative suffix."""
    for context in ("backend", "frontend"):
        prompt_dir = tmp_path / "specs" / context
        prompt_dir.mkdir(parents=True)
        (prompt_dir / "credits_Python.prompt").write_text(
            f"% {context}\n", encoding="utf-8"
        )
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)
    (tmp_path / ".pddrc").write_text(
        "contexts:\n"
        "  backend:\n    paths: [\"backend/**\"]\n"
        "    defaults:\n      prompts_dir: \"specs/backend\"\n"
        "      generate_output_path: \"backend/\"\n"
        "  frontend:\n    paths: [\"frontend/**\"]\n"
        "    defaults:\n      prompts_dir: \"specs/frontend\"\n"
        "      generate_output_path: \"frontend/\"\n",
        encoding="utf-8",
    )
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [{
            "filename": "credits_Python.prompt",
            "filepath": "frontend/credits.py",
        }]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "credits", "python", prompts_dir="specs", context_override="frontend",
    )

    resolved = paths["prompt"].resolve(strict=False).as_posix()
    assert "/specs/frontend/" in resolved
    assert "/specs/backend/" not in resolved


def test_get_pdd_file_paths_does_not_reconstruct_escaping_direct_symlink(
    tmp_path,
    monkeypatch,
):
    """Fallback must not return a direct symlink rejected by prompt discovery."""
    prompts_root = tmp_path / "prompts"
    prompts_root.mkdir()
    external = tmp_path / "external.prompt"
    original = "% external (must remain unchanged)\n"
    external.write_text(original, encoding="utf-8")
    try:
        (prompts_root / "credits_Python.prompt").symlink_to(external)
    except OSError:
        pytest.skip("file symlinks are unavailable")
    monkeypatch.chdir(tmp_path)

    with pytest.raises(UnsafePromptPathError, match="resolves outside prompts root"):
        get_pdd_file_paths("credits", "python", prompts_dir="prompts")

    assert external.read_text(encoding="utf-8") == original


def test_get_pdd_file_paths_missing_custom_module_keeps_context_root(
    tmp_path,
    monkeypatch,
):
    """A path-qualified new module lands under its custom context prompt root."""
    (tmp_path / "specs").mkdir()
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)
    (tmp_path / ".pddrc").write_text(
        "contexts:\n"
        "  frontend:\n    paths: [\"frontend/**\"]\n"
        "    defaults:\n      prompts_dir: \"specs/frontend\"\n"
        "      generate_output_path: \"frontend/\"\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "frontend/foo", "python", prompts_dir="specs", context_override="frontend",
    )

    assert paths["prompt"].resolve(strict=False) == (
        tmp_path / "specs" / "frontend" / "foo_python.prompt"
    ).resolve(strict=False)
    code = paths["code"].resolve(strict=False).as_posix()
    assert code.endswith("/frontend/foo.py")
    assert "/frontend/frontend/" not in code


def test_get_pdd_file_paths_sibling_root_output_does_not_veto_current_target(
    tmp_path,
    monkeypatch,
):
    """A sibling ``./`` output does not claim a current-context architecture path."""
    backend_prompts = tmp_path / "prompts" / "backend"
    backend_prompts.mkdir(parents=True)
    (backend_prompts / "foo_Python.prompt").write_text("% backend\n", encoding="utf-8")
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)
    (tmp_path / ".pddrc").write_text(
        "contexts:\n"
        "  backend:\n    paths: [\"backend/**\", \"prompts/backend/**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts/backend\"\n"
        "      generate_output_path: \"backend/functions/\"\n"
        "  frontend:\n    paths: [\"prompts/frontend/**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts/frontend\"\n"
        "      generate_output_path: \"./\"\n",
        encoding="utf-8",
    )
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [{
            "filename": "foo_Python.prompt",
            "filepath": "backend/special/foo.py",
        }]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "foo", "python", prompts_dir="prompts/backend", context_override="backend",
    )

    assert paths["code"].resolve(strict=False) == (
        tmp_path / "backend" / "special" / "foo.py"
    ).resolve(strict=False)


def test_get_pdd_file_paths_nested_escaping_symlink_is_hard_failure(
    tmp_path,
    monkeypatch,
):
    """An unsafe recursive match cannot be downgraded to a new-module fallback."""
    prompts_root = tmp_path / "prompts"
    nested = prompts_root / "nested"
    nested.mkdir(parents=True)
    external = tmp_path / "external.prompt"
    original = "% external (must remain unchanged)\n"
    external.write_text(original, encoding="utf-8")
    try:
        (nested / "credits_Python.prompt").symlink_to(external)
    except OSError:
        pytest.skip("file symlinks are unavailable")
    monkeypatch.chdir(tmp_path)

    with pytest.raises(UnsafePromptPathError, match="resolves outside prompts root"):
        get_pdd_file_paths("credits", "python", prompts_dir="prompts")

    assert external.read_text(encoding="utf-8") == original


def test_get_pdd_file_paths_loads_territory_config_once_for_duplicate_rows(
    tmp_path,
    monkeypatch,
):
    """Matching architecture rows share one context-territory config snapshot."""
    import sync_determine_operation as sync_determine_module

    backend_prompts = tmp_path / "prompts" / "backend"
    backend_prompts.mkdir(parents=True)
    (backend_prompts / "credits_Python.prompt").write_text("% backend\n", encoding="utf-8")
    _write_two_context_pddrc(tmp_path)
    rows = [
        {
            "filename": "stale/credits_Python.prompt",
            "filepath": "frontend/credits.py",
        }
        for _ in range(500)
    ]
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": rows}), encoding="utf-8"
    )
    original_load = sync_determine_module._load_pddrc_config
    original_owner = sync_determine_module._architecture_prompt_owner
    loads = {"count": 0}
    ownership_checks = {"count": 0}

    def counting_load(path):
        loads["count"] += 1
        return original_load(path)

    def counting_owner(*args, **kwargs):
        ownership_checks["count"] += 1
        return original_owner(*args, **kwargs)

    monkeypatch.setattr(sync_determine_module, "_load_pddrc_config", counting_load)
    monkeypatch.setattr(
        sync_determine_module, "_architecture_prompt_owner", counting_owner
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "credits", "python", prompts_dir="prompts/backend", context_override="backend",
    )

    assert not paths["code"].resolve(strict=False).as_posix().endswith(
        "frontend/credits.py"
    )
    assert loads["count"] <= 10
    assert ownership_checks["count"] <= 1


def test_get_pdd_file_paths_rejects_missing_basename_traversal(tmp_path, monkeypatch):
    """A missing module basename cannot escape prompt/output roots via ``..``."""
    (tmp_path / "prompts").mkdir()
    monkeypatch.chdir(tmp_path)

    with pytest.raises(UnsafePromptPathError, match="Unsafe prompt path"):
        get_pdd_file_paths("../outside/foo", "python", prompts_dir="prompts")

    assert not (tmp_path / "outside" / "foo_python.prompt").exists()


def test_get_pdd_file_paths_nested_missing_custom_module_keeps_context_root(
    tmp_path,
    monkeypatch,
):
    """Nested path-qualified new modules retain both context and nested segments."""
    (tmp_path / "specs").mkdir()
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)
    (tmp_path / ".pddrc").write_text(
        "contexts:\n"
        "  frontend:\n    paths: [\"frontend/**\"]\n"
        "    defaults:\n      prompts_dir: \"specs/frontend\"\n"
        "      generate_output_path: \"frontend/\"\n",
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "frontend/utils/foo",
        "python",
        prompts_dir="specs",
        context_override="frontend",
    )

    assert paths["prompt"].resolve(strict=False) == (
        tmp_path / "specs" / "frontend" / "utils" / "foo_python.prompt"
    ).resolve(strict=False)
    code = paths["code"].resolve(strict=False).as_posix()
    assert code.endswith("/frontend/utils/foo.py")
    assert "/frontend/frontend/" not in code
    test_path = paths["test"].resolve(strict=False).as_posix()
    assert test_path.endswith("/utils/test_foo.py")
    assert "/utils/utils/" not in test_path


def test_get_pdd_file_paths_ignores_unsafe_symlink_in_sibling_context(
    tmp_path,
    monkeypatch,
):
    """An unsafe frontend candidate cannot block an explicit backend new module."""
    (tmp_path / "prompts" / "backend").mkdir(parents=True)
    frontend = tmp_path / "prompts" / "frontend"
    frontend.mkdir()
    external = tmp_path / "external.prompt"
    original = "% external (must remain unchanged)\n"
    external.write_text(original, encoding="utf-8")
    try:
        (frontend / "foo_Python.prompt").symlink_to(external)
    except OSError:
        pytest.skip("file symlinks are unavailable")
    _write_two_context_pddrc(tmp_path)
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "foo", "python", prompts_dir="prompts", context_override="backend",
    )

    assert paths["prompt"].resolve(strict=False) == (
        tmp_path / "prompts" / "backend" / "foo_python.prompt"
    ).resolve(strict=False)
    assert external.read_text(encoding="utf-8") == original


def test_get_pdd_file_paths_rejects_language_traversal(tmp_path, monkeypatch):
    """Language is one filename component and cannot traverse artifact roots."""
    (tmp_path / "prompts").mkdir()
    monkeypatch.chdir(tmp_path)

    with pytest.raises(UnsafePromptPathError, match="Unsafe prompt path"):
        get_pdd_file_paths("foo", "../../../outside", prompts_dir="prompts")

    assert not (tmp_path.parent / "outside").exists()


def test_get_pdd_file_paths_active_unsafe_prompt_beats_safe_sibling(
    tmp_path,
    monkeypatch,
):
    """A safe frontend prompt cannot mask an unsafe requested backend prompt."""
    backend = tmp_path / "prompts" / "backend"
    frontend = tmp_path / "prompts" / "frontend"
    backend.mkdir(parents=True)
    frontend.mkdir()
    external = tmp_path / "external.prompt"
    original = "% external (must remain unchanged)\n"
    external.write_text(original, encoding="utf-8")
    try:
        (backend / "foo_Python.prompt").symlink_to(external)
    except OSError:
        pytest.skip("file symlinks are unavailable")
    (frontend / "foo_Python.prompt").write_text("% frontend\n", encoding="utf-8")
    _write_two_context_pddrc(tmp_path)
    monkeypatch.chdir(tmp_path)

    with pytest.raises(UnsafePromptPathError, match="resolves outside prompts root"):
        get_pdd_file_paths(
            "foo", "python", prompts_dir="prompts", context_override="backend",
        )

    assert external.read_text(encoding="utf-8") == original


def test_get_pdd_file_paths_explicit_context_does_not_borrow_safe_sibling(
    tmp_path,
    monkeypatch,
):
    """A lone safe frontend prompt is not a fallback for explicit backend creation."""
    (tmp_path / "prompts" / "backend").mkdir(parents=True)
    frontend = tmp_path / "prompts" / "frontend"
    frontend.mkdir()
    (frontend / "foo_Python.prompt").write_text("% frontend\n", encoding="utf-8")
    _write_two_context_pddrc(tmp_path)
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "foo", "python", prompts_dir="prompts", context_override="backend",
    )

    assert paths["prompt"].resolve(strict=False) == (
        tmp_path / "prompts" / "backend" / "foo_python.prompt"
    ).resolve(strict=False)


def test_get_pdd_file_paths_flat_arch_hint_aligns_path_qualified_basename(
    tmp_path,
    monkeypatch,
):
    """A flat hint cannot pair an unrelated directory's prompt with canonical code."""
    wrong = tmp_path / "prompts" / "afoo"
    wrong.mkdir(parents=True)
    (wrong / "page_Python.prompt").write_text("% wrong afoo page\n", encoding="utf-8")
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)
    (tmp_path / ".pddrc").write_text(
        "contexts:\n  default:\n    paths: [\"**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts\"\n"
        "      generate_output_path: \"src/\"\n",
        encoding="utf-8",
    )
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [{
            "filename": "page_Python.prompt",
            "filepath": "foo/page.py",
        }]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths("foo/page", "python", prompts_dir="prompts")

    assert paths["prompt"].resolve(strict=False) == (
        tmp_path / "prompts" / "foo" / "page_python.prompt"
    ).resolve(strict=False)
    assert "/prompts/afoo/" not in paths["prompt"].resolve(strict=False).as_posix()


def test_get_pdd_file_paths_direct_fast_path_respects_explicit_context(
    tmp_path,
    monkeypatch,
):
    """A root-level prompt is not a direct-path fallback for explicit backend."""
    (tmp_path / "prompts" / "backend").mkdir(parents=True)
    (tmp_path / "prompts" / "foo_Python.prompt").write_text(
        "% root-level sibling\n", encoding="utf-8"
    )
    _write_two_context_pddrc(tmp_path)
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "foo", "python", prompts_dir="prompts", context_override="backend",
    )

    assert paths["prompt"].resolve(strict=False) == (
        tmp_path / "prompts" / "backend" / "foo_python.prompt"
    ).resolve(strict=False)


def test_get_pdd_file_paths_misaligned_direct_arch_join_is_not_returned(
    tmp_path,
    monkeypatch,
):
    """A rejected flat direct join cannot be returned again as the helper fallback."""
    (tmp_path / "prompts").mkdir()
    (tmp_path / "prompts" / "page_Python.prompt").write_text(
        "% wrong root page\n", encoding="utf-8"
    )
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)
    (tmp_path / ".pddrc").write_text(
        "contexts:\n  default:\n    paths: [\"**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts\"\n"
        "      generate_output_path: \"src/\"\n",
        encoding="utf-8",
    )
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [{
            "filename": "page_Python.prompt",
            "filepath": "foo/page.py",
        }]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths("foo/page", "python", prompts_dir="prompts")

    assert paths["prompt"].resolve(strict=False) == (
        tmp_path / "prompts" / "foo" / "page_python.prompt"
    ).resolve(strict=False)
    assert paths["prompt"].resolve(strict=False) != (
        tmp_path / "prompts" / "page_Python.prompt"
    ).resolve(strict=False)


def test_get_pdd_file_paths_nested_exact_arch_filename_still_aligns_filepath(
    tmp_path,
    monkeypatch,
):
    """An exact nested filename cannot bypass path-qualified filepath alignment."""
    prompt = tmp_path / "prompts" / "foo" / "page_Python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("% foo page\n", encoding="utf-8")
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)
    (tmp_path / ".pddrc").write_text(
        "contexts:\n  default:\n    paths: [\"**\"]\n"
        "    defaults:\n      prompts_dir: \"prompts\"\n"
        "      generate_output_path: \"src/\"\n",
        encoding="utf-8",
    )
    (tmp_path / "architecture.json").write_text(
        json.dumps({"modules": [{
            "filename": "foo/page_Python.prompt",
            "filepath": "bar/page.py",
        }]}),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths("foo/page", "python", prompts_dir="prompts")

    assert paths["prompt"].resolve(strict=False) == prompt.resolve(strict=False)
    assert not paths["code"].resolve(strict=False).as_posix().endswith("bar/page.py")


def test_get_pdd_file_paths_nested_directories_match_case_insensitively(
    tmp_path,
    monkeypatch,
):
    """Linux nested lookup reuses an existing differently-cased directory path."""
    prompt = tmp_path / "prompts" / "foo" / "page_Python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("% foo page\n", encoding="utf-8")
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths("Foo/Page", "python", prompts_dir="prompts")

    assert paths["prompt"].resolve(strict=False) == prompt.resolve(strict=False)
    assert paths["prompt"].parts[-2:] == ("foo", "page_Python.prompt")


@pytest.mark.parametrize(
    ("basename", "language"),
    [
        (" foo", "python"),
        ("foo ", "python"),
        ("foo\x00bar", "python"),
        ("foo", " python"),
        ("foo", "python "),
        ("foo", "py\x00thon"),
        ("foo", "py\nthon"),
        ("foo\u202ebar", "python"),
        ("foo", "py\u2066thon"),
    ],
)
def test_get_pdd_file_paths_rejects_noncanonical_or_control_input(
    tmp_path,
    monkeypatch,
    basename,
    language,
):
    """Validation rejects controls and whitespace the caller would otherwise retain."""
    (tmp_path / "prompts").mkdir()
    monkeypatch.chdir(tmp_path)

    with pytest.raises(UnsafePromptPathError, match="Unsafe prompt path"):
        get_pdd_file_paths(basename, language, prompts_dir="prompts")


def test_get_pdd_file_paths_unsafe_root_direct_candidate_does_not_block_context(
    tmp_path,
    monkeypatch,
):
    """Containment is not evaluated for a direct candidate outside explicit context."""
    (tmp_path / "prompts" / "backend").mkdir(parents=True)
    external = tmp_path / "external.prompt"
    original = "% external (must remain unchanged)\n"
    external.write_text(original, encoding="utf-8")
    try:
        (tmp_path / "prompts" / "foo_Python.prompt").symlink_to(external)
    except OSError:
        pytest.skip("file symlinks are unavailable")
    _write_two_context_pddrc(tmp_path)
    monkeypatch.chdir(tmp_path)

    paths = get_pdd_file_paths(
        "foo", "python", prompts_dir="prompts", context_override="backend",
    )

    assert paths["prompt"].resolve(strict=False) == (
        tmp_path / "prompts" / "backend" / "foo_python.prompt"
    ).resolve(strict=False)
    assert external.read_text(encoding="utf-8") == original


@pytest.mark.parametrize("basename", [".", "./", "foo/", "foo/.", "./foo", "foo//bar"])
def test_get_pdd_file_paths_rejects_degenerate_basename(
    tmp_path,
    monkeypatch,
    basename,
):
    """Noncanonical or empty normalized basenames cannot create hidden artifacts."""
    (tmp_path / "prompts").mkdir()
    monkeypatch.chdir(tmp_path)

    with pytest.raises(UnsafePromptPathError, match="Unsafe prompt path"):
        get_pdd_file_paths(basename, "python", prompts_dir="prompts")


@pytest.mark.parametrize("basename", ["foo\nFORGED", "foo\rFORGED", "foo\x1b[31m"])
def test_get_pdd_file_paths_validates_before_logging_raw_input(
    tmp_path,
    monkeypatch,
    caplog,
    basename,
):
    """Rejected control characters never reach the INFO log record."""
    (tmp_path / "prompts").mkdir()
    monkeypatch.chdir(tmp_path)
    caplog.set_level("INFO", logger="sync_determine_operation")

    with pytest.raises(UnsafePromptPathError, match="Unsafe prompt path"):
        get_pdd_file_paths(basename, "python", prompts_dir="prompts")

    assert not caplog.records


def test_get_pdd_file_paths_rejects_control_bearing_prompts_dir_before_logging(
    tmp_path,
    monkeypatch,
    caplog,
):
    """A control-bearing prompt root is neither resolved nor emitted into INFO logs."""
    monkeypatch.chdir(tmp_path)
    caplog.set_level("INFO", logger="sync_determine_operation")

    with pytest.raises(UnsafePromptPathError, match="Unsafe prompt path"):
        get_pdd_file_paths("foo", "python", prompts_dir="prompts\nFORGED")

    assert not caplog.records


@pytest.mark.parametrize(
    "basename",
    ["foo:bar", "CON", "NUL", "COM1", "LPT9.txt", "dir/PRN.py", "AUX"],
)
def test_get_pdd_file_paths_rejects_windows_device_or_ads_basename(
    tmp_path,
    monkeypatch,
    basename,
):
    """Portable module identities cannot address NTFS streams or device names."""
    (tmp_path / "prompts").mkdir()
    monkeypatch.chdir(tmp_path)

    with pytest.raises(UnsafePromptPathError, match="Unsafe prompt path"):
        get_pdd_file_paths(basename, "python", prompts_dir="prompts")


def test_directory_index_case_collision_fallback_is_deterministic(tmp_path):
    """Case-fold collisions have a stable fallback independent of scandir order."""
    import sync_determine_operation as sync_determine_module

    lower = tmp_path / "foo"
    upper = tmp_path / "Foo"
    lower.mkdir()
    try:
        upper.mkdir()
    except FileExistsError:
        pytest.skip("filesystem does not support case-distinct sibling directories")
    if lower.samefile(upper):
        pytest.skip("filesystem is case-insensitive")

    found = sync_determine_module._indexed_directory_child(
        tmp_path, "FOO", directory=True
    )

    assert found == upper


def test_get_pdd_file_paths_rejects_symlink_architecture_escape(tmp_path, monkeypatch):
    """A relative architecture path cannot escape through an existing symlink."""
    monkeypatch.chdir(tmp_path)
    outside = tmp_path.parent / f"{tmp_path.name}-outside"
    outside.mkdir()
    try:
        (tmp_path / "linked").symlink_to(outside, target_is_directory=True)
    except OSError:
        pytest.skip("directory symlinks are unavailable")
    _write_nested_architecture_project(
        tmp_path,
        prompts_dir="prompts/backend",
        architecture_filename="backend/credits_Python.prompt",
        architecture_filepath="linked/credits.py",
    )

    paths = get_pdd_file_paths(
        "credits",
        "python",
        prompts_dir="prompts/backend",
        context_override="backend",
    )

    assert paths["code"].resolve(strict=False) == (
        tmp_path / "backend" / "functions" / "credits.py"
    ).resolve(strict=False)


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

    def test_workflow_complete_with_both_skip_flags_needs_no_run_report(self, tmp_path, monkeypatch):
        """When tests and verify are skipped, file existence is enough."""
        monkeypatch.chdir(tmp_path)
        (tmp_path / ".pdd" / "meta").mkdir(parents=True)
        code_file = tmp_path / "test.py"
        example_file = tmp_path / "test_example.py"
        code_file.write_text("def add(a, b): return a + b")
        example_file.write_text("from test import add")

        paths = {
            'code': code_file,
            'example': example_file,
            'test': tmp_path / "test_test.py"
        }

        assert _is_workflow_complete(
            paths,
            skip_tests=True,
            skip_verify=True,
            basename="test",
            language="python",
        ) is True
    
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
    """A path-qualified basename keeps its subdirectory under the configured dir (#1677).

    For basename='core/cloud' with no architecture entry and .pddrc paths ending in /:
    - generate_output_path: pdd/ → code: pdd/core/cloud.py
    - test_output_path: tests/ → test: tests/core/test_cloud.py
    - example_output_path: examples/ → example: examples/core/cloud_example.py

    Issue #1677: the basename's directory (`core/`) is preserved so two modules sharing
    a leaf (`core/cloud`, `aws/cloud`) don't collapse onto one `pdd/cloud.py`. Any
    segment the configured directory already provides is de-duplicated (it is NOT
    re-prefixed to `pdd/pdd/...`). A context whose prompts_dir already maps the
    directory keeps using its generate_output_path directly (see
    test_explicit_output_paths).
    """
    _write_pddrc_here()

    # Create prompt file in subdirectory
    prompts_core_dir = Path("prompts") / "core"
    prompts_core_dir.mkdir(parents=True, exist_ok=True)
    (prompts_core_dir / "cloud_python.prompt").write_text("Write a cloud module")

    repo_root = Path(__file__).parent.parent
    monkeypatch.setenv("PDD_PATH", str(repo_root))

    paths = get_pdd_file_paths(basename="core/cloud", language="python", prompts_dir="prompts")

    # The basename's subdirectory (core/) is preserved under each configured dir.
    code_path = paths["code"].as_posix()
    test_path = paths["test"].as_posix()
    example_path = paths["example"].as_posix()

    assert code_path.endswith("pdd/core/cloud.py"), \
        f"Expected path ending with 'pdd/core/cloud.py', got {code_path}"
    assert test_path.endswith("tests/core/test_cloud.py"), \
        f"Expected path ending with 'tests/core/test_cloud.py', got {test_path}"
    assert example_path.endswith("examples/core/cloud_example.py"), \
        f"Expected path ending with 'examples/core/cloud_example.py', got {example_path}"


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


def test_get_pdd_file_paths_no_duplication_when_prompts_dir_is_absolute_with_subdirectory(tmp_path, monkeypatch):
    """
    Regression test: prompt path duplication when prompts_dir is an absolute path
    that already contains the context's subdirectory.

    Bug scenario (from downstream_project recruiting modules):
      - .pddrc context has prompts_dir: "prompts/recruiting"
      - sync_main discovers a prompt via template and passes the absolute parent as
        prompts_dir, e.g. "/abs/path/prompts/recruiting"
      - _resolve_prompts_root returns it unchanged (already absolute)
      - The prefix logic extracts "recruiting" from prompts_dir config and prepends
        it AGAIN, producing "/abs/path/prompts/recruiting/recruiting/mod_python.prompt"
      - The prompt file is then not found because the doubled path doesn't exist

    The bug is in the early prompt_path construction (before the construct_paths
    fallback). When the outputs config does NOT include a prompt template, the
    corrupted prompt_path is passed as fallback to _generate_paths_from_templates
    and used directly.

    Expected: The prompt path should be "/abs/path/prompts/recruiting/mod_python.prompt"
    (no duplicated "recruiting" directory segment).
    """
    monkeypatch.chdir(tmp_path)

    # Directory structure mimicking downstream_project recruiting
    prompts_recruiting = tmp_path / "prompts" / "recruiting"
    prompts_recruiting.mkdir(parents=True)

    # Create the prompt file at the correct location
    prompt_file = prompts_recruiting / "recruiting_nurture_models_python.prompt"
    prompt_file.write_text("Build nurture models")

    # .pddrc with prompts_dir: "prompts/recruiting" but NO prompt path in outputs.
    # This forces the fallback to use the initial prompt_path built by the prefix logic.
    (tmp_path / ".pddrc").write_text(
        'contexts:\n'
        '  recruiting_nurture_models:\n'
        '    paths: ["backend/functions/recruiting/nurture/**"]\n'
        '    defaults:\n'
        '      prompts_dir: "prompts/recruiting"\n'
        '      generate_output_path: "backend/functions/recruiting/nurture/"\n'
        '      outputs:\n'
        '        code:\n'
        '          path: "backend/functions/recruiting/nurture/recruiting_nurture_models.py"\n'
        '        test:\n'
        '          path: "backend/tests/recruiting/test_recruiting_nurture_models.py"\n'
    )

    # Call with ABSOLUTE prompts_dir (as sync_main does after template discovery)
    paths = get_pdd_file_paths(
        basename="recruiting_nurture_models",
        language="python",
        prompts_dir=str(prompts_recruiting),  # absolute, already includes "recruiting"
        context_override="recruiting_nurture_models",
    )

    prompt_path = paths.get("prompt")
    assert prompt_path is not None

    # Key assertion: the "recruiting" directory must NOT be duplicated in the path.
    # Note: "recruiting/recruiting_nurture_models..." is fine (dir/filename), but
    # "recruiting/recruiting/" (two consecutive directory segments) is the bug.
    path_str = str(prompt_path)
    assert "recruiting/recruiting/" not in path_str, \
        f"Path has duplicated 'recruiting' directory segment: {path_str}"

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

    # Create code/example/test files first so the fingerprint represents a
    # prompt-only change rather than a prompt+derived conflict.
    paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir="prompts")
    code_hash = create_file(paths['code'], "def add(a, b): return a + b")
    example_hash = create_file(paths['example'], "print(add(1, 2))")
    test_hash = create_file(paths['test'], "def test_add(): assert add(1, 2) == 3")

    # Create fingerprint with OLD prompt hash and command='crash'
    old_prompt_hash = "old_hash_that_differs_from_current"
    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0.0",
        "timestamp": "2025-01-01T00:00:00Z",
        "command": "crash",  # Previous command was crash
        "prompt_hash": old_prompt_hash,  # Different from current!
        "code_hash": code_hash,
        "example_hash": example_hash,
        "test_hash": test_hash
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

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE)

    # Should detect prompt change and regenerate, NOT continue to verify
    assert decision.operation in ('generate', 'auto-deps'), \
        f"Expected 'generate' or 'auto-deps' due to prompt change, got '{decision.operation}'"
    assert 'prompt' in decision.reason.lower(), \
        f"Reason should mention prompt change: {decision.reason}"


def test_prompt_change_progresses_generate_verify_test_then_complete(pdd_test_environment):
    """
    Regression guard for prompt-only changes: sync should regenerate first, then
    require verify, then require test before considering the workflow complete.
    """
    tmp_path = pdd_test_environment
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir(exist_ok=True)

    prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
    old_prompt_hash = create_file(prompt_path, "ORIGINAL PROMPT CONTENT")

    paths = get_pdd_file_paths(BASENAME, LANGUAGE, prompts_dir=str(prompts_dir))
    code_hash = create_file(paths['code'], "def add(a, b):\n    return a + b\n")
    example_hash = create_file(paths['example'], "print(add(1, 2))\n")
    test_hash = create_file(paths['test'], "def test_add():\n    assert add(1, 2) == 3\n")

    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"

    # Start from a fully completed workflow for the old prompt version.
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0.0",
        "timestamp": "2025-01-01T00:00:00Z",
        "command": "test",
        "prompt_hash": old_prompt_hash,
        "code_hash": code_hash,
        "example_hash": example_hash,
        "test_hash": test_hash
    })
    create_run_report_file(rr_path, {
        "timestamp": "2025-01-01T00:01:00Z",
        "exit_code": 0,
        "tests_passed": 5,
        "tests_failed": 0,
        "coverage": 95.0,
        "test_hash": test_hash
    })

    # User edits only the prompt. Sync should restart with generation.
    new_prompt_hash = create_file(prompt_path, "UPDATED PROMPT CONTENT")
    decision = sync_determine_operation(
        BASENAME, LANGUAGE, TARGET_COVERAGE,
        prompts_dir=str(prompts_dir)
    )
    assert decision.operation == 'generate', (
        f"Expected prompt-only change to restart at 'generate', got '{decision.operation}'"
    )

    # Simulate successful generate: hashes now match the new prompt, but verify has
    # not run for this generation yet.
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0.0",
        "timestamp": "2025-01-01T00:02:00Z",
        "command": "generate",
        "prompt_hash": new_prompt_hash,
        "code_hash": code_hash,
        "example_hash": example_hash,
        "test_hash": test_hash
    })
    decision = sync_determine_operation(
        BASENAME, LANGUAGE, TARGET_COVERAGE,
        prompts_dir=str(prompts_dir)
    )
    assert decision.operation == 'verify', (
        f"Expected post-generate sync to require 'verify', got '{decision.operation}'"
    )

    # Simulate successful verify: sync should still require tests before completion.
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0.0",
        "timestamp": "2025-01-01T00:03:00Z",
        "command": "verify",
        "prompt_hash": new_prompt_hash,
        "code_hash": code_hash,
        "example_hash": example_hash,
        "test_hash": test_hash
    })
    create_run_report_file(rr_path, {
        "timestamp": "2025-01-01T00:03:30Z",
        "exit_code": 0,
        "tests_passed": 5,
        "tests_failed": 0,
        "coverage": 95.0,
        "test_hash": test_hash
    })
    decision = sync_determine_operation(
        BASENAME, LANGUAGE, TARGET_COVERAGE,
        prompts_dir=str(prompts_dir)
    )
    assert decision.operation == 'test', (
        f"Expected post-verify sync to require 'test', got '{decision.operation}'"
    )

    # After tests complete successfully for the new prompt version, sync is done.
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0.0",
        "timestamp": "2025-01-01T00:04:00Z",
        "command": "test",
        "prompt_hash": new_prompt_hash,
        "code_hash": code_hash,
        "example_hash": example_hash,
        "test_hash": test_hash
    })
    create_run_report_file(rr_path, {
        "timestamp": "2025-01-01T00:04:30Z",
        "exit_code": 0,
        "tests_passed": 5,
        "tests_failed": 0,
        "coverage": 95.0,
        "test_hash": test_hash
    })
    decision = sync_determine_operation(
        BASENAME, LANGUAGE, TARGET_COVERAGE,
        prompts_dir=str(prompts_dir)
    )
    assert decision.operation == 'nothing', (
        f"Expected workflow to be complete after test succeeds, got '{decision.operation}'"
    )


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

    @pytest.mark.parametrize(
        "attributed_include",
        [
            '<include select="def:helper">utils.py</include>',
            '<include query="utility helpers">utils.py</include>',
            '<include select="def:helper" mode="interface">utils.py</include>',
        ],
        ids=["select-attr", "query-attr", "select-plus-mode"],
    )
    def test_extract_include_deps_finds_attributed_includes(
        self, pdd_test_environment, attributed_include
    ):
        """extract_include_deps must match attributed <include …> forms.

        ``auto_include`` emits ``<include select="…">`` and
        ``<include query="…">`` directives; if the extractor's regex only
        matched bare ``<include>`` the fingerprint would lose those deps
        and dependency changes would go undetected by sync.
        """
        prompts_dir = pdd_test_environment / "prompts"
        dep_file = pdd_test_environment / "utils.py"
        create_file(dep_file, "def helper(): pass\n")

        prompt_path = prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt"
        create_file(prompt_path, f"Build module.\n{attributed_include}\n")

        deps = extract_include_deps(prompt_path)
        assert len(deps) == 1, (
            f"Expected 1 dep for {attributed_include!r}, got {deps!r}"
        )
        assert any("utils.py" in k for k in deps), (
            f"Expected utils.py in deps keys, got {list(deps)}"
        )

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


# ---------------------------------------------------------------------------
# Bug: _generate_paths_from_templates missing 'code' fallback (#826)
# ---------------------------------------------------------------------------

class TestGeneratePathsFromTemplatesCodeFallback:
    """When .pddrc outputs config defines 'prompt' but not 'code', the returned
    dict must still have a 'code' key. Otherwise sync_orchestration crashes with
    KeyError: 'code'.

    Regression test for promptdriven/example_app#826: the frontend catch-all
    context has outputs.prompt but no outputs.code, causing page syncs to crash.
    """

    def test_code_key_always_present(self):
        """_generate_paths_from_templates must return a 'code' key even when
        outputs config only defines 'prompt'."""
        from pdd.sync_determine_operation import _generate_paths_from_templates

        outputs_config = {
            "prompt": {"path": "prompts/frontend/{dir_prefix}{name}_{language}.prompt"},
            # NOTE: no 'code' output defined — this is the bug trigger
        }
        result = _generate_paths_from_templates(
            basename="app/dashboard/page",
            language="typescriptreact",
            extension="tsx",
            outputs_config=outputs_config,
            prompt_path="prompts/frontend/app/dashboard/page_TypescriptReact.prompt",
        )

        assert "code" in result, (
            f"'code' key missing from result: {list(result.keys())}. "
            "sync_orchestration accesses pdd_files['code'] directly and will "
            "crash with KeyError if this key is absent."
        )
        assert "page" in str(result["code"]), (
            f"Code path should contain the module name 'page', got: {result['code']}"
        )

    def test_code_key_present_with_generate_output_path(self):
        """When generate_output_path is available, use it for the code fallback."""
        from pdd.sync_determine_operation import _generate_paths_from_templates

        outputs_config = {
            "prompt": {"path": "prompts/frontend/{dir_prefix}{name}_{language}.prompt"},
        }
        result = _generate_paths_from_templates(
            basename="app/dashboard/page",
            language="typescriptreact",
            extension="tsx",
            outputs_config=outputs_config,
            prompt_path="prompts/frontend/app/dashboard/page_TypescriptReact.prompt",
        )

        assert "code" in result
        # Should use dir_prefix + name pattern
        code_str = str(result["code"])
        assert "page.tsx" in code_str, f"Expected page.tsx in code path, got: {code_str}"


# =============================================================================
# Issue #1048: Glob patterns must escape brackets in basenames
# =============================================================================


class TestIssue1048GlobEscapingInDetermineOperation:
    """Tests that glob patterns in sync_determine_operation correctly handle
    bracket characters in basenames by using glob.escape()."""

    def test_check_example_success_history_with_bracket_basename(self, tmp_path):
        """_check_example_success_history glob pattern must escape brackets in _safe_basename output.

        Bug: _safe_basename('frontend/[id]') -> 'frontend_[id]', then
        meta_dir.glob('frontend_[id]_python_run*.json') interprets [id] as char class.
        """
        from sync_determine_operation import _check_example_success_history, _safe_basename

        assert _safe_basename("frontend/[id]") == "frontend_[id]"

        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True, exist_ok=True)

        report_file = meta_dir / "frontend_[id]_python_run_001.json"
        report_file.write_text('{"exit_code": 0}')

        with patch("sync_determine_operation.get_meta_dir", return_value=meta_dir), \
             patch("sync_determine_operation.read_fingerprint", return_value=None), \
             patch("sync_determine_operation.read_run_report", return_value=None):

            result = _check_example_success_history("frontend/[id]", "python")

        assert result is True, \
            "Bug #1048: _check_example_success_history can't find run report because " \
            "glob interprets [id] as character class matching 'i' or 'd'"

    def test_get_pdd_file_paths_primary_test_glob_with_brackets(self, tmp_path, monkeypatch):
        """get_pdd_file_paths primary path: test glob must escape brackets in name_part.

        Bug: _extract_name_part('[id]') returns ('', '[id]'), then
        test_dir.glob('test_[id]*.py') interprets [id] as char class.
        The fallback returns [test_path] (1 file) masking the glob failure.
        We create 2 test files so only proper glob finds both.
        """
        monkeypatch.chdir(tmp_path)

        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "[id]_python.prompt").write_text("# prompt")

        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        # Create TWO matching test files — fallback only returns 1
        test_file_1 = tests_dir / "test_[id].py"
        test_file_1.write_text("def test_1(): pass")
        test_file_2 = tests_dir / "test_[id]_extra.py"
        test_file_2.write_text("def test_2(): pass")

        with patch("sync_determine_operation.construct_paths") as mock_cp:
            def side_effect(*args, **kwargs):
                cmd = kwargs.get("command", "sync")
                if cmd == "test":
                    return (
                        {"prompts_dir": str(prompts_dir), "tests_dir": str(tests_dir)},
                        {"prompt_file": "content"},
                        {"output": str(tests_dir / "test_[id].py")},
                        "python",
                    )
                return (
                    {"prompts_dir": str(prompts_dir), "tests_dir": str(tests_dir)},
                    {"prompt_file": "content"},
                    {
                        "output": str(tmp_path / "src" / "[id].py"),
                        "generate_output_path": str(tmp_path / "src" / "[id].py"),
                        "test_output_path": str(tests_dir / "test_[id].py"),
                        "example_output_path": str(tmp_path / "examples" / "[id]_example.py"),
                    },
                    "python",
                )
            mock_cp.side_effect = side_effect

            result = get_pdd_file_paths("[id]", "python", prompts_dir=str(prompts_dir))

        test_files = result.get("test_files", [])
        test_file_names = [Path(f).name for f in test_files]

        # Both test files should be found by glob. The fallback only returns 1.
        assert "test_[id].py" in test_file_names, \
            f"Bug #1048: glob missed test_[id].py. Found: {test_file_names}"
        assert "test_[id]_extra.py" in test_file_names, \
            f"Bug #1048: glob missed test_[id]_extra.py because [id] was treated as char class " \
            f"(fallback masked the bug by returning only test_path). Found: {test_file_names}"

    def test_get_pdd_file_paths_fallback_glob_with_brackets(self, tmp_path, monkeypatch):
        """get_pdd_file_paths exception fallback: test glob must also escape brackets.

        With construct_paths raising, the fallback globs in CWD.
        We create 2 test files to detect the glob failure (fallback returns only 1).
        """
        monkeypatch.chdir(tmp_path)

        # Create TWO test files in CWD
        test_file_1 = tmp_path / "test_[id].py"
        test_file_1.write_text("def test_1(): pass")
        test_file_2 = tmp_path / "test_[id]_extra.py"
        test_file_2.write_text("def test_2(): pass")

        with patch("sync_determine_operation.construct_paths", side_effect=Exception("force fallback")):
            result = get_pdd_file_paths("[id]", "python", prompts_dir=str(tmp_path))

        test_files = result.get("test_files", [])
        test_file_names = [Path(f).name for f in test_files]

        assert "test_[id]_extra.py" in test_file_names, \
            f"Bug #1048: fallback glob missed test_[id]_extra.py because [id] was treated as char class. Found: {test_file_names}"

    def test_get_pdd_file_paths_prompt_missing_glob_with_brackets(self, tmp_path, monkeypatch):
        """get_pdd_file_paths prompt-missing fallback: test glob must escape brackets.

        When prompt doesn't exist on disk, the function still tries to find test files.
        We create 2 test files to detect the glob failure.
        """
        monkeypatch.chdir(tmp_path)

        # NO prompt file exists — triggers the prompt-missing path
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        test_file_1 = tests_dir / "test_[id].py"
        test_file_1.write_text("def test_1(): pass")
        test_file_2 = tests_dir / "test_[id]_extra.py"
        test_file_2.write_text("def test_2(): pass")

        with patch("sync_determine_operation.construct_paths") as mock_cp:
            mock_cp.return_value = (
                {"prompts_dir": str(tmp_path / "prompts"), "tests_dir": str(tests_dir)},
                {"prompt_file": "content"},
                {
                    "generate_output_path": str(tmp_path / "src" / "[id].py"),
                    "test_output_path": str(tests_dir / "test_[id].py"),
                    "example_output_path": str(tmp_path / "examples" / "[id]_example.py"),
                },
                "python",
            )

            result = get_pdd_file_paths("[id]", "python", prompts_dir=str(tmp_path / "prompts"))

        test_files = result.get("test_files", [])
        test_file_names = [Path(f).name for f in test_files]

        assert "test_[id]_extra.py" in test_file_names, \
            f"Bug #1048: prompt-missing glob missed test_[id]_extra.py. Found: {test_file_names}"


# ============================================================================
# Issue #1169: get_pdd_file_paths fails for nested subdirectories + case mismatch
# ============================================================================

from pdd.sync_determine_operation import (
    _case_insensitive_path_lookup,
    _resolve_prompt_path_from_architecture,
)


def test_case_insensitive_path_lookup_returns_on_disk_casing_when_alias_exists(tmp_path, monkeypatch):
    """Case-insensitive filesystems must not preserve the caller's wrong casing."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    actual_prompt = prompts_dir / "api_pipeline_compositions_route_TypeScript.prompt"
    actual_prompt.write_text("Generate API route")
    lower_candidate = prompts_dir / "api_pipeline_compositions_route_typescript.prompt"

    original_exists = Path.exists

    def fake_exists(path):
        if path == lower_candidate:
            return True
        return original_exists(path)

    monkeypatch.setattr(Path, "exists", fake_exists)

    assert _case_insensitive_path_lookup(lower_candidate) == actual_prompt


def test_get_pdd_file_paths_preserves_existing_mixed_case_prompt_suffix(tmp_path, monkeypatch):
    """CI drift path should return the Git-tracked mixed-case prompt path."""
    monkeypatch.chdir(tmp_path)

    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    actual_prompt = prompts_dir / "api_pipeline_compositions_route_TypeScript.prompt"
    actual_prompt.write_text("Generate API route")
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)

    paths = get_pdd_file_paths(
        "api_pipeline_compositions_route", "typescript", "prompts"
    )

    assert paths["prompt"] == actual_prompt.relative_to(tmp_path)


def test_get_pdd_file_paths_nested_subdir_case_mismatch(tmp_path, monkeypatch):
    """Bug #1169: get_pdd_file_paths must find prompts in nested subdirs with case mismatch.

    Production scenario: prompt at prompts/src/clients/firestore_client_Python.prompt
    but get_pdd_file_paths("firestore_client", "python", "prompts") constructs
    prompts/firestore_client_python.prompt (wrong case, wrong dir).
    """
    monkeypatch.chdir(tmp_path)

    # Create nested directory structure matching the issue's reproduction
    nested_dir = tmp_path / "prompts" / "src" / "clients"
    nested_dir.mkdir(parents=True)
    actual_prompt = nested_dir / "firestore_client_Python.prompt"
    actual_prompt.write_text("Generate Firestore client")

    # Create minimal .pdd structure
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)

    paths = get_pdd_file_paths("firestore_client", "python", "prompts")

    # BUG: Current code constructs prompts/firestore_client_python.prompt (wrong case + wrong dir)
    # After fix, should resolve to the actual file in the nested subdirectory
    assert paths['prompt'].exists(), (
        f"Bug #1169: prompt not found. Got path: {paths['prompt']}. "
        f"Expected to find: {actual_prompt}"
    )


def test_get_pdd_file_paths_architecture_json_nested_subdir(tmp_path, monkeypatch):
    """Bug #1169: architecture.json lookup must resolve prompts in nested subdirs.

    When architecture.json has filename: "firestore_client_Python.prompt",
    _resolve_prompt_path_from_architecture naively joins to prompts_root (flat),
    missing the actual file in prompts/src/clients/.
    """
    monkeypatch.chdir(tmp_path)

    # Create nested prompt file
    nested_dir = tmp_path / "prompts" / "src" / "clients"
    nested_dir.mkdir(parents=True)
    actual_prompt = nested_dir / "firestore_client_Python.prompt"
    actual_prompt.write_text("Generate Firestore client")

    # Create code file
    code_dir = tmp_path / "src" / "clients"
    code_dir.mkdir(parents=True)
    (code_dir / "firestore_client.py").write_text("# client code")

    # Create architecture.json with filename (not full path)
    arch = {
        "modules": [{
            "filename": "firestore_client_Python.prompt",
            "filepath": "src/clients/firestore_client.py"
        }]
    }
    (tmp_path / "architecture.json").write_text(json.dumps(arch))

    # Create minimal .pdd structure
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)

    paths = get_pdd_file_paths("firestore_client", "python", "prompts")

    # BUG: _resolve_prompt_path_from_architecture joins prompts_root + filename → flat path
    # Then _case_insensitive_prompt_lookup searches only prompts/, not prompts/src/clients/
    assert paths['prompt'].exists(), (
        f"Bug #1169: prompt not found via architecture.json path. Got: {paths['prompt']}. "
        f"Expected to resolve to: {actual_prompt}"
    )
    # Verify code path resolves correctly from architecture.json
    assert "firestore_client.py" in str(paths['code'])


def test_get_pdd_file_paths_nested_subdir_logging_shows_exists_true(tmp_path, monkeypatch, caplog):
    """Bug #1169: Logging must show exists=True when prompt is in nested subdir.

    Production logs showed 'exists=False' for every sync attempt on nested prompts.
    After fix, the log should show exists=True.
    """
    import logging
    monkeypatch.chdir(tmp_path)

    # Create nested prompt file
    nested_dir = tmp_path / "prompts" / "src" / "clients"
    nested_dir.mkdir(parents=True)
    actual_prompt = nested_dir / "firestore_client_Python.prompt"
    actual_prompt.write_text("Generate Firestore client")

    # Create minimal .pdd structure
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)

    with caplog.at_level(logging.INFO, logger="pdd.sync_determine_operation"):
        paths = get_pdd_file_paths("firestore_client", "python", "prompts")

    # BUG: Current code logs "exists=False" because it looks in prompts/ not prompts/src/clients/
    exists_log_entries = [r for r in caplog.records if "exists=" in r.message]
    assert any("exists=True" in r.message for r in exists_log_entries), (
        f"Bug #1169: Expected 'exists=True' in logs but got: "
        f"{[r.message for r in exists_log_entries]}"
    )


def test_resolve_prompt_path_from_architecture_flat_filename_misses_subdirectory(tmp_path):
    """Bug #1169: _resolve_prompt_path_from_architecture produces wrong path for flat filenames.

    When architecture.json has filename: "firestore_client_Python.prompt" (no subdirectory),
    _resolve_prompt_path_from_architecture joins it to prompts_root producing
    prompts/firestore_client_Python.prompt. But the file is actually at
    prompts/src/clients/firestore_client_Python.prompt.

    The resolved path must exist when the file is in a nested subdirectory.
    This tests that the architecture.json lookup + path resolution chain
    produces a path that actually resolves to the file on disk.
    """
    prompts_root = tmp_path / "prompts"
    nested_dir = prompts_root / "src" / "clients"
    nested_dir.mkdir(parents=True)
    actual_file = nested_dir / "firestore_client_Python.prompt"
    actual_file.write_text("prompt content")

    # This is what happens in the buggy code: architecture.json returns just the filename
    resolved = _resolve_prompt_path_from_architecture(
        prompts_root, "firestore_client_Python.prompt"
    )

    # BUG: resolved is prompts/firestore_client_Python.prompt which doesn't exist
    # The file is at prompts/src/clients/firestore_client_Python.prompt
    # After fix, either _resolve_prompt_path_from_architecture or its caller
    # must search subdirectories to find the actual file
    # Post-#1169: _resolve_prompt_path_from_architecture itself performs the
    # recursive case-insensitive search when the naive join misses. The
    # returned path must point at the real file on disk.
    assert resolved.exists(), (
        f"Bug #1169: architecture.json flat filename must resolve to the nested file. "
        f"Resolved: {resolved}. Actual file: {actual_file}"
    )
    assert resolved == actual_file, (
        f"Bug #1169: expected resolved path to equal {actual_file}, got {resolved}"
    )


def test_get_pdd_file_paths_deep_nesting_different_language(tmp_path, monkeypatch):
    """Bug #1169: Nested subdirectory resolution must work for all languages.

    Tests deeper nesting with TypeScript to ensure the fix isn't Python-specific.
    """
    monkeypatch.chdir(tmp_path)

    # Create deeply nested prompt file with TypeScript language
    deep_dir = tmp_path / "prompts" / "api" / "v2" / "handlers"
    deep_dir.mkdir(parents=True)
    actual_prompt = deep_dir / "user_handler_TypeScript.prompt"
    actual_prompt.write_text("Generate user handler")

    # Create minimal .pdd structure
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)

    paths = get_pdd_file_paths("user_handler", "typescript", "prompts")

    # BUG: Constructs prompts/user_handler_typescript.prompt (wrong case + wrong dir)
    assert paths['prompt'].exists(), (
        f"Bug #1169: prompt not found for TypeScript in deep nesting. Got: {paths['prompt']}. "
        f"Expected to find: {actual_prompt}"
    )


def _write_frontend_page_test_config(tmp_path: Path) -> None:
    """Create the minimal repo config needed for nested frontend page path resolution."""
    config = {
        "contexts": {
            "frontend": {
                "paths": ["frontend/**", "prompts/frontend/**"],
                "defaults": {
                    "prompts_dir": "prompts/frontend",
                    "generate_output_path": "frontend/src",
                    "default_language": "typescriptreact",
                    "strength": 0.818,
                    "outputs": {
                        "prompt": {
                            "path": "prompts/frontend/{dir_prefix}{name}_{language}.prompt"
                        }
                    },
                },
            },
            "default": {"defaults": {}},
        }
    }
    (tmp_path / ".pddrc").write_text(json.dumps(config))
    (tmp_path / ".pdd" / "meta").mkdir(parents=True)
    (tmp_path / ".pdd" / "locks").mkdir(parents=True)


def test_get_pdd_file_paths_nested_frontend_page_prefers_nested_prompt(tmp_path, monkeypatch):
    """Nested frontend page basenames must not collapse to the flat `page` prompt."""
    monkeypatch.chdir(tmp_path)
    _write_frontend_page_test_config(tmp_path)

    flat_prompt = tmp_path / "prompts" / "frontend" / "page_TypescriptReact.prompt"
    flat_prompt.parent.mkdir(parents=True)
    flat_prompt.write_text("flat page prompt")

    nested_prompt = tmp_path / "prompts" / "frontend" / "app" / "settings" / "account" / "page_TypescriptReact.prompt"
    nested_prompt.parent.mkdir(parents=True)
    nested_prompt.write_text("account page prompt")

    paths = get_pdd_file_paths("frontend/app/settings/account/page", "typescriptreact", "prompts")

    assert paths["prompt"].is_file()
    assert paths["prompt"].samefile(nested_prompt)
    assert paths["code"].resolve() == (tmp_path / "frontend" / "src" / "app" / "settings" / "account" / "page.tsx").resolve()


def test_get_pdd_file_paths_nested_frontend_page_uses_context_relative_architecture_entry(tmp_path, monkeypatch):
    """Relative architecture filenames like app/settings/security/page_* must resolve correctly."""
    monkeypatch.chdir(tmp_path)
    _write_frontend_page_test_config(tmp_path)

    flat_prompt = tmp_path / "prompts" / "frontend" / "page_TypescriptReact.prompt"
    flat_prompt.parent.mkdir(parents=True)
    flat_prompt.write_text("flat page prompt")

    security_prompt = tmp_path / "prompts" / "frontend" / "app" / "settings" / "security" / "page_TypescriptReact.prompt"
    security_prompt.parent.mkdir(parents=True)
    security_prompt.write_text("security page prompt")

    (tmp_path / "architecture.json").write_text(json.dumps([
        {
            "filename": "app/settings/security/page_TypescriptReact.prompt",
            "filepath": "frontend/src/app/settings/security/page.tsx",
        },
        {
            "filename": "page_TypescriptReact.prompt",
            "filepath": "frontend/src/app/settings/github/page.tsx",
        },
    ]))

    paths = get_pdd_file_paths("frontend/app/settings/security/page", "typescriptreact", "prompts")

    assert paths["prompt"].is_file()
    assert paths["prompt"].samefile(security_prompt)
    assert paths["code"].resolve() == (tmp_path / "frontend" / "src" / "app" / "settings" / "security" / "page.tsx").resolve()


def test_get_pdd_file_paths_nested_frontend_page_rejects_wrong_flat_architecture_match(tmp_path, monkeypatch):
    """Flat architecture entries must not steal other nested page basenames with the same filename."""
    monkeypatch.chdir(tmp_path)
    _write_frontend_page_test_config(tmp_path)

    flat_prompt = tmp_path / "prompts" / "frontend" / "page_TypescriptReact.prompt"
    flat_prompt.parent.mkdir(parents=True)
    flat_prompt.write_text("flat page prompt")

    account_prompt = tmp_path / "prompts" / "frontend" / "app" / "settings" / "account" / "page_TypescriptReact.prompt"
    account_prompt.parent.mkdir(parents=True)
    account_prompt.write_text("account page prompt")

    github_prompt = tmp_path / "prompts" / "frontend" / "app" / "settings" / "github" / "page_TypescriptReact.prompt"
    github_prompt.parent.mkdir(parents=True)
    github_prompt.write_text("github page prompt")

    (tmp_path / "architecture.json").write_text(json.dumps([
        {
            "filename": "page_TypescriptReact.prompt",
            "filepath": "frontend/src/app/settings/github/page.tsx",
        },
    ]))

    github_paths = get_pdd_file_paths("frontend/app/settings/github/page", "typescriptreact", "prompts")
    assert github_paths["prompt"].is_file()
    assert github_paths["prompt"].samefile(github_prompt)
    assert github_paths["code"].resolve() == (tmp_path / "frontend" / "src" / "app" / "settings" / "github" / "page.tsx").resolve()

    account_paths = get_pdd_file_paths("frontend/app/settings/account/page", "typescriptreact", "prompts")
    assert account_paths["prompt"].is_file()
    assert account_paths["prompt"].samefile(account_prompt)
    assert account_paths["code"].resolve() == (tmp_path / "frontend" / "src" / "app" / "settings" / "account" / "page.tsx").resolve()


# --- Issue #1256: Dict-format architecture tolerance ---
# Scope addition: covers expansion item "pdd/sync_determine_operation.py:340-342
# has partial tolerance but should use centralized extract_modules() for consistency"
# identified by Step 6 but absent from Step 8's plan


def test_get_filepath_dict_format_without_modules_key_returns_tuple(tmp_path):
    """_get_filepath_from_architecture returns (None, None) for dict without 'modules' key (Test 18).

    Bug: at sync_determine_operation.py:340, arch.get("modules", arch) falls back to
    the dict itself when there is no "modules" key. Then isinstance(modules, list)
    is False and line 343 returns bare None instead of the expected (None, None) tuple.
    Callers that unpack `filepath, filename = _get_filepath_from_architecture(...)` crash
    with TypeError.
    """
    from pdd.sync_determine_operation import _get_filepath_from_architecture

    arch_path = tmp_path / "architecture.json"
    # Dict without "modules" key — triggers the fallback bug
    arch_path.write_text(json.dumps({"prd_files": ["prd.md"]}), encoding="utf-8")

    result = _get_filepath_from_architecture(arch_path, "auth_Python.prompt")
    assert result == (None, None), (
        f"Expected (None, None) for dict without 'modules' key, got {result!r}. "
        "Line 343 returns bare None instead of the expected (None, None) tuple."
    )


# ---------------------------------------------------------------------------
# Issue #1201: generate_output_path from .pddrc not honored in arch branch
# ---------------------------------------------------------------------------
# The architecture.json branch of get_pdd_file_paths() at line 942 sets
#   code_path = project_root / arch_filepath
# with no consultation of .pddrc's generate_output_path.  Meanwhile,
# lines 961-962 correctly read test_dir and example_dir from .pddrc defaults.
# All four tests below FAIL on the current (buggy) code and must PASS after
# the fix that reads generate_output_path from .pddrc in the same block.
# ---------------------------------------------------------------------------

class TestIssue1201GenerateOutputPathInArchBranch:
    """Issue #1201: generate_output_path is silently ignored when architecture.json
    provides a filepath, unlike example_output_path and test_output_path which are
    correctly applied from .pddrc defaults.
    """

    def _write_pddrc(self, tmp_path: Path, generate_dir: str = "src/",
                     test_dir: str = "tests/", example_dir: str = "examples/") -> None:
        (tmp_path / ".pddrc").write_text(
            f"contexts:\n"
            f"  default:\n"
            f"    paths: [\"**\"]\n"
            f"    defaults:\n"
            f"      generate_output_path: \"{generate_dir}\"\n"
            f"      test_output_path: \"{test_dir}\"\n"
            f"      example_output_path: \"{example_dir}\"\n"
        )

    def _write_arch_json(self, tmp_path: Path, prompt_filename: str, filepath: str) -> None:
        (tmp_path / "architecture.json").write_text(json.dumps({
            "modules": [{"filename": prompt_filename, "filepath": filepath}]
        }))

    def _setup_dirs(self, tmp_path: Path) -> None:
        for d in ("prompts", ".pdd/meta", ".pdd/locks"):
            (tmp_path / d).mkdir(parents=True, exist_ok=True)

    def test_generate_output_path_honored_when_arch_filepath_is_bare(self, tmp_path, monkeypatch):
        """code_path must land in .pddrc generate_output_path when arch.json filepath has no
        directory component (i.e., is a bare filename at the project root).

        Bug: code_path = project_root / arch_filepath uses root unconditionally.
        Fix: read generate_output_path from .pddrc defaults and apply it to code_path,
             exactly as example_dir/test_dir are already applied.
        """
        monkeypatch.chdir(tmp_path)
        self._setup_dirs(tmp_path)
        self._write_pddrc(tmp_path, generate_dir="src/")
        self._write_arch_json(tmp_path, "widget_python.prompt", "widget.py")

        paths = get_pdd_file_paths("widget", "python", "prompts")

        assert "src" in paths["code"].parts, (
            f"generate_output_path 'src/' from .pddrc must be applied to code path in the "
            f"architecture.json branch, but got: {paths['code']!r} (parent: {paths['code'].parent!r})"
        )

    def test_all_three_output_paths_applied_symmetrically_in_arch_branch(self, tmp_path, monkeypatch):
        """generate_output_path, test_output_path, and example_output_path must all be
        honored uniformly in the architecture.json branch — not just the latter two.

        Currently example_dir and test_dir are read from .pddrc (correct), but
        generate_output_path is absent from the same block, causing asymmetry.
        """
        monkeypatch.chdir(tmp_path)
        self._setup_dirs(tmp_path)
        self._write_pddrc(tmp_path, generate_dir="src/", test_dir="tests/", example_dir="examples/")
        self._write_arch_json(tmp_path, "widget_python.prompt", "widget.py")

        paths = get_pdd_file_paths("widget", "python", "prompts")

        # test and example are already correct (they should stay correct after fix)
        assert "examples" in paths["example"].parts, (
            f"example_output_path not honored: {paths['example']!r}"
        )
        assert "tests" in paths["test"].parts, (
            f"test_output_path not honored: {paths['test']!r}"
        )
        # code must also use its configured directory — currently broken
        assert "src" in paths["code"].parts, (
            f"generate_output_path 'src/' is not applied symmetrically with "
            f"test_output_path and example_output_path. "
            f"code={paths['code']!r}, test={paths['test']!r}, example={paths['example']!r}"
        )

    def test_code_filename_from_arch_json_preserved_after_generate_path_applied(
        self, tmp_path, monkeypatch
    ):
        """After the fix, the filename component from architecture.json must be preserved;
        only the parent directory should be overridden by .pddrc generate_output_path.

        This verifies the correct resolution: src/widget.py — not src/widget_widget.py.
        """
        monkeypatch.chdir(tmp_path)
        self._setup_dirs(tmp_path)
        self._write_pddrc(tmp_path, generate_dir="src/")
        self._write_arch_json(tmp_path, "widget_python.prompt", "widget.py")

        paths = get_pdd_file_paths("widget", "python", "prompts")

        # Filename must come from arch.json
        assert paths["code"].name == "widget.py", (
            f"Filename should be preserved from arch.json as 'widget.py', got: {paths['code'].name!r}"
        )
        # Parent directory must come from .pddrc generate_output_path
        assert paths["code"].parent.name == "src", (
            f"Parent directory should be 'src' from generate_output_path, "
            f"got: {paths['code'].parent.name!r} (full path: {paths['code']!r})"
        )

    def test_generate_output_path_honored_with_explicit_context_override(
        self, tmp_path, monkeypatch
    ):
        """generate_output_path is honored in the arch branch even when context_override is given.

        Steps 2-3 confirmed the bug in the pddrc_path branch that reads context_name from
        context_override (line 952).  This test ensures the fix works end-to-end when the
        caller supplies an explicit context.
        """
        monkeypatch.chdir(tmp_path)
        self._setup_dirs(tmp_path)
        (tmp_path / ".pddrc").write_text(
            "contexts:\n"
            "  default:\n"
            "    paths: [\"**\"]\n"
            "    defaults:\n"
            "      generate_output_path: \"lib/\"\n"
            "      test_output_path: \"tests/\"\n"
            "      example_output_path: \"examples/\"\n"
            "  backend:\n"
            "    paths: [\"backend/**\"]\n"
            "    defaults:\n"
            "      generate_output_path: \"backend/src/\"\n"
            "      test_output_path: \"backend/tests/\"\n"
            "      example_output_path: \"backend/examples/\"\n"
        )
        self._write_arch_json(tmp_path, "service_python.prompt", "service.py")

        paths = get_pdd_file_paths("service", "python", "prompts", context_override="backend")

        # With context_override="backend", generate_output_path should be "backend/src/"
        code_parts = paths["code"].parts
        assert "backend" in code_parts and "src" in code_parts, (
            f"With context_override='backend', code_path should be in backend/src/, "
            f"but got: {paths['code']!r}"
        )
from datetime import datetime, timezone
from pathlib import Path

from pdd.sync_determine_operation import _handle_missing_expected_files


def test_missing_example_schedules_example_by_default(tmp_path: Path) -> None:
    from pdd.sync_determine_operation import Fingerprint
    prompt = tmp_path / "prompts" / "calc_python.prompt"
    code = tmp_path / "pdd" / "calc.py"
    example = tmp_path / "context" / "calc_example.py"
    test = tmp_path / "tests" / "test_calc.py"
    prompt.parent.mkdir()
    code.parent.mkdir()
    example.parent.mkdir()
    test.parent.mkdir()
    prompt.write_text("Create calc.\n", encoding="utf-8")
    code.write_text("def add(a, b): return a + b\n", encoding="utf-8")
    fingerprint = Fingerprint("test", datetime.now(timezone.utc).isoformat(), "fix", "p", "c", "e", "t")

    decision = _handle_missing_expected_files(
        ["example"],
        {"prompt": prompt, "code": code, "example": example, "test": test},
        fingerprint,
        "calc",
        "python",
        str(prompt.parent),
    )

    assert decision.operation == "example"


def test_missing_example_is_bypassed_for_isolated_repair_or_replay(tmp_path: Path) -> None:
    from pdd.sync_determine_operation import Fingerprint

    prompt = tmp_path / "prompts" / "calc_python.prompt"
    code = tmp_path / "pdd" / "calc.py"
    example = tmp_path / "context" / "calc_example.py"
    test = tmp_path / "tests" / "test_calc.py"
    prompt.parent.mkdir()
    code.parent.mkdir()
    example.parent.mkdir()
    test.parent.mkdir()
    prompt.write_text("Create calc.\n", encoding="utf-8")
    code.write_text("def add(a, b): return a + b\n", encoding="utf-8")
    fingerprint = Fingerprint("test", datetime.now(timezone.utc).isoformat(), "fix", "p", "c", "e", "t")

    decision = _handle_missing_expected_files(
        ["example"],
        {"prompt": prompt, "code": code, "example": example, "test": test},
        fingerprint,
        "calc",
        "python",
        str(prompt.parent),
        isolated_replay_or_repair=True,
    )

    assert decision.operation == "generate"
    assert decision.details["isolated_replay_or_repair"] is True


# ---------------------------------------------------------------------------
# Issue #551 (reopened): YAML and Markdown example/test paths use raw language
# name instead of canonical file extension.
#
# Root cause: local get_extension() in sync_determine_operation fell back to
# language.lower() for languages not in its hard-coded map, returning "yaml"
# instead of "yml" and "markdown" instead of "md".
#
# Fix: local get_extension() now reads the first matching row from the
# package-local language_format.csv, which maps YAML -> .yml and Markdown -> .md.
# ---------------------------------------------------------------------------

class TestIssue551CanonicalExtensionInGetPddFilePaths:
    """Regression tests for issue #551 (reopened): YAML and Markdown example/test
    paths must use canonical file extensions, not raw language names.
    """

    def _write_arch_json(self, tmp_path: Path, prompt_filename: str, filepath: str) -> None:
        (tmp_path / "architecture.json").write_text(json.dumps({
            "modules": [{"filename": prompt_filename, "filepath": filepath}]
        }))

    def _setup_dirs(self, tmp_path: Path) -> None:
        for d in ("prompts", "examples", "tests", ".pdd/meta", ".pdd/locks"):
            (tmp_path / d).mkdir(parents=True, exist_ok=True)

    @pytest.mark.parametrize("language,code_filename,expected_example_suffix,expected_test_suffix", [
        ("YAML",     "ci.yml",          ".yml",  ".yml"),
        ("Markdown", "manifest.md",     ".md",   ".md"),
        ("Text",     "dockerfile.txt",  ".txt",  ".txt"),
    ])
    def test_architecture_paths_use_canonical_extensions(
        self,
        tmp_path,
        monkeypatch,
        language,
        code_filename,
        expected_example_suffix,
        expected_test_suffix,
    ):
        """get_pdd_file_paths must derive example/test extensions from the canonical
        language mapping, not the raw language string.

        Before the fix:
          YAML     -> ci_example.yaml / test_ci.yaml   (wrong, should be .yml)
          Markdown -> manifest_example.markdown         (wrong, should be .md)
          Text     -> dockerfile_example.text           (wrong, should be .txt)
        """
        monkeypatch.chdir(tmp_path)
        self._setup_dirs(tmp_path)

        basename = Path(code_filename).stem
        prompt_filename = f"{basename}_{language}.prompt"
        (tmp_path / "prompts" / prompt_filename).write_text(f"% {language} module\n")
        self._write_arch_json(tmp_path, prompt_filename, code_filename)

        paths = get_pdd_file_paths(basename, language, "prompts")

        assert paths["example"].suffix == expected_example_suffix, (
            f"Issue #551: example path for {language} must end with {expected_example_suffix!r}, "
            f"got {paths['example'].suffix!r} (full path: {paths['example']})"
        )
        assert paths["test"].suffix == expected_test_suffix, (
            f"Issue #551: test path for {language} must end with {expected_test_suffix!r}, "
            f"got {paths['test'].suffix!r} (full path: {paths['test']})"
        )

    def test_yaml_example_path_is_yml_not_yaml(self, tmp_path, monkeypatch):
        """Explicit regression for the reported YAML case: ci.yml must produce
        ci_example.yml (not ci_example.yaml) and test_ci.yml (not test_ci.yaml).
        """
        monkeypatch.chdir(tmp_path)
        self._setup_dirs(tmp_path)
        (tmp_path / "prompts" / "ci_YAML.prompt").write_text("% CI pipeline\n")
        self._write_arch_json(tmp_path, "ci_YAML.prompt", "ci.yml")

        paths = get_pdd_file_paths("ci", "YAML", "prompts")

        assert paths["example"].name == "ci_example.yml", (
            f"Issue #551: YAML example must be ci_example.yml, got {paths['example'].name!r}"
        )
        assert paths["test"].name == "test_ci.yml", (
            f"Issue #551: YAML test must be test_ci.yml, got {paths['test'].name!r}"
        )

    def test_markdown_example_path_is_md_not_markdown(self, tmp_path, monkeypatch):
        """Explicit regression for the reported Markdown case: manifest.md must
        produce manifest_example.md (not manifest_example.markdown).
        """
        monkeypatch.chdir(tmp_path)
        self._setup_dirs(tmp_path)
        (tmp_path / "prompts" / "manifest_Markdown.prompt").write_text("% Manifest docs\n")
        self._write_arch_json(tmp_path, "manifest_Markdown.prompt", "manifest.md")

        paths = get_pdd_file_paths("manifest", "Markdown", "prompts")

        assert paths["example"].name == "manifest_example.md", (
            f"Issue #551: Markdown example must be manifest_example.md, "
            f"got {paths['example'].name!r}"
        )
        assert paths["test"].name == "test_manifest.md", (
            f"Issue #551: Markdown test must be test_manifest.md, "
            f"got {paths['test'].name!r}"
        )

    # ------------------------------------------------------------------
    # Comprehensive sibling-language parametrized regression tests
    # These cover languages from the Step 6 NEEDS_FIX list where the old
    # local helper returned raw language names instead of canonical exts.
    # ------------------------------------------------------------------

    @pytest.mark.parametrize("language,code_filename,expected_example_suffix,expected_test_suffix", [
        # C-family / systems
        ("C++",             "engine.cpp",   ".cpp",    ".cpp"),
        ("C#",              "service.cs",   ".cs",     ".cs"),
        ("Haskell",         "parser.hs",    ".hs",     ".hs"),
        ("F#",              "module.fs",    ".fs",     ".fs"),
        ("R",               "stats.R",      ".R",      ".R"),
        ("LaTeX",           "paper.tex",    ".tex",    ".tex"),
        ("Assembly",        "boot.asm",     ".asm",    ".asm"),
        ("Fortran",         "solver.f90",   ".f90",    ".f90"),
        ("COBOL",           "report.cob",   ".cob",    ".cob"),
        ("Prolog",          "facts.pl",     ".pl",     ".pl"),
        ("Erlang",          "node.erl",     ".erl",    ".erl"),
        ("Clojure",         "core.clj",     ".clj",    ".clj"),
        ("Julia",           "compute.jl",   ".jl",     ".jl"),
        ("Elixir",          "worker.ex",    ".ex",     ".ex"),
        ("Pascal",          "program.pas",  ".pas",    ".pas"),
        ("VBScript",        "script.vbs",   ".vbs",    ".vbs"),
        ("CoffeeScript",    "app.coffee",   ".coffee", ".coffee"),
        ("Objective-C",     "view.m",       ".m",      ".m"),
        ("Scheme",          "eval.scm",     ".scm",    ".scm"),
        ("OCaml",           "lexer.ml",     ".ml",     ".ml"),
        ("LLM",             "agent.prompt", ".prompt", ".prompt"),
        ("reStructuredText","manual.rst",   ".rst",    ".rst"),
        ("Verilog",         "adder.v",      ".v",      ".v"),
        ("Systemverilog",   "module.sv",    ".sv",     ".sv"),
        ("Jinja",           "tmpl.jinja2",  ".jinja2", ".jinja2"),
        ("Handlebars",      "page.hbs",     ".hbs",    ".hbs"),
        ("Terraform",       "main.tf",      ".tf",     ".tf"),
        ("Solidity",        "token.sol",    ".sol",    ".sol"),
        ("Protobuf",        "schema.proto", ".proto",  ".proto"),
        ("Starlark",        "rules.bzl",    ".bzl",    ".bzl"),
    ])
    def test_sibling_language_architecture_paths_use_canonical_extensions(
        self,
        tmp_path,
        monkeypatch,
        language,
        code_filename,
        expected_example_suffix,
        expected_test_suffix,
    ):
        """Issue #551 scope expansion: all languages from the Step 6 NEEDS_FIX list
        must produce canonical extensions in get_pdd_file_paths, not raw language names.

        Before the fix, the local get_extension() fell back to language.lower() for any
        language not in its hard-coded map, producing suffixes like .c++, .haskell,
        .terraform, .restructuredtext, etc. instead of canonical .cpp, .hs, .tf, .rst.
        """
        monkeypatch.chdir(tmp_path)
        self._setup_dirs(tmp_path)

        basename = Path(code_filename).stem
        prompt_filename = f"{basename}_{language}.prompt"
        (tmp_path / "prompts" / prompt_filename).write_text(f"% {language} module\n")
        self._write_arch_json(tmp_path, prompt_filename, code_filename)

        paths = get_pdd_file_paths(basename, language, "prompts")

        assert paths["example"].suffix == expected_example_suffix, (
            f"Issue #551 ({language}): example path must end with {expected_example_suffix!r}, "
            f"got {paths['example'].suffix!r} (full path: {paths['example']})"
        )
        assert paths["test"].suffix == expected_test_suffix, (
            f"Issue #551 ({language}): test path must end with {expected_test_suffix!r}, "
            f"got {paths['test'].suffix!r} (full path: {paths['test']})"
        )
        assert paths["test_files"] == [paths["test"]], (
            f"Issue #551 ({language}): test_files must contain the canonical test path, "
            f"got {paths['test_files']!r}"
        )

    def test_makefile_uses_no_extension(self, tmp_path, monkeypatch):
        """Makefile has no extension in language_format.csv — example/test paths must
        not get a raw .makefile suffix.

        Before the fix: get_extension('Makefile') returned 'makefile', so paths
        would be *_example.makefile and test_*.makefile.
        After the fix: the canonical CSV row has empty extension, so get_extension
        returns '' and paths omit the suffix.
        """
        monkeypatch.chdir(tmp_path)
        self._setup_dirs(tmp_path)
        (tmp_path / "prompts" / "build_Makefile.prompt").write_text("% Build rules\n")
        self._write_arch_json(tmp_path, "build_Makefile.prompt", "Makefile")

        paths = get_pdd_file_paths("Makefile", "Makefile", "prompts")

        # The empty extension must not leave a malformed trailing-dot path
        # (e.g. "Makefile_example.") via the unconditional ".{extension}" join.
        for key in ("code", "example", "test"):
            name = paths[key].name
            assert not name.endswith("."), (
                f"Issue #551 (Makefile): {key} path must not end with a trailing "
                f"dot, got {name!r}"
            )
            assert ".makefile" not in name.lower(), (
                f"Issue #551 (Makefile): {key} path must not contain .makefile, "
                f"got {name!r}"
            )

        # test_files entries must likewise be free of trailing dots.
        for tf in paths.get("test_files", []):
            tf_name = Path(tf).name
            assert not tf_name.endswith("."), (
                f"Issue #551 (Makefile): test_files entry must not end with a "
                f"trailing dot, got {tf_name!r}"
            )

    def test_test_files_list_uses_canonical_extension(self, tmp_path, monkeypatch):
        """test_files key in get_pdd_file_paths return must also use the canonical extension.

        Before the fix, YAML produced test_files=[Path('tests/test_ci.yaml')] instead of
        [Path('tests/test_ci.yml')].
        """
        monkeypatch.chdir(tmp_path)
        self._setup_dirs(tmp_path)
        (tmp_path / "prompts" / "ci_YAML.prompt").write_text("% CI pipeline\n")
        self._write_arch_json(tmp_path, "ci_YAML.prompt", "ci.yml")

        paths = get_pdd_file_paths("ci", "YAML", "prompts")

        assert len(paths["test_files"]) >= 1, "test_files must be non-empty"
        for tf in paths["test_files"]:
            assert Path(tf).suffix == ".yml", (
                f"Issue #551: test_files entry must end with .yml, got {Path(tf).suffix!r} "
                f"(entry: {tf!r})"
            )
            assert Path(tf).suffix != ".yaml", (
                f"Issue #551: test_files must not contain .yaml path, got {tf!r}"
            )

    def test_pdd_path_unset_generation_matches_sync_extension(self, tmp_path, monkeypatch):
        """Issue #551 (FM1): with PDD_PATH unset, the extension generation WRITES
        (construct_paths' offline fallback) must equal the extension sync EXPECTS
        (get_pdd_file_paths). Before the shared-CSV fix, generation wrote
        ci_example.yaml (BUILTIN_EXT_MAP) while sync expected ci_example.yml
        (bundled CSV) -> sync looped regenerating forever.
        """
        from pdd.construct_paths import construct_paths

        monkeypatch.delenv("PDD_PATH", raising=False)
        monkeypatch.chdir(tmp_path)
        (tmp_path / "prompts").mkdir(parents=True, exist_ok=True)
        prompt_file = tmp_path / "prompts" / "ci_YAML.prompt"
        code_file = tmp_path / "ci.yml"
        prompt_file.write_text("% CI pipeline example\n")
        code_file.write_text("on: [push]\n")

        # What generation writes for `pdd example` when PDD_PATH is unset.
        _, _, output_paths, _ = construct_paths(
            input_file_paths={"prompt_file": str(prompt_file), "code_file": str(code_file)},
            force=True,
            quiet=True,
            command="example",
            command_options={},
        )
        written = Path(output_paths["output"])

        # What sync expects for the same module.
        expected = get_pdd_file_paths("ci", "YAML", "prompts")["example"]

        assert written.suffix == ".yml", (
            f"FM1: generation should write .yml offline, got {written.name!r}"
        )
        assert written.suffix == expected.suffix, (
            f"FM1: generation writes {written.suffix!r} but sync expects "
            f"{expected.suffix!r} (PDD_PATH unset) -> #551 regeneration loop"
        )
