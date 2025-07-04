# tests/test_sync_determine_operation.py

import pytest
import os
import sys
import json
import hashlib
import subprocess
from pathlib import Path
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
    read_fingerprint,
    read_run_report,
    PDD_DIR,
    META_DIR,
    LOCKS_DIR,
    get_pdd_dir,
    get_meta_dir,
    get_locks_dir
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
            assert get_locks_dir() / f"{BASENAME}_{LANGUAGE}.lock"


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
@patch('sync_determine_operation.construct_paths')
def test_decision_crash_on_exit_code_nonzero(mock_construct, pdd_test_environment):
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
    # And the run report shows a crash
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 1, "tests_passed": 0, "tests_failed": 0, "coverage": 0.0
    })
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE)
    assert decision.operation == 'verify'
    assert "Previous crash was fixed" in decision.reason

@patch('sync_determine_operation.construct_paths')
def test_decision_fix_on_test_failures(mock_construct, pdd_test_environment):
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 0, "tests_passed": 5, "tests_failed": 2, "coverage": 80.0
    })
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE)
    assert decision.operation == 'fix'
    assert "Test failures detected" in decision.reason

@patch('sync_determine_operation.construct_paths')
def test_decision_test_on_low_coverage(mock_construct, pdd_test_environment):
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 0, "tests_passed": 10, "tests_failed": 0, "coverage": 75.0
    })
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE)
    assert decision.operation == 'test'
    assert f"Coverage 75.0% below target {TARGET_COVERAGE:.1f}%" in decision.reason

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

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
    assert decision.operation == 'nothing'
    assert "All required files synchronized" in decision.reason

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
    assert decision.operation == 'analyze_conflict'
    assert "Multiple files changed" in decision.reason
    assert "prompt" in decision.details['changed_files']
    assert "code" in decision.details['changed_files']


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
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 0, "tests_passed": 10, "tests_failed": 0, "coverage": 75.0
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

    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir), skip_tests=True)
    assert decision.operation == 'nothing'
    assert "skip_tests=True" in decision.reason

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
    # Create run report with test failures (fix should still trigger)
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 0, "tests_passed": 5, "tests_failed": 2, "coverage": 80.0
    })
    
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, skip_tests=True, skip_verify=True)
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
        target_coverage = 90.0
        
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
        target_coverage = 90.0
        
        # Re-import after changing directory
        from pdd.sync_determine_operation import sync_determine_operation
        
        # Create files
        prompts_dir = Path("prompts")
        prompts_dir.mkdir(exist_ok=True)
        create_file(prompts_dir / f"{basename}_{language}.prompt", "...")
        create_file(Path(f"{basename}.py"), "def add(a, b): return a + b")
        create_file(Path(f"test_{basename}.py"), "assert add(2, 2) == 5")
        
        # Create run report with test failure (exit_code=0 but tests_failed>0 for 'fix' operation)
        run_report = {
            "timestamp": "2025-06-29T10:00:00",
            "exit_code": 0,  # Use 0 to avoid 'crash' operation
            "tests_passed": 0,
            "tests_failed": 1,
            "coverage": 50.0
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
        target_coverage = 90.0
        
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
        target_coverage = 90.0
        
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
        example_hash = create_file(Path(f"{basename}_example.py"), example_content)
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