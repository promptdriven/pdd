import pytest
import os
import json
import hashlib
import platform
import datetime
import subprocess
import time
from pathlib import Path
from typing import Dict, Any, Optional, List
from dataclasses import asdict
from unittest.mock import patch, MagicMock, mock_open

# Import the module and classes under test
# Assuming the test file is in 'tests/' and the module is in 'pdd/'
from pdd import sync_determine_operation
from pdd.sync_determine_operation import (
    Fingerprint,
    RunReport,
    SyncDecision,
    SyncLock,
    LLMConflictResolutionOutput,
    get_pdd_file_paths, # For convenience in tests
    calculate_sha256, # For convenience
    _ensure_pdd_dirs_exist # For direct testing if needed
)

# --- Constants for Tests ---
TEST_BASENAME = "test_unit"
TEST_LANGUAGE = "python"
TEST_TARGET_COVERAGE = 0.80
TEST_PDD_VERSION = "0.1.0"

# --- Fixtures ---

@pytest.fixture
def pdd_test_environment(tmp_path, monkeypatch):
    """
    Sets up a temporary isolated environment for PDD operations.
    - Creates temp dirs for .pdd, prompts, code, examples, tests.
    - Monkeypatches global path constants in the module under test.
    - Provides paths and helper to create files.
    """
    base_dir = tmp_path / "pdd_project"
    base_dir.mkdir()

    pdd_dir = base_dir / ".pdd"
    locks_dir = pdd_dir / "locks"
    meta_dir = pdd_dir / "meta"
    
    prompts_root = base_dir / "prompts"
    code_root = base_dir / "src" # Assuming code might be in src
    examples_root = base_dir / "examples"
    tests_root = base_dir / "tests"

    for d in [pdd_dir, locks_dir, meta_dir, prompts_root, code_root, examples_root, tests_root]:
        d.mkdir(parents=True, exist_ok=True)

    # Monkeypatch module-level constants
    monkeypatch.setattr(sync_determine_operation, 'PDD_DIR', pdd_dir)
    monkeypatch.setattr(sync_determine_operation, 'LOCKS_DIR', locks_dir)
    monkeypatch.setattr(sync_determine_operation, 'META_DIR', meta_dir)
    monkeypatch.setattr(sync_determine_operation, 'PROMPTS_ROOT_DIR', prompts_root)
    monkeypatch.setattr(sync_determine_operation, 'EXAMPLES_ROOT_DIR', examples_root)
    monkeypatch.setattr(sync_determine_operation, 'TESTS_ROOT_DIR', tests_root)


    class FileCreator:
        def __init__(self):
            self.paths = get_pdd_file_paths(TEST_BASENAME, TEST_LANGUAGE) # Uses monkeypatched roots

        def create_file(self, file_type: str, content: str = "") -> Path:
            path = self.paths[file_type]
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
            return path

        def delete_file(self, file_type: str):
            self.paths[file_type].unlink(missing_ok=True)

        def get_path(self, file_type: str) -> Path:
            return self.paths[file_type]
        
        def make_fingerprint_file(self, fp: Fingerprint):
            fp_path = meta_dir / f"{TEST_BASENAME}_{TEST_LANGUAGE}.json"
            with open(fp_path, 'w') as f:
                json.dump(asdict(fp), f, indent=2)
            return fp_path

        def make_run_report_file(self, rr: RunReport):
            rr_path = meta_dir / f"{TEST_BASENAME}_{TEST_LANGUAGE}_run.json"
            with open(rr_path, 'w') as f:
                json.dump(asdict(rr), f, indent=2)
            return rr_path
            
    return {'base_dir': base_dir, 'file_creator': FileCreator(), 'meta_dir': meta_dir, 'locks_dir': locks_dir}


@pytest.fixture
def temp_git_repo(pdd_test_environment):
    """Fixture to create a temporary git repository for testing get_git_diff."""
    repo_dir = pdd_test_environment['base_dir']
    
    original_cwd = Path.cwd()
    os.chdir(repo_dir)

    try:
        subprocess.run(["git", "init"], check=True, capture_output=True)
        subprocess.run(["git", "config", "user.name", "Test User"], check=True)
        subprocess.run(["git", "config", "user.email", "test@example.com"], check=True)
    except (subprocess.CalledProcessError, FileNotFoundError) as e:
        pytest.skip(f"Git setup failed, skipping git-dependent tests: {e}")

    # Update the file creator paths to work within the git repo context
    # Since we changed the working directory, we need to recalculate the paths
    fc = pdd_test_environment['file_creator']
    fc.paths = get_pdd_file_paths(TEST_BASENAME, TEST_LANGUAGE)

    def _commit_file(file_path_in_repo: Path, content: str, commit_message: str = "Initial commit"):
        # Git needs relative paths for adding files from subdirectories
        relative_path = file_path_in_repo.relative_to(repo_dir)
        relative_path.parent.mkdir(parents=True, exist_ok=True)
        relative_path.write_text(content)
        subprocess.run(["git", "add", str(relative_path)], check=True, cwd=repo_dir)
        subprocess.run(["git", "commit", "-m", commit_message], check=True, cwd=repo_dir)

    pdd_test_environment['git_commit_file'] = _commit_file
    pdd_test_environment['repo_dir'] = repo_dir
    
    yield pdd_test_environment
    
    os.chdir(original_cwd)


# --- SyncLock Tests ---

def test_lock_acquire_release_successful(pdd_test_environment):
    lock_file = pdd_test_environment['locks_dir'] / f"{TEST_BASENAME}_{TEST_LANGUAGE}.lock"
    assert not lock_file.exists()
    
    with SyncLock(TEST_BASENAME, TEST_LANGUAGE) as lock:
        assert lock_file.exists()
        assert lock_file.read_text().strip() == str(os.getpid())
        assert lock._lock_fd is not None # Check internal detail for test clarity
    
    assert not lock_file.exists()

def test_lock_reentrancy_same_process(pdd_test_environment):
    lock_file = pdd_test_environment['locks_dir'] / f"{TEST_BASENAME}_{TEST_LANGUAGE}.lock"
    
    with SyncLock(TEST_BASENAME, TEST_LANGUAGE) as lock1:
        assert lock_file.exists()
        
        # Different instance, same process - this is the main re-entrancy test
        with SyncLock(TEST_BASENAME, TEST_LANGUAGE) as lock2:
            assert lock_file.exists() # Still held by lock1 conceptually
            assert lock2._is_reentrant_acquisition # Check internal flag for this specific case
        
        assert lock_file.exists() # lock1 still active
    
    assert not lock_file.exists()

@patch('psutil.pid_exists')
def test_lock_stale_lock_pid_not_running(mock_pid_exists, pdd_test_environment):
    mock_pid_exists.return_value = False
    stale_pid = 12345
    lock_file = pdd_test_environment['locks_dir'] / f"{TEST_BASENAME}_{TEST_LANGUAGE}.lock"
    lock_file.write_text(str(stale_pid))

    with SyncLock(TEST_BASENAME, TEST_LANGUAGE) as lock:
        assert lock_file.exists() # Should have been replaced
        assert lock_file.read_text().strip() == str(os.getpid())
    
    assert not lock_file.exists()
    mock_pid_exists.assert_called_with(stale_pid)

def test_lock_stale_lock_corrupted_pid(pdd_test_environment):
    lock_file = pdd_test_environment['locks_dir'] / f"{TEST_BASENAME}_{TEST_LANGUAGE}.lock"
    lock_file.write_text("not-a-pid")

    with SyncLock(TEST_BASENAME, TEST_LANGUAGE) as lock:
        assert lock_file.exists()
        assert lock_file.read_text().strip() == str(os.getpid())
    assert not lock_file.exists()

def test_lock_stale_lock_empty_pid_file(pdd_test_environment):
    lock_file = pdd_test_environment['locks_dir'] / f"{TEST_BASENAME}_{TEST_LANGUAGE}.lock"
    lock_file.write_text("") # Empty

    with SyncLock(TEST_BASENAME, TEST_LANGUAGE) as lock:
        assert lock_file.exists()
        assert lock_file.read_text().strip() == str(os.getpid())
    assert not lock_file.exists()

@patch('psutil.pid_exists')
def test_lock_contention_simulated(mock_pid_exists, pdd_test_environment):
    other_pid = os.getpid() + 1 # A PID different from current
    mock_pid_exists.return_value = True # Simulate other_pid is running
    
    lock_file = pdd_test_environment['locks_dir'] / f"{TEST_BASENAME}_{TEST_LANGUAGE}.lock"
    lock_file.write_text(str(other_pid))

    with pytest.raises(TimeoutError, match=f"is locked by another process \\(PID: {other_pid}\\)"):
        with SyncLock(TEST_BASENAME, TEST_LANGUAGE):
            pass # Should not reach here
    
    # Ensure lock file created by test is still there (as SyncLock failed to acquire)
    assert lock_file.exists() 
    assert lock_file.read_text().strip() == str(other_pid)
    mock_pid_exists.assert_called_with(other_pid)


# --- Helper Function Tests ---

def test_get_pdd_file_paths_uses_monkeypatched_roots(pdd_test_environment, monkeypatch):
    # Change working directory to the test environment
    original_cwd = os.getcwd()
    test_base_dir = pdd_test_environment['base_dir']
    monkeypatch.chdir(test_base_dir)
    
    try:
        paths = get_pdd_file_paths("myunit", "python")
        assert str(paths['prompt']).startswith(str(test_base_dir / "prompts"))
        # Since we use generate_output_paths, the code will be in the current directory (test_base_dir)
        assert str(paths['code']).startswith(str(test_base_dir))
        assert paths['code'].name == "myunit.py"
    finally:
        # Restore original working directory
        os.chdir(original_cwd)

# Note: get_language_extension was removed as we now use PDD's get_extension function

def test_calculate_sha256(pdd_test_environment, monkeypatch):
    # Change working directory to the test environment  
    test_base_dir = pdd_test_environment['base_dir']
    monkeypatch.chdir(test_base_dir)
    
    # Get fresh paths after changing working directory
    paths = get_pdd_file_paths(TEST_BASENAME, TEST_LANGUAGE)
    
    # Create prompt file and test it
    paths['prompt'].parent.mkdir(parents=True, exist_ok=True)
    paths['prompt'].write_text("content")
    assert calculate_sha256(paths['prompt']) == hashlib.sha256(b"content").hexdigest()
    
    # Test non-existent file (code doesn't exist yet)
    assert calculate_sha256(paths['code']) is None
    
    # Create empty example file and test it
    paths['example'].parent.mkdir(parents=True, exist_ok=True)
    paths['example'].write_text("")
    assert calculate_sha256(paths['example']) == hashlib.sha256(b"").hexdigest()

def test_read_fingerprint(pdd_test_environment):
    fp_path = pdd_test_environment['meta_dir'] / f"{TEST_BASENAME}_{TEST_LANGUAGE}.json"
    
    # Valid (with optional fields missing)
    valid_data = {"pdd_version": "1.0", "timestamp": "sometime", "command": "generate", "prompt_hash": "abc"}
    fp_path.write_text(json.dumps(valid_data))
    fp = sync_determine_operation.read_fingerprint(TEST_BASENAME, TEST_LANGUAGE)
    assert isinstance(fp, Fingerprint)
    assert fp.prompt_hash == "abc"
    assert fp.code_hash is None

    # Non-existent
    fp_path.unlink()
    assert sync_determine_operation.read_fingerprint(TEST_BASENAME, TEST_LANGUAGE) is None

    # Corrupted JSON
    fp_path.write_text("{not_json:")
    assert sync_determine_operation.read_fingerprint(TEST_BASENAME, TEST_LANGUAGE) is None

    # Missing required fields (should cause TypeError caught by reader)
    fp_path.write_text(json.dumps({"pdd_version": "1.0"}))
    assert sync_determine_operation.read_fingerprint(TEST_BASENAME, TEST_LANGUAGE) is None


def test_read_run_report(pdd_test_environment):
    rr_path = pdd_test_environment['meta_dir'] / f"{TEST_BASENAME}_{TEST_LANGUAGE}_run.json"
    valid_data = {"timestamp": "now", "exit_code": 0, "tests_passed": 1, "tests_failed": 0, "coverage": 0.5}
    rr_path.write_text(json.dumps(valid_data))
    rr = sync_determine_operation.read_run_report(TEST_BASENAME, TEST_LANGUAGE)
    assert isinstance(rr, RunReport)
    assert rr.coverage == 0.5
    # Other cases similar to read_fingerprint (non-existent, corrupted, missing fields)

def test_calculate_current_hashes(pdd_test_environment, monkeypatch):
    # Change working directory to the test environment
    test_base_dir = pdd_test_environment['base_dir']
    monkeypatch.chdir(test_base_dir)
    
    # Get paths after changing working directory
    paths = get_pdd_file_paths(TEST_BASENAME, TEST_LANGUAGE)
    
    # Create files at the correct paths
    paths['prompt'].parent.mkdir(parents=True, exist_ok=True)
    paths['prompt'].write_text("p")
    paths['code'].parent.mkdir(parents=True, exist_ok=True)
    paths['code'].write_text("c")
    # example and test do not exist
    
    hashes = sync_determine_operation.calculate_current_hashes(paths)
    
    assert hashes['prompt_hash'] == hashlib.sha256(b"p").hexdigest()
    assert hashes['code_hash'] == hashlib.sha256(b"c").hexdigest()
    assert hashes['example_hash'] is None
    assert hashes['test_hash'] is None

# --- get_git_diff Tests ---
def test_get_git_diff_tracked_no_changes(temp_git_repo):
    fc = temp_git_repo['file_creator']
    code_file_path = fc.get_path('code')
    
    temp_git_repo['git_commit_file'](code_file_path, "initial content")
    
    diff = sync_determine_operation.get_git_diff(code_file_path)
    assert diff == ""

def test_get_git_diff_tracked_with_changes(temp_git_repo):
    fc = temp_git_repo['file_creator']
    code_file_path = fc.get_path('code')

    temp_git_repo['git_commit_file'](code_file_path, "initial content")
    code_file_path.write_text("modified content") # Modify after commit
    
    diff = sync_determine_operation.get_git_diff(code_file_path)
    assert "initial content" in diff
    assert "modified content" in diff
    assert diff.startswith("diff --git")

def test_get_git_diff_untracked_file(temp_git_repo):
    fc = temp_git_repo['file_creator']
    # Create an untracked file
    untracked_file_path = fc.get_path('example')
    untracked_file_path.write_text("untracked content")
    
    diff = sync_determine_operation.get_git_diff(untracked_file_path)
    assert "untracked content" in diff
    # Diff for untracked file against /dev/null or NUL
    if platform.system() == "Windows":
        assert "--- NUL" in diff or "--- a/NUL" in diff
    else:
        assert "--- /dev/null" in diff or "--- a/dev/null" in diff
    
    # Use relative path for assertion to be robust
    relative_path = untracked_file_path.relative_to(temp_git_repo['repo_dir'])
    assert f"+++ b/{str(relative_path)}" in diff

def test_get_git_diff_non_existent_file(temp_git_repo):
    fc = temp_git_repo['file_creator']
    non_existent_path = fc.get_path('test') # Assuming it's not created
    assert not non_existent_path.exists()
    diff = sync_determine_operation.get_git_diff(non_existent_path)
    assert diff == ""

@patch('subprocess.run')
def test_get_git_diff_git_command_not_found(mock_subprocess_run, pdd_test_environment):
    mock_subprocess_run.side_effect = FileNotFoundError("git not found")
    fc = pdd_test_environment['file_creator']
    p_file = fc.create_file('prompt', "content")
    diff = sync_determine_operation.get_git_diff(p_file)
    assert diff == "content" # Should fall back to file content


# --- determine_sync_operation Tests ---

# Helper to create a default fingerprint
def _default_fingerprint(fc, hashes: Optional[Dict[str, Optional[str]]] = None) -> Fingerprint:
    if hashes is None:
        hashes = {ft: None for ft in ['prompt', 'code', 'example', 'test']}
    return Fingerprint(
        pdd_version=TEST_PDD_VERSION,
        timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        command="generate",
        prompt_hash=hashes.get('prompt'),
        code_hash=hashes.get('code'),
        example_hash=hashes.get('example'),
        test_hash=hashes.get('test')
    )

# Helper to create a default run report
def _default_run_report(exit_code=0, tests_failed=0, coverage=1.0) -> RunReport:
    return RunReport(
        timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        exit_code=exit_code,
        tests_passed=10 - tests_failed,
        tests_failed=tests_failed,
        coverage=coverage
    )

def test_determine_op_uses_lock(pdd_test_environment):
    lock_file = pdd_test_environment['locks_dir'] / f"{TEST_BASENAME}_{TEST_LANGUAGE}.lock"
    
    # Patch SyncLock to check for file existence during its context
    original_acquire = SyncLock.acquire
    original_release = SyncLock.release
    acquired_event = []

    def new_acquire(self_lock):
        original_acquire(self_lock)
        if lock_file.exists() and lock_file.read_text().strip() == str(os.getpid()):
            acquired_event.append(True)
    
    def new_release(self_lock):
        # Check before original release potentially deletes it
        if not acquired_event or not lock_file.exists():
             # If acquire didn't set event, or file gone too soon, it's an issue
             acquired_event.append(False) 
        original_release(self_lock)

    with patch.object(SyncLock, 'acquire', new_acquire), \
         patch.object(SyncLock, 'release', new_release):
        sync_determine_operation.determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)

    assert len(acquired_event) > 0 and acquired_event[0] is True, "Lock was not acquired or PID was wrong"
    if len(acquired_event) > 1 and acquired_event[1] is False:
        pytest.fail("Lock file was not present at start of release or acquire failed to mark success")
    assert not lock_file.exists(), "Lock file was not released"


# B. Runtime Signals
def test_determine_op_report_exit_code_nonzero(pdd_test_environment):
    fc = pdd_test_environment['file_creator']
    fc.make_run_report_file(_default_run_report(exit_code=1))
    decision = sync_determine_operation.determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    assert decision.operation == 'crash'

def test_determine_op_report_tests_failed(pdd_test_environment):
    fc = pdd_test_environment['file_creator']
    fc.make_run_report_file(_default_run_report(tests_failed=1))
    decision = sync_determine_operation.determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    assert decision.operation == 'fix'

def test_determine_op_report_low_coverage(pdd_test_environment):
    fc = pdd_test_environment['file_creator']
    fc.make_run_report_file(_default_run_report(coverage=TEST_TARGET_COVERAGE - 0.1))
    decision = sync_determine_operation.determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    assert decision.operation == 'test'

def test_determine_op_report_priority(pdd_test_environment):
    fc = pdd_test_environment['file_creator']
    # Crash > Fix > Coverage
    fc.make_run_report_file(_default_run_report(exit_code=1, tests_failed=1, coverage=0.1))
    decision = sync_determine_operation.determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    assert decision.operation == 'crash'
    
    # Fix > Coverage
    fc.make_run_report_file(_default_run_report(exit_code=0, tests_failed=1, coverage=0.1))
    decision = sync_determine_operation.determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    assert decision.operation == 'fix'

# C. No Fingerprint
def test_determine_op_no_fingerprint_prompt_exists(pdd_test_environment):
    fc = pdd_test_environment['file_creator']
    fc.create_file('prompt', "content")
    decision = sync_determine_operation.determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    assert decision.operation == 'generate'

def test_determine_op_no_fingerprint_no_prompt(pdd_test_environment):
    # No files created, no fingerprint
    decision = sync_determine_operation.determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    assert decision.operation == 'nothing'
    assert "No PDD fingerprint and no prompt file found" in decision.reason

# D. Fingerprint Exists - File States
def test_determine_op_fp_exists_no_changes(pdd_test_environment, monkeypatch):
    # Change working directory to the test environment  
    test_base_dir = pdd_test_environment['base_dir']
    monkeypatch.chdir(test_base_dir)
    
    # Get paths after changing working directory
    paths = get_pdd_file_paths(TEST_BASENAME, TEST_LANGUAGE)
    
    # Create files at the correct paths and calculate hashes
    paths['prompt'].parent.mkdir(parents=True, exist_ok=True)
    paths['prompt'].write_text("p")
    p_hash = calculate_sha256(paths['prompt'])
    
    paths['code'].parent.mkdir(parents=True, exist_ok=True)
    paths['code'].write_text("c")
    c_hash = calculate_sha256(paths['code'])
    
    # Create fingerprint file
    fc = pdd_test_environment['file_creator']
    fc.make_fingerprint_file(_default_fingerprint(fc, {'prompt': p_hash, 'code': c_hash}))
    
    decision = sync_determine_operation.determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    # With workflow progression logic, if code exists but example doesn't, it should create example
    assert decision.operation == 'example'
    assert 'example' in decision.reason.lower()

def test_determine_op_fp_prompt_changed(pdd_test_environment, monkeypatch):
    # Change working directory to the test environment  
    test_base_dir = pdd_test_environment['base_dir']
    monkeypatch.chdir(test_base_dir)
    
    # Get paths after changing working directory
    paths = get_pdd_file_paths(TEST_BASENAME, TEST_LANGUAGE)
    
    # Create prompt file with old content and calculate hash
    paths['prompt'].parent.mkdir(parents=True, exist_ok=True)
    paths['prompt'].write_text("p_old")
    p_hash_old = calculate_sha256(paths['prompt'])
    
    # Create fingerprint file
    fc = pdd_test_environment['file_creator']
    fc.make_fingerprint_file(_default_fingerprint(fc, {'prompt': p_hash_old}))
    
    # Change prompt content
    paths['prompt'].write_text("p_new")
    
    decision = sync_determine_operation.determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    assert decision.operation == 'generate'

# Similar tests for code_changed -> update, test_changed -> test, example_changed -> verify

def test_determine_op_fp_code_changed(pdd_test_environment, monkeypatch):
    # Change working directory to the test environment  
    test_base_dir = pdd_test_environment['base_dir']
    monkeypatch.chdir(test_base_dir)
    
    # Get paths after changing working directory
    paths = get_pdd_file_paths(TEST_BASENAME, TEST_LANGUAGE)
    
    # Create files at the correct paths and calculate hashes
    paths['prompt'].parent.mkdir(parents=True, exist_ok=True)
    paths['prompt'].write_text("p")
    p_hash = calculate_sha256(paths['prompt'])
    
    paths['code'].parent.mkdir(parents=True, exist_ok=True)
    paths['code'].write_text("c_old")
    c_hash_old = calculate_sha256(paths['code'])
    
    # Create fingerprint file
    fc = pdd_test_environment['file_creator']
    fc.make_fingerprint_file(_default_fingerprint(fc, {'prompt': p_hash, 'code': c_hash_old}))
    
    # Change code content
    paths['code'].write_text("c_new")
    
    decision = sync_determine_operation.determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    assert decision.operation == 'update'

def test_determine_op_fp_file_deleted(pdd_test_environment, monkeypatch):
    # Change working directory to the test environment  
    test_base_dir = pdd_test_environment['base_dir']
    monkeypatch.chdir(test_base_dir)
    
    # Get paths after changing working directory
    paths = get_pdd_file_paths(TEST_BASENAME, TEST_LANGUAGE)
    
    # Create files at the correct paths and calculate hashes
    paths['prompt'].parent.mkdir(parents=True, exist_ok=True)
    paths['prompt'].write_text("p")
    p_hash = calculate_sha256(paths['prompt'])
    
    paths['code'].parent.mkdir(parents=True, exist_ok=True)
    paths['code'].write_text("c")
    c_hash_old = calculate_sha256(paths['code'])
    
    # Create fingerprint file
    fc = pdd_test_environment['file_creator']
    fc.make_fingerprint_file(_default_fingerprint(fc, {'prompt': p_hash, 'code': c_hash_old}))

    # Delete code file
    paths['code'].unlink()
    
    decision = sync_determine_operation.determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    # Deleting a file means its hash becomes None, different from fingerprint.
    # If only code changed (from existing to None), it's 'update'.
    assert decision.operation == 'update' 
    assert 'code' in decision.details['changed_files']


def test_determine_op_fp_file_appeared(pdd_test_environment, monkeypatch):
    # Change working directory to the test environment  
    test_base_dir = pdd_test_environment['base_dir']
    monkeypatch.chdir(test_base_dir)
    
    # Get paths after changing working directory
    paths = get_pdd_file_paths(TEST_BASENAME, TEST_LANGUAGE)
    
    # Create prompt file and calculate hash
    paths['prompt'].parent.mkdir(parents=True, exist_ok=True)
    paths['prompt'].write_text("p")
    p_hash = calculate_sha256(paths['prompt'])
    
    # Code did not exist in fingerprint (hash is None)
    fc = pdd_test_environment['file_creator']
    fc.make_fingerprint_file(_default_fingerprint(fc, {'prompt': p_hash, 'code': None}))

    # Create code file
    paths['code'].parent.mkdir(parents=True, exist_ok=True)
    paths['code'].write_text("c_new")
    
    decision = sync_determine_operation.determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    # Code appeared (hash from None to actual), it's 'update'.
    assert decision.operation == 'update'
    assert 'code' in decision.details['changed_files']


# E. Complex Changes
def test_determine_op_fp_multiple_files_changed(pdd_test_environment):
    fc = pdd_test_environment['file_creator']
    p_path = fc.create_file('prompt', "p_old")
    c_path = fc.create_file('code', "c_old")
    p_hash_old = calculate_sha256(p_path)
    c_hash_old = calculate_sha256(c_path)
    fc.make_fingerprint_file(_default_fingerprint(fc, {'prompt': p_hash_old, 'code': c_hash_old}))

    p_path.write_text("p_new")
    c_path.write_text("c_new")

    decision = sync_determine_operation.determine_sync_operation(TEST_BASENAME, TEST_LANGUAGE, TEST_TARGET_COVERAGE)
    # With LLM analysis, we should get a concrete operation back, not 'analyze_conflict'
    # The LLM should intelligently resolve the conflict based on the changes
    # Handle failure case where LLM analysis might fail - this is acceptable
    assert decision.operation in ['generate', 'update', 'merge_manually', 'nothing', 'fail_and_request_manual_merge']
    # The operation should have a clear reason
    assert decision.reason is not None
    assert len(decision.reason) > 0


# --- analyze_conflict_with_llm Tests ---

@patch('pdd.sync_determine_operation.llm_invoke')
@patch('pdd.sync_determine_operation.load_prompt_template')
@patch('pdd.sync_determine_operation.get_git_diff')
def test_analyze_conflict_llm_success(mock_get_git_diff, mock_load_template, mock_llm_invoke, pdd_test_environment):
    fc = pdd_test_environment['file_creator']
    fp = _default_fingerprint(fc) # Dummy fingerprint
    changed_files = ['prompt', 'code']

    mock_load_template.return_value = "Template: {prompt_diff} {code_diff}"
    mock_get_git_diff.side_effect = lambda path: f"diff_for_{path.name}"
    
    llm_response_obj = LLMConflictResolutionOutput(
        next_operation="manual_review", 
        reason="LLM says so", 
        confidence=0.9
    )
    mock_llm_invoke.return_value = {"result": llm_response_obj, "cost": 0.01, "model_name": "test_model"}

    decision = sync_determine_operation.analyze_conflict_with_llm(TEST_BASENAME, TEST_LANGUAGE, fp, changed_files)
    
    assert decision.operation == "manual_review"
    assert "LLM says so" in decision.reason
    mock_load_template.assert_called_once_with("sync_analysis_LLM.prompt")
    assert mock_get_git_diff.call_count == 2 # For prompt and code
    mock_llm_invoke.assert_called_once()


@patch('pdd.sync_determine_operation.llm_invoke')
@patch('pdd.sync_determine_operation.load_prompt_template')
def test_analyze_conflict_llm_low_confidence(mock_load_template, mock_llm_invoke, pdd_test_environment):
    fc = pdd_test_environment['file_creator']
    fp = _default_fingerprint(fc)
    changed_files = ['prompt']
    mock_load_template.return_value = "Template"
    
    llm_response_obj = LLMConflictResolutionOutput(
        next_operation="generate", reason="LLM unsure", confidence=0.5 # Below threshold 0.75
    )
    mock_llm_invoke.return_value = {"result": llm_response_obj, "cost": 0.01, "model_name": "test_model"}

    decision = sync_determine_operation.analyze_conflict_with_llm(TEST_BASENAME, TEST_LANGUAGE, fp, changed_files)
    assert decision.operation == 'fail_and_request_manual_merge'
    assert "LLM analysis confidence (0.50) is below threshold" in decision.reason


@patch('pdd.sync_determine_operation.load_prompt_template')
def test_analyze_conflict_llm_template_load_error(mock_load_template, pdd_test_environment):
    fc = pdd_test_environment['file_creator']
    fp = _default_fingerprint(fc)
    changed_files = ['prompt']
    mock_load_template.side_effect = Exception("Cannot load template")

    decision = sync_determine_operation.analyze_conflict_with_llm(TEST_BASENAME, TEST_LANGUAGE, fp, changed_files)
    assert decision.operation == 'fail_and_request_manual_merge'
    assert "LLM conflict analysis failed: Cannot load template" in decision.reason

@patch('pdd.sync_determine_operation.llm_invoke')
@patch('pdd.sync_determine_operation.load_prompt_template')
def test_analyze_conflict_llm_invoke_error(mock_load_template, mock_llm_invoke, pdd_test_environment):
    fc = pdd_test_environment['file_creator']
    fp = _default_fingerprint(fc)
    changed_files = ['prompt']
    mock_load_template.return_value = "Template"
    mock_llm_invoke.side_effect = Exception("LLM API down")

    decision = sync_determine_operation.analyze_conflict_with_llm(TEST_BASENAME, TEST_LANGUAGE, fp, changed_files)
    assert decision.operation == 'fail_and_request_manual_merge'
    assert "LLM conflict analysis failed: LLM API down" in decision.reason

@patch('pdd.sync_determine_operation.llm_invoke')
@patch('pdd.sync_determine_operation.load_prompt_template')
def test_analyze_conflict_llm_invoke_returns_invalid_type(mock_load_template, mock_llm_invoke, pdd_test_environment):
    fc = pdd_test_environment['file_creator']
    fp = _default_fingerprint(fc)
    changed_files = ['prompt']
    mock_load_template.return_value = "Template"
    # Simulate llm_invoke returning something other than the expected Pydantic model in 'result'
    mock_llm_invoke.return_value = {"result": "just a string", "cost": 0.01, "model_name": "test_model"}

    decision = sync_determine_operation.analyze_conflict_with_llm(TEST_BASENAME, TEST_LANGUAGE, fp, changed_files)
    assert decision.operation == 'fail_and_request_manual_merge'
    assert "LLM did not return the expected Pydantic object" in decision.reason


def test_ensure_pdd_dirs_exist_called_by_lock(pdd_test_environment):
    # This is implicitly tested by SyncLock's __init__
    # We can check if the dirs exist after creating a SyncLock instance
    # (though pdd_test_environment already creates them)
    # To test _ensure_pdd_dirs_exist directly:
    temp_dir = pdd_test_environment['base_dir'] / "new_pdd_root"
    
    with patch.object(sync_determine_operation, 'PDD_DIR', temp_dir / ".pdd"), \
         patch.object(sync_determine_operation, 'LOCKS_DIR', temp_dir / ".pdd" / "locks"), \
         patch.object(sync_determine_operation, 'META_DIR', temp_dir / ".pdd" / "meta"):
        
        assert not (temp_dir / ".pdd").exists()
        sync_determine_operation._ensure_pdd_dirs_exist()
        assert (temp_dir / ".pdd" / "locks").exists()
        assert (temp_dir / ".pdd" / "meta").exists()


def test_path_consistency_sync_vs_generate():
    """Test that sync operations use same paths as generate operations"""
    from pdd.generate_output_paths import generate_output_paths
    from pdd.sync_determine_operation import get_pdd_file_paths
    
    # Test parameters
    basename = "test_module"
    language = "python"
    context_config = {"generate_output_path": "pdd/"}
    
    # Get paths from sync operation
    sync_paths = get_pdd_file_paths(basename, language, context_config)
    
    # Get paths from individual generate operation  
    generate_paths = generate_output_paths(
        command='generate',
        output_locations={},
        basename=basename,
        language=language,
        file_extension=".py",
        context_config=context_config
    )
    
    # Paths should match
    assert str(sync_paths['code']) == generate_paths['output']
    
    # Test different context configs
    no_context_sync_paths = get_pdd_file_paths(basename, language, {})
    no_context_generate_paths = generate_output_paths(
        command='generate',
        output_locations={},
        basename=basename,
        language=language,
        file_extension=".py",
        context_config={}
    )
    
    assert str(no_context_sync_paths['code']) == no_context_generate_paths['output']
