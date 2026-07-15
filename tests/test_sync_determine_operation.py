import pytest
import os
import sys
import json
import hashlib
import subprocess
from pathlib import Path
from datetime import datetime, timezone
from unittest.mock import patch, MagicMock, mock_open

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
    UnsafeOutputPathError,
)

BASENAME = "test_unit"
LANGUAGE = "python"
TARGET_COVERAGE = 90.0


@pytest.fixture
def pdd_test_environment(tmp_path):
    original_cwd = Path.cwd()
    os.chdir(tmp_path)
    Path(".pdd/meta").mkdir(parents=True, exist_ok=True)
    Path(".pdd/locks").mkdir(parents=True, exist_ok=True)
    Path("prompts").mkdir(exist_ok=True)
    pdd_module = sys.modules['sync_determine_operation']
    pdd_module.PDD_DIR = pdd_module.get_pdd_dir()
    pdd_module.META_DIR = pdd_module.get_meta_dir()
    pdd_module.LOCKS_DIR = pdd_module.get_locks_dir()
    yield tmp_path
    os.chdir(original_cwd)
    pdd_module.PDD_DIR = pdd_module.get_pdd_dir()
    pdd_module.META_DIR = pdd_module.get_meta_dir()
    pdd_module.LOCKS_DIR = pdd_module.get_locks_dir()


def create_file(path: Path, content: str = "") -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return calculate_sha256(path)


def create_fingerprint_file(path: Path, data: dict):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, 'w') as f:
        json.dump(data, f)


def create_run_report_file(path: Path, data: dict):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, 'w') as f:
        json.dump(data, f)


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
        stale_pid = 99999
        lock_file.write_text(str(stale_pid))
        monkeypatch.setattr("psutil.pid_exists", lambda pid: pid != stale_pid)
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
            lock.acquire()
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


@pytest.mark.usefixtures("pdd_test_environment")
@patch('sync_determine_operation.construct_paths')
def test_log_mode_skips_lock(mock_construct):
    with patch('sync_determine_operation.SyncLock') as mock_lock:
        sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, log_mode=True)
        mock_lock.assert_not_called()

    with patch('sync_determine_operation.SyncLock') as mock_lock:
        sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, log_mode=False)
        mock_lock.assert_called_once_with(BASENAME, LANGUAGE)


def test_context_aware_fix_over_crash_logic(pdd_test_environment):
    prompts_dir = pdd_test_environment / "prompts"
    prompts_dir.mkdir(exist_ok=True)
    prompt_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", "Test prompt")

    create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
        "pdd_version": "1.0.0", "timestamp": "2025-07-15T12:00:00Z",
        "command": "generate", "prompt_hash": prompt_hash,
        "code_hash": "test_hash", "example_hash": None, "test_hash": None
    })
    create_run_report_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json", {
        "timestamp": "2025-07-15T12:00:00Z", "exit_code": 1,
        "tests_passed": 0, "tests_failed": 0, "coverage": 0.0
    })
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
    assert decision.operation == 'crash'
    assert "no successful example history" in decision.reason.lower()
    assert decision.details['example_success_history'] == False

    create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
        "pdd_version": "1.0.0", "timestamp": "2025-07-15T12:00:00Z",
        "command": "verify", "prompt_hash": prompt_hash,
        "code_hash": "test_hash", "example_hash": "test_hash", "test_hash": None
    })
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
    assert decision.operation == 'fix'
    assert "prefer fix over crash" in decision.reason.lower()
    assert decision.details['example_success_history'] == True

    create_fingerprint_file(get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json", {
        "pdd_version": "1.0.0", "timestamp": "2025-07-15T12:00:00Z",
        "command": "test", "prompt_hash": prompt_hash,
        "code_hash": "test_hash", "example_hash": "test_hash", "test_hash": "test_hash"
    })
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir))
    assert decision.operation == 'fix'
    assert "prefer fix over crash" in decision.reason.lower()
    assert decision.details['example_success_history'] == True


@pytest.mark.usefixtures("pdd_test_environment")
@patch('sync_determine_operation.construct_paths')
def test_decision_crash_on_exit_code_nonzero(mock_construct):
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


@pytest.mark.usefixtures("pdd_test_environment")
@patch('sync_determine_operation.construct_paths')
def test_decision_verify_after_crash_fix(mock_construct):
    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0", "timestamp": "t", "command": "crash",
        "prompt_hash": "p", "code_hash": "c", "example_hash": "e", "test_hash": "t"
    })
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 0, "tests_passed": 0, "tests_failed": 0, "coverage": 0.0
    })
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE)
    assert decision.operation == 'verify'
    assert "Previous crash operation completed" in decision.reason


@pytest.mark.usefixtures("pdd_test_environment")
@patch('sync_determine_operation.construct_paths')
def test_decision_crash_retry_when_exit_code_nonzero(mock_construct):
    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0", "timestamp": "t", "command": "crash",
        "prompt_hash": "p", "code_hash": "c", "example_hash": "e", "test_hash": "t"
    })
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 1, "tests_passed": 0, "tests_failed": 0, "coverage": 0.0
    })
    decision = sync_determine_operation(BASENAME, LANGUAGE, TARGET_COVERAGE)
    assert decision.operation == 'crash', f"Expected 'crash' when exit_code=1, got '{decision.operation}'"
    assert "retry crash fix" in decision.reason


@patch('sync_determine_operation.construct_paths')
def test_decision_fix_on_test_failures(mock_construct, pdd_test_environment):
    prompts_dir = pdd_test_environment / "prompts"
    prompts_dir.mkdir(exist_ok=True)
    prompt_hash = create_file(prompts_dir / f"{BASENAME}_{LANGUAGE}.prompt", "Test prompt")

    test_file = pdd_test_environment / f"test_{BASENAME}.py"
    create_file(test_file, "def test_x(): assert True\n")

    fp_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}.json"
    create_fingerprint_file(fp_path, {
        "pdd_version": "1.0", "timestamp": "t", "command": "test",
        "prompt_hash": prompt_hash, "code_hash": "c",
        "example_hash": "e", "test_hash": "t"
    })
    rr_path = get_meta_dir() / f"{BASENAME}_{LANGUAGE}_run.json"
    create_run_report_file(rr_path, {
        "timestamp": "t", "exit_code": 1, "tests_passed": 5,
        "tests_failed": 3, "coverage": 80.0
    })
    decision = sync_determine_operation(
        BASENAME, LANGUAGE, TARGET_COVERAGE, prompts_dir=str(prompts_dir)
    )
    assert decision.operation == 'fix'
    assert decision.details['tests_failed'] == 3