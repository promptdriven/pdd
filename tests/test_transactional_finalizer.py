"""Focused invariants for issue #1926 fingerprint finalization."""
from __future__ import annotations

import json
from pathlib import Path
import os
import signal
import subprocess
import sys
import threading
from unittest.mock import patch

import pytest

from pdd.fingerprint_transaction import (
    AtomicStateUpdate,
    FingerprintFinalizeError,
    FingerprintTransaction,
    finalize_fingerprint,
    operation_invalidates_run_report,
)


def _paths(tmp_path: Path) -> tuple[dict[str, Path], Path]:
    root = tmp_path / "subproject"
    (root / "prompts").mkdir(parents=True)
    (root / "src").mkdir()
    (root / ".pddrc").write_text("contexts: {}\n", encoding="utf-8")
    prompt = root / "prompts" / "sample_python.prompt"
    code = root / "src" / "sample.py"
    prompt.write_text("% Goal\nSample\n", encoding="utf-8")
    code.write_text("VALUE = 1\n", encoding="utf-8")
    return {"prompt": prompt, "code": code}, root


def test_finalizer_is_atomic_and_preserves_previous_fingerprint_on_replace_failure(
    tmp_path: Path,
) -> None:
    paths, root = _paths(tmp_path)
    destination = root / ".pdd" / "meta" / "sample_python.json"
    destination.parent.mkdir(parents=True)
    destination.write_text('{"old": true}\n', encoding="utf-8")

    with patch("pdd.fingerprint_transaction.atomic_write_json", side_effect=OSError("full")):
        with pytest.raises(FingerprintFinalizeError, match="full"):
            finalize_fingerprint("sample", "python", "generate", paths)

    assert json.loads(destination.read_text(encoding="utf-8")) == {"old": True}


def test_symlinked_state_target_fails_closed_without_touching_outside_victim(
    tmp_path: Path,
) -> None:
    """A metadata link is never resolved into an outside state destination."""
    paths, root = _paths(tmp_path)
    meta = root / ".pdd" / "meta"
    meta.mkdir(parents=True)
    victim = root / ".pdd" / "outside" / "victim.json"
    victim.parent.mkdir()
    original = b"outside evidence must remain exact\n"
    victim.write_bytes(original)
    target = meta / "sample_python.json"
    target.symlink_to(victim)

    with pytest.raises(FingerprintFinalizeError, match="symlink"):
        finalize_fingerprint("sample", "python", "generate", paths)

    assert target.is_symlink()
    assert victim.read_bytes() == original


def test_replaced_state_target_fails_before_publish(tmp_path: Path) -> None:
    """A target replacement after backup is detected instead of overwritten."""
    meta = tmp_path / ".pdd" / "meta"
    meta.mkdir(parents=True)
    target = meta / "sample_python.json"
    target.write_text('{"old": true}\n', encoding="utf-8")
    state = AtomicStateUpdate("sample", "python")
    original_backup = state._backup_target

    def replace_after_backup(path: Path):
        result = original_backup(path)
        if path == target:
            path.unlink()
            path.write_text('{"replacement": true}\n', encoding="utf-8")
        return result

    state._backup_target = replace_after_backup
    with pytest.raises(FingerprintFinalizeError, match="replaced"):
        with state:
            state.set_fingerprint({"new": True}, target)

    assert json.loads(target.read_text(encoding="utf-8")) == {"replacement": True}


def test_same_root_wrong_module_code_is_rejected_without_discovery(tmp_path: Path) -> None:
    """No legacy-discovery result is not permission to hash another module."""
    paths, root = _paths(tmp_path)
    unrelated = root / "src" / "unrelated.py"
    unrelated.write_text("VALUE = 2\n", encoding="utf-8")
    with pytest.raises(FingerprintFinalizeError, match="wrong module identity"):
        finalize_fingerprint(
            "sample", "python", "generate", {"prompt": paths["prompt"], "code": unrelated}
        )


def test_aggregate_new_state_payload_limit_fails_before_publication(tmp_path: Path) -> None:
    """Two individually valid records cannot exceed the transaction budget."""
    meta = tmp_path / ".pdd" / "meta"
    meta.mkdir(parents=True)
    report = meta / "sample_python_run.json"
    fingerprint = meta / "sample_python.json"
    old_report, old_fingerprint = b'{"old": "report"}\n', b'{"old": "fingerprint"}\n'
    report.write_bytes(old_report)
    fingerprint.write_bytes(old_fingerprint)
    payload = {"payload": "x" * (5 * 1024 * 1024)}

    with pytest.raises(FingerprintFinalizeError, match="aggregate"):
        with AtomicStateUpdate("sample", "python") as state:
            state.set_run_report(payload, report)
            state.set_fingerprint(payload, fingerprint)

    assert report.read_bytes() == old_report
    assert fingerprint.read_bytes() == old_fingerprint


def test_paired_verify_policy_retains_authoritative_run_evidence(tmp_path: Path) -> None:
    """A paired fingerprint is not an implicit run-report tombstone."""
    paths, root = _paths(tmp_path)
    meta = root / ".pdd" / "meta"
    meta.mkdir(parents=True)
    report = meta / "sample_python_run.json"
    report.write_text('{"evidence": "keep"}\n', encoding="utf-8")

    with AtomicStateUpdate("sample", "python", directory=meta) as state:
        FingerprintTransaction("sample", "python", "verify", paths, atomic_state=state).commit()

    assert json.loads(report.read_text(encoding="utf-8")) == {"evidence": "keep"}
    assert not operation_invalidates_run_report("verify")
    assert operation_invalidates_run_report("generate")


def test_first_journal_failure_cleans_tombstone_artifacts_and_preserves_cause(
    tmp_path: Path,
) -> None:
    """A failed prepared-journal write does not mask disk-full or leak files."""
    meta = tmp_path / ".pdd" / "meta"
    meta.mkdir(parents=True)
    report = meta / "sample_python_run.json"
    fingerprint = meta / "sample_python.json"
    report.write_text('{"old": "report"}\n', encoding="utf-8")
    fingerprint.write_text('{"old": "fingerprint"}\n', encoding="utf-8")
    state = AtomicStateUpdate("sample", "python")
    state._write_journal = lambda *_args: (_ for _ in ()).throw(OSError("disk full"))

    with pytest.raises(FingerprintFinalizeError, match="disk full"):
        with state:
            state.remove_run_report(report)
            state.set_fingerprint({"new": True}, fingerprint)

    assert json.loads(report.read_text()) == {"old": "report"}
    assert json.loads(fingerprint.read_text()) == {"old": "fingerprint"}
    assert not list(meta.glob("*.state-new"))
    assert not list(meta.glob("*.state-old"))


def test_interrupted_publish_fsync_recovers_old_pair_and_cleans_owned_files(
    tmp_path: Path,
) -> None:
    """A directory-fsync interruption is nonzero and leaves no split state."""
    meta = tmp_path / ".pdd" / "meta"
    meta.mkdir(parents=True)
    report = meta / "sample_python_run.json"
    fingerprint = meta / "sample_python.json"
    old_report = b'{"old": "report"}\n'
    old_fingerprint = b'{"old": "fingerprint"}\n'
    report.write_bytes(old_report)
    fingerprint.write_bytes(old_fingerprint)

    with patch("pdd.fingerprint_transaction.fsync_directory", side_effect=OSError("fsync interrupted")):
        with pytest.raises(FingerprintFinalizeError, match="fsync interrupted"):
            with AtomicStateUpdate("sample", "python") as state:
                state.remove_run_report(report)
                state.set_fingerprint({"new": True}, fingerprint)

    assert report.read_bytes() == old_report
    assert fingerprint.read_bytes() == old_fingerprint
    assert not list(meta.glob("*.state-new"))
    assert not list(meta.glob("*.state-old"))


def test_recovery_for_second_unit_is_not_skipped_by_first_unit_lock(tmp_path: Path) -> None:
    """Thread-local re-entrancy is scoped to a unit, not its whole directory."""
    meta = tmp_path / ".pdd" / "meta"
    meta.mkdir(parents=True)
    report = meta / "second_python_run.json"
    report.write_text('{"old": true}\n', encoding="utf-8")
    second = AtomicStateUpdate("second", "python", directory=meta)
    journal = meta / f".{second._identity}.state-txn.json"
    digest = second._digest(report)
    journal.write_text(json.dumps({
        "version": 3,
        "identity": second._identity,
        "state": "prepared",
        "records": [{
            "role": "run_report", "target": str(report), "staged": None,
            "backup": None, "target_hash": digest, "staged_hash": None,
        }],
    }), encoding="utf-8")

    with AtomicStateUpdate("first", "python", directory=meta):
        AtomicStateUpdate.recover("second", "python", meta)

    assert not report.exists()
    assert not journal.exists()


def test_nested_same_unit_state_joins_outer_without_premature_commit(tmp_path: Path) -> None:
    """Nested metadata work shares the outer journal instead of taking flock twice."""
    meta = tmp_path / ".pdd" / "meta"
    target = meta / "sample_python.json"
    outer = AtomicStateUpdate("sample", "python", directory=meta)

    with outer:
        with AtomicStateUpdate("sample", "python", directory=meta) as nested:
            assert nested is outer
            nested.set_fingerprint({"state": "new"}, target)
        # Exiting the nested helper must not publish or release the outer lock.
        assert not target.exists()

    assert json.loads(target.read_text(encoding="utf-8")) == {"state": "new"}


@pytest.mark.parametrize(
    ("target", "error"),
    (
        ("pdd.json_atomic.json.dump", OSError("temp write failed")),
        ("pdd.json_atomic.os.replace", OSError("replace failed")),
    ),
)
def test_real_atomic_writer_preserves_previous_state_on_failure(
    tmp_path: Path, target: str, error: OSError,
) -> None:
    """Both temp-file writes and replacement fail without exposing partial JSON."""
    paths, root = _paths(tmp_path)
    destination = root / ".pdd" / "meta" / "sample_python.json"
    destination.parent.mkdir(parents=True)
    previous = b'{"old": "fingerprint"}\n'
    destination.write_bytes(previous)

    with patch(target, side_effect=error):
        with pytest.raises(FingerprintFinalizeError, match=str(error)):
            finalize_fingerprint("sample", "python", "generate", paths)

    assert destination.read_bytes() == previous
    assert not list(destination.parent.glob(".sample_python.json.*.tmp"))


def test_finalizer_rejects_null_hash_and_parent_cwd_uses_subproject_root(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    parent = tmp_path / "parent"
    parent.mkdir()
    paths, root = _paths(parent)
    monkeypatch.chdir(parent)

    finalize_fingerprint("sample", "python", "generate", paths)
    destination = root / ".pdd" / "meta" / "sample_python.json"
    assert destination.exists()
    assert not (parent / ".pdd" / "meta" / "sample_python.json").exists()

    paths["prompt"].unlink()
    previous = destination.read_bytes()
    with pytest.raises(FingerprintFinalizeError, match="prompt_hash is null"):
        finalize_fingerprint("sample", "python", "fix", paths)
    assert destination.read_bytes() == previous


def test_atomic_state_rolls_back_when_later_state_write_fails(tmp_path: Path) -> None:
    from pdd.sync_orchestration import AtomicStateUpdate

    meta = tmp_path / ".pdd" / "meta"
    meta.mkdir(parents=True)
    report = meta / "sample_python_run.json"
    fingerprint = meta / "sample_python.json"
    report.write_text('{"old": "report"}\n', encoding="utf-8")
    fingerprint.write_text('{"old": "fingerprint"}\n', encoding="utf-8")
    state = AtomicStateUpdate("sample", "python")
    original_write = state._atomic_write
    calls = 0

    def fail_second(data, path):
        nonlocal calls
        calls += 1
        if calls == 2:
            raise OSError("replace failed")
        original_write(data, path)

    state._atomic_write = fail_second
    with pytest.raises(FingerprintFinalizeError, match="atomic state commit failed"):
        with state:
            state.set_run_report({"new": "report"}, report)
            state.set_fingerprint({"new": "fingerprint"}, fingerprint)

    assert json.loads(report.read_text(encoding="utf-8")) == {"old": "report"}
    assert json.loads(fingerprint.read_text(encoding="utf-8")) == {"old": "fingerprint"}


def test_cleanup_after_durable_commit_is_success_not_a_repeat_signal(tmp_path: Path) -> None:
    """The committed journal state is the API commit point, not cleanup."""
    meta = tmp_path / ".pdd" / "meta"
    meta.mkdir(parents=True)
    report = meta / "sample_python_run.json"
    fingerprint = meta / "sample_python.json"
    state = AtomicStateUpdate("sample", "python")
    original_cleanup = state._cleanup_records
    calls = 0

    def fail_once(records):
        nonlocal calls
        calls += 1
        if calls == 1:
            raise OSError("cleanup unavailable")
        original_cleanup(records)

    state._cleanup_records = fail_once
    with state:
        state.set_run_report({"version": "new"}, report)
        state.set_fingerprint({"version": "new"}, fingerprint)

    assert json.loads(report.read_text()) == {"version": "new"}
    assert json.loads(fingerprint.read_text()) == {"version": "new"}
    assert calls == 2
    assert not list(meta.glob("*.state-txn.json"))


def test_paired_finalizer_locks_before_canonicalization_and_hashing(tmp_path: Path) -> None:
    """A paired sync finalizer cannot snapshot files before its outer lock."""
    paths, root = _paths(tmp_path)
    events: list[str] = []
    state = AtomicStateUpdate("sample", "python")
    original_lock = state._lock_and_recover

    def record_lock(directory: Path) -> None:
        events.append("lock")
        original_lock(directory)

    original_hashes = __import__(
        "pdd.fingerprint_transaction", fromlist=["calculate_current_hashes"]
    ).calculate_current_hashes

    def record_hashes(*args, **kwargs):
        events.append("hash")
        return original_hashes(*args, **kwargs)

    state._lock_and_recover = record_lock
    with patch("pdd.fingerprint_transaction.calculate_current_hashes", side_effect=record_hashes):
        with state:
            state.set_run_report({"version": "one"}, root / ".pdd" / "meta" / "sample_python_run.json")
            FingerprintTransaction(
                "sample", "python", "sync", paths, atomic_state=state
            ).commit()

    assert events.index("lock") < events.index("hash")


def test_outer_state_context_locks_before_operation_body(tmp_path: Path) -> None:
    """The sync/pin outer mutation scope owns the same unit lock."""
    meta = tmp_path / ".pdd" / "meta"
    events: list[str] = []
    state = AtomicStateUpdate("sample", "python", directory=meta)
    original_lock = state._lock_and_recover

    def record_lock(directory: Path) -> None:
        events.append("lock")
        original_lock(directory)

    state._lock_and_recover = record_lock
    with state:
        events.append("mutation")
    events.append("unlock")
    assert events == ["lock", "mutation", "unlock"]


def test_report_tombstone_recovers_after_crash_before_fingerprint_publish(tmp_path: Path) -> None:
    """A SIGKILL cannot permanently erase pre-existing run evidence."""
    paths, root = _paths(tmp_path)
    meta = root / ".pdd" / "meta"
    meta.mkdir(parents=True)
    report = meta / "sample_python_run.json"
    fingerprint = meta / "sample_python.json"
    report.write_bytes(b"not necessarily utf8: \xff")
    fingerprint.write_text(
        json.dumps({"pdd_version": "old", "timestamp": "old", "command": "old"}),
        encoding="utf-8",
    )
    script = """
import os
from pathlib import Path
from pdd.fingerprint_transaction import AtomicStateUpdate
meta = Path(os.environ['STATE_META'])
state = AtomicStateUpdate('sample', 'python', directory=meta)
write = state._write_journal
def stop(phase, records):
    write(phase, records)
    if phase == 'report_published': os.kill(os.getpid(), 9)
state._write_journal = stop
with state:
    state.remove_run_report(meta / 'sample_python_run.json')
    state.set_fingerprint({'pdd_version': 'new', 'timestamp': 'new', 'command': 'new'}, meta / 'sample_python.json')
"""
    result = subprocess.run(
        [sys.executable, "-c", script],
        env=dict(os.environ, STATE_META=str(meta), PYTHONPATH=str(Path.cwd())),
        check=False,
    )
    assert result.returncode == -signal.SIGKILL
    assert not report.exists()

    AtomicStateUpdate.recover("sample", "python", meta)
    assert report.read_bytes() == b"not necessarily utf8: \xff"
    assert json.loads(fingerprint.read_text())["command"] == "old"


def test_second_publish_failure_recovers_before_raising(tmp_path: Path) -> None:
    """A caller never receives a failure while the held lock exposes a split pair."""
    from pdd.fingerprint_transaction import AtomicStateUpdate

    meta = tmp_path / ".pdd" / "meta"
    meta.mkdir(parents=True)
    report = meta / "sample_python_run.json"
    fingerprint = meta / "sample_python.json"
    report.write_text('{"version": "old-report"}\n', encoding="utf-8")
    fingerprint.write_text('{"version": "old-fingerprint"}\n', encoding="utf-8")
    original_replace = os.replace
    failed = False

    def fail_fingerprint(source, target):
        nonlocal failed
        if Path(target) == fingerprint and not failed:
            failed = True
            raise OSError("forced second publish failure")
        return original_replace(source, target)

    with patch("pdd.fingerprint_transaction.os.replace", side_effect=fail_fingerprint):
        with pytest.raises(FingerprintFinalizeError, match="forced second publish failure"):
            with AtomicStateUpdate("sample", "python") as state:
                state.set_run_report({"version": "new-report"}, report)
                state.set_fingerprint({"version": "new-fingerprint"}, fingerprint)

    assert json.loads(report.read_text())["version"] == "old-report"
    assert json.loads(fingerprint.read_text())["version"] == "old-fingerprint"
    assert not list(meta.glob("*.state-txn.json"))


def test_recovery_rejects_tampered_target_without_touching_victim(tmp_path: Path) -> None:
    """Journal recovery treats metadata as untrusted and cannot escape its directory."""
    from pdd.fingerprint_transaction import AtomicStateUpdate

    meta = tmp_path / ".pdd" / "meta"
    meta.mkdir(parents=True)
    victim = tmp_path / "victim.txt"
    victim.write_text("SAFE", encoding="utf-8")
    journal = meta / f".{AtomicStateUpdate('sample', 'python')._identity}.state-txn.json"
    journal.write_text(json.dumps({
        "version": 2,
        "identity": AtomicStateUpdate("sample", "python")._identity,
        "state": "report_published",
        "records": [{"role": "fingerprint", "target": str(victim), "staged": str(meta / ".x.state-new"), "backup": None}],
    }), encoding="utf-8")
    with pytest.raises(FingerprintFinalizeError, match="escapes metadata"):
        AtomicStateUpdate.recover("sample", "python", meta)
    assert victim.read_text(encoding="utf-8") == "SAFE"


def test_explicit_null_hints_do_not_erase_discovered_artifacts(tmp_path: Path) -> None:
    """Optional null/empty thin-caller hints retain canonical example/test paths."""
    paths, root = _paths(tmp_path)
    example = root / "examples" / "sample_example.py"
    test = root / "tests" / "test_sample.py"
    example.parent.mkdir()
    test.parent.mkdir()
    example.write_text("VALUE = 1\n", encoding="utf-8")
    test.write_text("def test_value(): assert True\n", encoding="utf-8")
    complete = {**paths, "example": example, "test": test, "test_files": [test]}
    with patch("pdd.fingerprint_transaction.get_pdd_file_paths", return_value=complete):
        finalize_fingerprint("sample", "python", "fix", {**paths, "example": None, "test_files": None})
    payload = json.loads((root / ".pdd" / "meta" / "sample_python.json").read_text())
    assert payload["example_hash"] and payload["test_files"][test.name]


def test_explicit_artifact_outside_prompt_project_is_rejected(tmp_path: Path) -> None:
    """Real explicit paths cannot redirect hashing outside the owning project."""
    paths, _root = _paths(tmp_path)
    outside = tmp_path / "outside" / "sample_example.py"
    outside.parent.mkdir()
    outside.write_text("VALUE = 1\n", encoding="utf-8")
    with pytest.raises(FingerprintFinalizeError, match="escapes owning project root"):
        finalize_fingerprint("sample", "python", "fix", {**paths, "example": outside})


def test_restart_recovers_after_process_death_between_state_publications(tmp_path: Path) -> None:
    """A durable journal restores the old pair after a real SIGKILL transition."""
    meta = tmp_path / ".pdd" / "meta"
    meta.mkdir(parents=True)
    report = meta / "sample_python_run.json"
    fingerprint = meta / "sample_python.json"
    report.write_text('{"version": "old-report"}\n', encoding="utf-8")
    fingerprint.write_text('{"version": "old-fingerprint"}\n', encoding="utf-8")
    script = """
import os
from pathlib import Path
from pdd.fingerprint_transaction import AtomicStateUpdate
meta = Path(os.environ['STATE_META'])
state = AtomicStateUpdate('sample', 'python')
original = state._write_journal
def kill_after_report(phase, records):
    original(phase, records)
    if phase == 'report_published':
        os.kill(os.getpid(), 9)
state._write_journal = kill_after_report
with state:
    state.set_run_report({'version': 'new-report'}, meta / 'sample_python_run.json')
    state.set_fingerprint({'version': 'new-fingerprint'}, meta / 'sample_python.json')
"""
    environment = dict(os.environ, STATE_META=str(meta), PYTHONPATH=str(Path.cwd()))
    result = subprocess.run([sys.executable, "-c", script], env=environment, check=False)
    assert result.returncode == -signal.SIGKILL
    assert json.loads(report.read_text(encoding="utf-8"))["version"] == "new-report"
    assert json.loads(fingerprint.read_text(encoding="utf-8"))["version"] == "old-fingerprint"

    from pdd.fingerprint_transaction import AtomicStateUpdate

    AtomicStateUpdate.recover("sample", "python", meta)
    assert json.loads(report.read_text(encoding="utf-8"))["version"] == "old-report"
    assert json.loads(fingerprint.read_text(encoding="utf-8"))["version"] == "old-fingerprint"
    assert not list(meta.glob("*.state-txn.json"))


def test_fresh_authoritative_reader_recovers_killed_pair(tmp_path: Path) -> None:
    """A new process repairs the journal through read_fingerprint, not a test hook."""
    paths, root = _paths(tmp_path)
    meta = root / ".pdd" / "meta"
    meta.mkdir(parents=True)
    report = meta / "sample_python_run.json"
    fingerprint = meta / "sample_python.json"
    report.write_text(
        json.dumps({"timestamp": "old", "exit_code": 0, "tests_passed": 1,
                    "tests_failed": 0, "coverage": 1.0}), encoding="utf-8"
    )
    fingerprint.write_text(
        json.dumps({"pdd_version": "old", "timestamp": "old", "command": "old"}),
        encoding="utf-8",
    )
    writer = """
import os
from pathlib import Path
from pdd.fingerprint_transaction import AtomicStateUpdate
meta = Path(os.environ['STATE_META'])
state = AtomicStateUpdate('sample', 'python')
write_journal = state._write_journal
def stop_after_first_publish(phase, records):
    write_journal(phase, records)
    if phase == 'report_published':
        os.kill(os.getpid(), 9)
state._write_journal = stop_after_first_publish
with state:
    state.set_run_report({'timestamp': 'new', 'exit_code': 0, 'tests_passed': 2, 'tests_failed': 0, 'coverage': 1.0}, meta / 'sample_python_run.json')
    state.set_fingerprint({'pdd_version': 'new', 'timestamp': 'new', 'command': 'new'}, meta / 'sample_python.json')
"""
    environment = dict(os.environ, STATE_META=str(meta), PYTHONPATH=str(Path.cwd()))
    result = subprocess.run([sys.executable, "-c", writer], env=environment, check=False)
    assert result.returncode == -signal.SIGKILL

    reader = """
import os
from pathlib import Path
from pdd.sync_determine_operation import read_fingerprint, read_run_report
prompt = Path(os.environ['STATE_PROMPT'])
paths = {'prompt': prompt}
fingerprint = read_fingerprint('sample', 'python', paths=paths)
report = read_run_report('sample', 'python', paths=paths)
assert fingerprint is not None and fingerprint.command == 'old'
assert report is not None and report.tests_passed == 1
"""
    result = subprocess.run(
        [sys.executable, "-c", reader],
        env=dict(environment, STATE_PROMPT=str(paths["prompt"])),
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr
    assert not list(meta.glob("*.state-txn.json"))


def test_concurrent_state_finalizers_publish_only_complete_pairs(tmp_path: Path) -> None:
    """The metadata lock serializes concurrent writers and leaves no split pair."""
    from pdd.fingerprint_transaction import AtomicStateUpdate

    meta = tmp_path / ".pdd" / "meta"
    meta.mkdir(parents=True)
    report = meta / "sample_python_run.json"
    fingerprint = meta / "sample_python.json"
    barrier = threading.Barrier(2)
    failures: list[BaseException] = []

    def publish(version: int) -> None:
        try:
            barrier.wait()
            with AtomicStateUpdate("sample", "python") as state:
                state.set_run_report({"version": version}, report)
                state.set_fingerprint({"version": version}, fingerprint)
        except BaseException as exc:  # Assert thread failures in the parent.
            failures.append(exc)

    threads = [threading.Thread(target=publish, args=(version,)) for version in (1, 2)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()

    assert not failures
    assert json.loads(report.read_text(encoding="utf-8"))["version"] == json.loads(
        fingerprint.read_text(encoding="utf-8")
    )["version"]


def test_finalizer_completes_thin_metadata_paths_before_hashing(tmp_path: Path) -> None:
    """Prompt/code callers cannot omit existing example and test hashes."""
    paths, root = _paths(tmp_path)
    example = root / "examples" / "sample_example.py"
    test = root / "tests" / "test_sample.py"
    example.parent.mkdir()
    test.parent.mkdir()
    example.write_text("VALUE = 1\n", encoding="utf-8")
    test.write_text("def test_value(): assert True\n", encoding="utf-8")
    complete = {**paths, "example": example, "test": test, "test_files": [test]}

    with patch("pdd.fingerprint_transaction.get_pdd_file_paths", return_value=complete):
        finalize_fingerprint("sample", "python", "fix", paths)

    payload = json.loads((root / ".pdd" / "meta" / "sample_python.json").read_text())
    assert payload["example_hash"]
    assert payload["test_hash"]
    assert payload["test_files"][test.name]
