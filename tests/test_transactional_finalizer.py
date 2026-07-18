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
from click.testing import CliRunner

from pdd.fingerprint_transaction import FingerprintFinalizeError, finalize_fingerprint


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


@pytest.mark.parametrize("command_name", ("auto_deps", "update"))
def test_real_click_commands_do_not_convert_finalization_failure_to_success(
    tmp_path: Path, command_name: str,
) -> None:
    """Maintenance and modify Click boundaries preserve typed finalizer failure."""
    failure = FingerprintFinalizeError("test", tmp_path / "fingerprint.json", "disk full")
    runner = CliRunner()
    prompt = tmp_path / "sample_python.prompt"
    prompt.write_text("% Goal\nSample\n", encoding="utf-8")
    if command_name == "auto_deps":
        from pdd.commands.maintenance import auto_deps

        with patch("pdd.commands.maintenance.auto_deps_main", side_effect=failure):
            result = runner.invoke(auto_deps, [str(prompt), str(tmp_path)], obj={"quiet": True})
    else:
        from pdd.commands.modify import update

        code = tmp_path / "sample.py"
        code.write_text("VALUE = 1\n", encoding="utf-8")
        with patch("pdd.commands.modify.update_main", side_effect=failure):
            result = runner.invoke(update, [str(code)], obj={"quiet": True})

    assert result.exit_code != 0
    assert isinstance(result.exception, FingerprintFinalizeError)
    assert "Success" not in result.output
