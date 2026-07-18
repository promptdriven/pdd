"""Focused invariants for issue #1926 fingerprint finalization."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest

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
