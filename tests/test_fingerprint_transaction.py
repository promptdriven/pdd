"""Unit and regression tests for transactional fingerprint persistence."""

from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.fingerprint_transaction import (
    FingerprintFinalizeError,
    FingerprintTransaction,
)
from pdd.operation_log import get_fingerprint_path, save_fingerprint


def _project(tmp_path: Path, name: str = "project") -> tuple[Path, dict[str, Path]]:
    root = tmp_path / name
    (root / "prompts").mkdir(parents=True)
    (root / "src").mkdir()
    (root / "examples").mkdir()
    (root / "tests").mkdir()
    (root / ".pddrc").write_text("{}", encoding="utf-8")
    paths = {
        "prompt": root / "prompts" / "widget_python.prompt",
        "code": root / "src" / "widget.py",
        "example": root / "examples" / "widget_example.py",
        "test": root / "tests" / "test_widget.py",
    }
    for key, path in paths.items():
        path.write_text(f"{key} v1\n", encoding="utf-8")
    return root, paths


def test_transaction_writes_complete_atomic_fingerprint(tmp_path: Path) -> None:
    """A clean exit writes the full payload through a same-directory rename."""
    _root, paths = _project(tmp_path)
    destination = get_fingerprint_path("widget", "Python", paths=paths)

    real_replace = __import__("os").replace
    replace_calls: list[tuple[Path, Path]] = []

    def recording_replace(source, target):
        replace_calls.append((Path(source), Path(target)))
        real_replace(source, target)

    with patch("pdd.fingerprint_transaction.os.replace", side_effect=recording_replace):
        with FingerprintTransaction("widget", "Python", "generate", paths=paths):
            pass

    payload = json.loads(destination.read_text(encoding="utf-8"))
    assert payload["command"] == "generate"
    assert all(payload[f"{name}_hash"] for name in ("prompt", "code", "example", "test"))
    assert replace_calls
    temp_path, target_path = replace_calls[0]
    assert temp_path.parent == destination.parent
    assert target_path == destination


def test_null_prompt_hash_fails_without_overwriting_existing_state(tmp_path: Path) -> None:
    """Null prompt hashes fail without replacing known-good state (#1305)."""
    root, paths = _project(tmp_path)
    paths["prompt"].unlink()
    destination = root / ".pdd" / "meta" / "widget_python.json"
    destination.parent.mkdir(parents=True)
    destination.write_text('{"known": "good"}\n', encoding="utf-8")

    with pytest.raises(FingerprintFinalizeError, match="prompt_hash is null"):
        with FingerprintTransaction("widget", "python", "example", paths=paths):
            pass

    assert json.loads(destination.read_text(encoding="utf-8")) == {"known": "good"}
    assert not list(destination.parent.glob("*.tmp"))


def test_destination_is_resolved_once_before_cwd_changes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Changing cwd after entry cannot redirect the resolved metadata root."""
    root_a, paths_a = _project(tmp_path, "a")
    root_b, _paths_b = _project(tmp_path, "b")

    transaction = FingerprintTransaction("widget", "python", "update", paths=paths_a)
    monkeypatch.chdir(root_b)
    with transaction:
        pass

    assert (root_a / ".pdd" / "meta" / "widget_python.json").is_file()
    assert not (root_b / ".pdd" / "meta" / "widget_python.json").exists()


def test_body_exception_and_explicit_skip_do_not_write(tmp_path: Path) -> None:
    """Exceptions and intentional skips never write a fingerprint."""
    root, paths = _project(tmp_path)
    destination = root / ".pdd" / "meta" / "widget_python.json"

    with pytest.raises(RuntimeError, match="body failed"):
        with FingerprintTransaction("widget", "python", "fix", paths=paths):
            raise RuntimeError("body failed")
    assert not destination.exists()

    with FingerprintTransaction("widget", "python", "fix", paths=paths) as transaction:
        transaction.skip("dry-run mode")
    assert not destination.exists()


def test_replace_failure_is_explicit_and_leaves_no_partial_file(tmp_path: Path) -> None:
    """Rename failures include diagnostics and clean their temporary file."""
    root, paths = _project(tmp_path)
    destination = root / ".pdd" / "meta" / "widget_python.json"

    with patch("pdd.fingerprint_transaction.os.replace", side_effect=OSError("disk full")):
        with pytest.raises(FingerprintFinalizeError) as exc_info:
            with FingerprintTransaction("widget", "python", "auto-deps", paths=paths):
                pass

    message = str(exc_info.value)
    assert "[auto-deps]" in message
    assert str(destination) in message
    assert "disk full" in message
    assert not destination.exists()
    assert not list(destination.parent.glob("*.tmp"))


def test_save_fingerprint_is_a_thin_transaction_wrapper(tmp_path: Path) -> None:
    """The legacy public helper delegates without retaining write logic."""
    _root, paths = _project(tmp_path)

    with patch("pdd.fingerprint_transaction.FingerprintTransaction") as transaction_cls:
        save_fingerprint(
            "widget",
            "python",
            "generate",
            paths=paths,
            cost=1.25,
            model="model",
        )

    transaction_cls.assert_called_once_with(
        basename="widget",
        language="python",
        operation="generate",
        paths=paths,
        cost=1.25,
        model="model",
    )
    transaction_cls.return_value.__enter__.assert_called_once()
    transaction_cls.return_value.__exit__.assert_called_once()


def test_include_dependency_override_is_persisted(tmp_path: Path) -> None:
    """Pre-rewrite dependency snapshots survive prompt transformations."""
    root, paths = _project(tmp_path)
    dependency = root / "context.md"
    dependency.write_text("context", encoding="utf-8")
    override = {str(dependency): "captured-before-rewrite"}

    with FingerprintTransaction("widget", "python", "sync", paths=paths) as transaction:
        transaction.set_include_deps_override(override)

    destination = root / ".pdd" / "meta" / "widget_python.json"
    assert json.loads(destination.read_text(encoding="utf-8"))["include_deps"] == override
