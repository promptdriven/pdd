"""Regression coverage for transactional fingerprint finalization (#1926)."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.fingerprint_transaction import (
    FingerprintFinalizeError,
    FingerprintTransaction,
)
from pdd.operation_log import save_fingerprint
from pdd.sync_determine_operation import calculate_current_hashes


def _unit(tmp_path: Path) -> tuple[dict[str, Path], Path]:
    root = tmp_path / "project"
    (root / "prompts").mkdir(parents=True)
    (root / "pdd").mkdir()
    (root / "tests").mkdir()
    (root / ".pdd" / "meta").mkdir(parents=True)
    (root / ".pddrc").write_text("contexts: {}\n", encoding="utf-8")
    paths = {
        "prompt": root / "prompts" / "sample_python.prompt",
        "code": root / "pdd" / "sample.py",
        "test": root / "tests" / "test_sample.py",
    }
    paths["prompt"].write_text("% Goal\nCreate sample.\n", encoding="utf-8")
    paths["code"].write_text("def sample():\n    return 1\n", encoding="utf-8")
    paths["test"].write_text("def test_sample():\n    assert True\n", encoding="utf-8")
    return paths, root


def test_clean_exit_writes_complete_fingerprint(tmp_path: Path) -> None:
    paths, root = _unit(tmp_path)

    with FingerprintTransaction("sample", "python", "generate", paths):
        pass

    fingerprint_path = root / ".pdd" / "meta" / "sample_python.json"
    data = json.loads(fingerprint_path.read_text(encoding="utf-8"))
    expected = calculate_current_hashes(paths)
    assert data["command"] == "generate"
    assert data["prompt_hash"] == expected["prompt_hash"]
    assert data["code_hash"] == expected["code_hash"]
    assert data["test_hash"] == expected["test_hash"]
    assert data["prompt_hash"] is not None


def test_body_exception_preserves_existing_fingerprint(tmp_path: Path) -> None:
    paths, root = _unit(tmp_path)
    fingerprint_path = root / ".pdd" / "meta" / "sample_python.json"
    fingerprint_path.write_text('{"sentinel": true}\n', encoding="utf-8")

    with pytest.raises(ValueError, match="body failed"):
        with FingerprintTransaction("sample", "python", "generate", paths):
            raise ValueError("body failed")

    assert json.loads(fingerprint_path.read_text(encoding="utf-8")) == {
        "sentinel": True
    }


def test_skip_is_idempotent_and_does_not_write(tmp_path: Path) -> None:
    paths, root = _unit(tmp_path)
    transaction = FingerprintTransaction("sample", "python", "update", paths)

    with transaction:
        transaction.skip("dry-run")
        transaction.skip("dry-run")

    assert not (root / ".pdd" / "meta" / "sample_python.json").exists()


def test_null_prompt_hash_is_hard_failure_and_preserves_previous_file(
    tmp_path: Path,
) -> None:
    paths, root = _unit(tmp_path)
    paths["prompt"].unlink()
    fingerprint_path = root / ".pdd" / "meta" / "sample_python.json"
    fingerprint_path.write_text('{"old": "state"}\n', encoding="utf-8")

    with pytest.raises(FingerprintFinalizeError) as raised:
        with FingerprintTransaction("sample", "python", "fix", paths):
            pass

    message = str(raised.value)
    assert "[fix]" in message
    assert str(fingerprint_path) in message
    assert "prompt_hash is null" in message
    assert json.loads(fingerprint_path.read_text(encoding="utf-8")) == {
        "old": "state"
    }


def test_existing_non_prompt_artifact_cannot_have_null_hash(
    tmp_path: Path,
) -> None:
    paths, _root = _unit(tmp_path)
    hashes = calculate_current_hashes(paths)
    hashes["code_hash"] = None

    with patch(
        "pdd.fingerprint_transaction.calculate_current_hashes",
        return_value=hashes,
    ):
        with pytest.raises(FingerprintFinalizeError, match="code_hash is null"):
            with FingerprintTransaction("sample", "python", "generate", paths):
                pass


def test_atomic_write_failure_has_context_and_leaves_destination_intact(
    tmp_path: Path,
) -> None:
    paths, root = _unit(tmp_path)
    fingerprint_path = root / ".pdd" / "meta" / "sample_python.json"
    fingerprint_path.write_text('{"old": true}\n', encoding="utf-8")

    with patch(
        "pdd.fingerprint_transaction.atomic_write_json",
        side_effect=OSError("disk full"),
    ):
        with pytest.raises(FingerprintFinalizeError) as raised:
            with FingerprintTransaction("sample", "python", "example", paths):
                pass

    assert "[example]" in str(raised.value)
    assert str(fingerprint_path) in str(raised.value)
    assert "disk full" in str(raised.value)
    assert json.loads(fingerprint_path.read_text(encoding="utf-8")) == {
        "old": True
    }


def test_explicit_paths_eagerly_anchor_nested_subproject(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    parent = tmp_path / "parent"
    nested = parent / "nested"
    (nested / "prompts").mkdir(parents=True)
    (nested / "src").mkdir()
    (nested / ".pddrc").write_text("contexts: {}\n", encoding="utf-8")
    prompt = nested / "prompts" / "sample_python.prompt"
    code = nested / "src" / "sample.py"
    prompt.write_text("% Goal\nNested.\n", encoding="utf-8")
    code.write_text("VALUE = 1\n", encoding="utf-8")
    monkeypatch.chdir(parent)

    transaction = FingerprintTransaction(
        "sample",
        "python",
        "update",
        {"prompt": prompt, "code": code},
    )
    assert transaction.fingerprint_path == (
        nested / ".pdd" / "meta" / "sample_python.json"
    )
    with transaction:
        pass

    assert transaction.fingerprint_path.exists()
    assert not (parent / ".pdd" / "meta" / "sample_python.json").exists()


def test_include_override_controls_hash_and_persisted_graph(tmp_path: Path) -> None:
    paths, root = _unit(tmp_path)
    dependency = root / "schema.md"
    dependency.write_text("contract-v1\n", encoding="utf-8")
    override = {str(dependency): "pre-captured-hash"}
    expected = calculate_current_hashes(paths, stored_include_deps=override)

    transaction = FingerprintTransaction(
        "sample",
        "python",
        "auto-deps",
        paths,
    )
    transaction.set_include_deps_override(override)
    with transaction:
        pass

    data = json.loads(
        (root / ".pdd" / "meta" / "sample_python.json").read_text(
            encoding="utf-8"
        )
    )
    assert data["prompt_hash"] == expected["prompt_hash"]
    assert data["include_deps"] == override


def test_atomic_state_uses_same_payload_builder_without_early_write(
    tmp_path: Path,
) -> None:
    paths, root = _unit(tmp_path)

    class Buffer:
        payload = None
        path = None
        operation = None

        def set_fingerprint(self, payload, path, *, operation=None):
            self.payload = payload
            self.path = path
            self.operation = operation

    buffer = Buffer()
    with FingerprintTransaction(
        "sample",
        "python",
        "test",
        paths,
        atomic_state=buffer,
    ):
        pass

    destination = root / ".pdd" / "meta" / "sample_python.json"
    assert not destination.exists()
    assert buffer.path == destination
    assert buffer.operation == "test"
    assert buffer.payload["prompt_hash"] is not None


def test_outer_atomic_state_rolls_back_fingerprint_if_run_report_commit_fails(
    tmp_path: Path,
) -> None:
    """The buffered sync path must not expose half of its state pair."""
    from pdd.sync_orchestration import AtomicStateUpdate

    meta = tmp_path / ".pdd" / "meta"
    meta.mkdir(parents=True)
    fingerprint_path = meta / "sample_python.json"
    run_report_path = meta / "sample_python_run.json"
    old_fingerprint = b'{"old": "fingerprint"}\n'
    old_run_report = b'{"old": "run-report"}\n'
    fingerprint_path.write_bytes(old_fingerprint)
    run_report_path.write_bytes(old_run_report)

    state = AtomicStateUpdate("sample", "python")
    real_atomic_write = state._atomic_write
    write_count = 0

    def fail_second_write(data, target_path):
        nonlocal write_count
        write_count += 1
        if write_count == 2:
            raise OSError("run-report disk failure")
        real_atomic_write(data, target_path)

    state._atomic_write = fail_second_write
    with pytest.raises(FingerprintFinalizeError, match="atomic state commit failed"):
        with state:
            state.set_fingerprint(
                {"prompt_hash": "new"},
                fingerprint_path,
                operation="test",
            )
            state.set_run_report({"exit_code": 0}, run_report_path)

    assert fingerprint_path.read_bytes() == old_fingerprint
    assert run_report_path.read_bytes() == old_run_report


def test_public_save_wrapper_propagates_transaction_failure(tmp_path: Path) -> None:
    paths, _root = _unit(tmp_path)
    paths["prompt"].unlink()

    with pytest.raises(FingerprintFinalizeError, match="prompt_hash is null"):
        save_fingerprint("sample", "python", "generate", paths=paths)


def test_path_normalization_handles_strings_and_null_test_list(
    tmp_path: Path,
) -> None:
    paths, root = _unit(tmp_path)

    with FingerprintTransaction(
        "sample",
        "python",
        "generate",
        paths={"prompt": str(paths["prompt"]), "test_files": None},
    ):
        pass

    payload = json.loads(
        (root / ".pdd" / "meta" / "sample_python.json").read_text(
            encoding="utf-8"
        )
    )
    assert payload["prompt_hash"] is not None
    assert payload["test_files"] == {}


def test_implicit_path_discovery_and_failure_are_typed(tmp_path: Path) -> None:
    paths, _root = _unit(tmp_path)
    with patch(
        "pdd.fingerprint_transaction.get_pdd_file_paths",
        return_value=paths,
    ) as discover:
        with FingerprintTransaction("sample", "python", "generate"):
            pass
    discover.assert_called_once_with("sample", "python")

    with patch(
        "pdd.fingerprint_transaction.get_pdd_file_paths",
        side_effect=OSError("cannot discover project"),
    ):
        with pytest.raises(
            FingerprintFinalizeError,
            match="path resolution failed: cannot discover project",
        ) as raised:
            FingerprintTransaction("nested/sample", "python", "generate")
    assert raised.value.fingerprint_path == Path(
        ".pdd/meta/nested_sample_python.json"
    )


def test_existing_test_file_requires_test_files_hash(tmp_path: Path) -> None:
    paths, _root = _unit(tmp_path)
    paths["test_files"] = [paths["test"]]
    hashes = calculate_current_hashes(paths)
    hashes["test_files"] = {}

    with patch(
        "pdd.fingerprint_transaction.calculate_current_hashes",
        return_value=hashes,
    ):
        with pytest.raises(
            FingerprintFinalizeError,
            match="test_files hash is null",
        ):
            with FingerprintTransaction("sample", "python", "test", paths):
                pass


def test_atomic_state_requires_fingerprint_setter(tmp_path: Path) -> None:
    paths, _root = _unit(tmp_path)

    with pytest.raises(
        FingerprintFinalizeError,
        match="atomic_state does not provide set_fingerprint",
    ):
        with FingerprintTransaction(
            "sample",
            "python",
            "sync",
            paths,
            atomic_state=object(),
        ):
            pass


def test_fingerprint_payload_has_one_authoritative_constructor() -> None:
    """Future mutating paths must delegate instead of reimplementing writes."""
    package_root = Path(__file__).parents[1] / "pdd"
    constructor_owners = []
    serialized_write_owners = []
    for path in package_root.rglob("*.py"):
        source = path.read_text(encoding="utf-8")
        if "Fingerprint(" in source:
            constructor_owners.append(path.relative_to(package_root).as_posix())
        if "json.dump(asdict(fingerprint)" in source:
            serialized_write_owners.append(path.relative_to(package_root).as_posix())

    # read_fingerprint reconstructs the persisted dataclass; only the
    # transaction is allowed to construct a new write payload.
    assert sorted(constructor_owners) == [
        "fingerprint_transaction.py",
        "sync_determine_operation.py",
    ]
    assert serialized_write_owners == []
