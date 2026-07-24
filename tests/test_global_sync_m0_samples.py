"""Contract tests for the read-only global-sync M0 sample harness."""
# pylint: disable=missing-function-docstring,protected-access

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import subprocess

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "verify_global_sync_m0_samples.py"


def _module():
    spec = importlib.util.spec_from_file_location("m0_samples", SCRIPT)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_m0_samples_rejects_zero_requested_closure() -> None:
    with pytest.raises(ValueError, match="closure limit"):
        _module().validate_arguments(closure_limit=0, sample_paths=("p.prompt",))


def test_m0_samples_rejects_empty_sample_set() -> None:
    with pytest.raises(ValueError, match="at least one sample"):
        _module().validate_arguments(closure_limit=1, sample_paths=())


def test_m0_samples_deterministic_payload_excludes_metrics() -> None:
    module = _module()
    payload = module.deterministic_payload(
        base_sha="a" * 40,
        partition={"derivable": 1},
        cases=[{"id": "01", "patch_sha256": "b" * 64, "outcome": "accepted"}],
        closure={"requested": 1, "completed": 1, "invalid": []},
    )
    assert "metrics" not in payload
    assert json.loads(json.dumps(payload, sort_keys=True)) == payload


def test_m0_samples_requires_all_named_inputs(tmp_path: Path) -> None:
    module = _module()
    (tmp_path / "pdd/prompts").mkdir(parents=True)
    (tmp_path / "pdd/prompts/one_python.prompt").write_text("x\n", encoding="utf-8")
    with pytest.raises(ValueError, match="required sample paths are absent"):
        module.require_sample_paths(
            tmp_path,
            ("pdd/prompts/one_python.prompt", "pdd/prompts/two_python.prompt"),
        )


def test_m0_samples_rejects_an_invalid_patch_false_pass() -> None:
    with pytest.raises(ValueError, match="bypassed profile validation"):
        _module().require_profile_rejection("01-profile", ())


def _git(root: Path, *arguments: str) -> None:
    subprocess.run(
        ["git", *arguments], cwd=root, check=True, capture_output=True, text=True
    )


def test_m0_samples_patch_captures_untracked_text_and_binary_in_clone(
    tmp_path: Path,
) -> None:
    source = tmp_path / "source"
    source.mkdir()
    _git(source, "init", "--quiet")
    _git(source, "config", "user.name", "test")
    _git(source, "config", "user.email", "test@example.invalid")
    (source / "tracked.txt").write_text("base\n", encoding="utf-8")
    _git(source, "add", "tracked.txt")
    _git(source, "commit", "--quiet", "-m", "base")

    candidate = tmp_path / "candidate"
    _git(tmp_path, "clone", "--quiet", str(source), str(candidate))
    (candidate / "candidate.txt").write_text("untracked text\n", encoding="utf-8")
    (candidate / "candidate.bin").write_bytes(b"\x00\x01untracked binary\xff")

    patch = _module()._patch_bytes(candidate)

    assert b"candidate.txt" in patch
    assert b"untracked text" in patch
    assert b"candidate.bin" in patch
    assert b"GIT binary patch" in patch
    assert _git_status(source) == ""


def _git_status(root: Path) -> str:
    result = subprocess.run(
        ["git", "status", "--porcelain"],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout
