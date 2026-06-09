"""Tests for deterministic interactive prompt patch apply (#1437)."""

from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.checkup_interactive_session import ApprovedPatch
from pdd.checkup_prompt_apply import (
    _validate_patch,
    apply_approved_patches,
)


def _patch(
    *,
    kind: str = "vocab_definition",
    target: str = "prompts/test_python.prompt",
    finding_id: str = "lint:test:1:VAGUE",
    replacement: str = "- Defined term: explicit meaning.",
    line: int = 1,
) -> ApprovedPatch:
    return ApprovedPatch(
        kind=kind,
        target=Path(target),
        anchor={"finding_id": finding_id, "line": line},
        replacement=replacement,
        finding_id=finding_id,
    )


def _write_prompt(repo: Path, rel: str = "prompts/test_python.prompt", content: str = "line one\n") -> Path:
    path = repo / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return path


def test_validate_patch_accepts_prompt_and_story(tmp_path: Path) -> None:
    prompt = _write_prompt(tmp_path)
    story = tmp_path / "user_stories" / "story__refund.md"
    story.parent.mkdir(parents=True)
    story.write_text("# Story\n", encoding="utf-8")

    _validate_patch(_patch(target="prompts/test_python.prompt"), tmp_path)
    _validate_patch(
        _patch(kind="story_template", target="user_stories/story__refund.md"),
        tmp_path,
    )
    assert prompt.is_file()
    assert story.is_file()


@pytest.mark.parametrize(
    ("target", "kind", "message"),
    [
        ("../../../etc/passwd", "vocab_definition", "escapes"),
        ("tests/test_x.prompt", "vocab_definition", "not writable"),
        ("prompts/secret_LLM.prompt", "vocab_definition", "_LLM.prompt"),
        ("README.md", "vocab_definition", "must be"),
        ("prompts/test_python.prompt", "repair_candidate", "allowlisted"),
    ],
)
def test_validate_patch_rejects_invalid_targets(
    tmp_path: Path,
    target: str,
    kind: str,
    message: str,
) -> None:
    if target.endswith(".prompt"):
        _write_prompt(tmp_path, target)
    elif target == "README.md":
        (tmp_path / "README.md").write_text("docs\n", encoding="utf-8")

    with pytest.raises(ValueError, match=message):
        _validate_patch(_patch(kind=kind, target=target), tmp_path)


def test_dry_run_writes_no_bytes_and_still_logs(tmp_path: Path) -> None:
    prompt = _write_prompt(tmp_path, content="original\n")
    original = prompt.read_text(encoding="utf-8")

    result = apply_approved_patches(
        [_patch()],
        repo_root=tmp_path,
        original_target=str(prompt),
        dry_run=True,
        choices_by_finding={"lint:test:1:VAGUE": 1},
    )

    assert prompt.read_text(encoding="utf-8") == original
    assert result.log_path is not None
    assert result.log_path.is_file()
    payload = json.loads(result.log_path.read_text(encoding="utf-8"))
    assert payload["dry_run"] is True
    assert payload["findings"][0]["status"] == "accepted"
    assert not list((tmp_path / ".pdd" / "evidence" / "checkups" / "backups").glob("**/*"))


def test_apply_creates_backup_and_mutates_prompt(tmp_path: Path) -> None:
    prompt = _write_prompt(tmp_path, content="before\n")

    with patch("pdd.checkup_prompt_apply.run_checkup_prompt", return_value=(True, "ok", 0.0, "", 0)):
        result = apply_approved_patches(
            [_patch(replacement="- Defined term: explicit meaning.\n")],
            repo_root=tmp_path,
            original_target=str(prompt),
            choices_by_finding={"lint:test:1:VAGUE": 1},
        )

    assert result.backup_root is not None
    backup_file = result.backup_root / "prompts" / "test_python.prompt"
    assert backup_file.read_text(encoding="utf-8") == "before\n"
    assert "- Defined term" in prompt.read_text(encoding="utf-8")
    assert result.log_path is not None
    assert result.postflight_status == "pass"


def test_apply_rejects_invalid_patch_kind_in_log(tmp_path: Path) -> None:
    prompt = _write_prompt(tmp_path, content="unchanged\n")
    bad = _patch(kind="repair_candidate")

    result = apply_approved_patches(
        [bad],
        repo_root=tmp_path,
        original_target=str(prompt),
        choices_by_finding={"lint:test:1:VAGUE": 1},
    )

    assert result.findings[0].status == "rejected"
    assert prompt.read_text(encoding="utf-8") == "unchanged\n"
    assert result.backup_root is None


def test_postflight_failure_propagates_exit_code(tmp_path: Path) -> None:
    prompt = _write_prompt(tmp_path)

    with patch(
        "pdd.checkup_prompt_apply.run_checkup_prompt",
        return_value=(False, "fail", 0.0, "", 2),
    ):
        result = apply_approved_patches(
            [_patch()],
            repo_root=tmp_path,
            original_target=str(prompt),
            choices_by_finding={"lint:test:1:VAGUE": 1},
        )

    assert result.postflight_status == "fail"
    assert result.exit_code == 2


def test_append_covers_appends_to_file_end(tmp_path: Path) -> None:
    prompt = _write_prompt(tmp_path, content="header\n")

    with patch("pdd.checkup_prompt_apply.run_checkup_prompt", return_value=(True, "ok", 0.0, "", 0)):
        apply_approved_patches(
            [_patch(kind="append_covers", replacement="covers: extra")],
            repo_root=tmp_path,
            original_target=str(prompt),
            choices_by_finding={"lint:test:1:VAGUE": 2},
        )

    assert prompt.read_text(encoding="utf-8").endswith("covers: extra\n")
