from __future__ import annotations

from pathlib import Path

import pytest

from pdd.checkup_target import CheckupTargetKind, classify_checkup_target, is_prompt_shaped_target


def test_classify_prompt_file_target() -> None:
    assert classify_checkup_target("prompts/foo_python.prompt") == CheckupTargetKind.PROMPT_FILE


def test_classify_prompt_directory_target(tmp_path: Path) -> None:
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    assert classify_checkup_target("prompts", project_root=tmp_path) == CheckupTargetKind.PROMPT_DIRECTORY


def test_classify_devunit_target() -> None:
    assert classify_checkup_target("refund_payment") == CheckupTargetKind.DEVUNIT


def test_classify_github_issue_target() -> None:
    assert (
        classify_checkup_target("https://github.com/org/repo/issues/123")
        == CheckupTargetKind.GITHUB_ISSUE
    )


def test_is_prompt_shaped_target_for_devunit(tmp_path: Path) -> None:
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    (prompts_dir / "refund_payment_python.prompt").write_text("% test\n", encoding="utf-8")
    assert is_prompt_shaped_target("refund_payment", project_root=tmp_path) is True


def test_is_prompt_shaped_target_for_unresolved_devunit(tmp_path: Path) -> None:
    assert is_prompt_shaped_target("refund_payment", project_root=tmp_path) is False


def test_is_prompt_shaped_target_for_issue_url() -> None:
    assert is_prompt_shaped_target("https://github.com/org/repo/issues/123") is False
