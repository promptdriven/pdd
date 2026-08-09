from __future__ import annotations

from pathlib import Path

import pytest

from pdd.source_set_model import resolve_devunit_prompts, resolve_prompt_targets


def test_resolve_prompt_file_target(tmp_path: Path) -> None:
    prompt = tmp_path / "prompts" / "refund_payment_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("% clean prompt\n", encoding="utf-8")

    resolved = resolve_prompt_targets(str(prompt), project_root=tmp_path)
    assert resolved == [prompt.resolve()]


def test_resolve_prompt_directory_target(tmp_path: Path) -> None:
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    first = prompts_dir / "alpha_python.prompt"
    second = prompts_dir / "beta_python.prompt"
    skipped = prompts_dir / "beta_LLM.prompt"
    first.write_text("% one\n", encoding="utf-8")
    second.write_text("% two\n", encoding="utf-8")
    skipped.write_text("% skip\n", encoding="utf-8")

    resolved = resolve_prompt_targets(str(prompts_dir), project_root=tmp_path)
    assert resolved == [first.resolve(), second.resolve()]


def test_resolve_devunit_glob(tmp_path: Path) -> None:
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt = prompts_dir / "refund_payment_python.prompt"
    prompt.write_text("% devunit\n", encoding="utf-8")

    resolved = resolve_devunit_prompts("refund_payment", tmp_path)
    assert resolved == [prompt.resolve()]


def test_resolve_devunit_missing_raises(tmp_path: Path) -> None:
    with pytest.raises(Exception, match="Could not resolve devunit"):
        resolve_devunit_prompts("missing_devunit", tmp_path)
