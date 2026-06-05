from __future__ import annotations

from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.prompt_gate import (
    filter_changed_prompt_paths,
    load_prompt_gate_config,
    resolve_prompt_gate_mode,
    run_automatic_prompt_gate,
)


def test_filter_changed_prompt_paths() -> None:
    paths = filter_changed_prompt_paths(
        ["prompts/a_python.prompt", "pdd/foo.py", "prompts/b_LLM.prompt"]
    )
    assert [path.name for path in paths] == ["a_python.prompt"]


def test_resolve_prompt_gate_mode_cli_overrides_config(tmp_path: Path) -> None:
    pyproject = tmp_path / "pyproject.toml"
    pyproject.write_text(
        '[tool.pdd.checkup]\nprompt_gate = "off"\n',
        encoding="utf-8",
    )
    assert resolve_prompt_gate_mode(
        cli_prompt_checkup="strict",
        no_prompt_checkup=False,
        project_root=tmp_path,
    ) == "strict"


def test_resolve_prompt_gate_mode_no_prompt_checkup_wins(tmp_path: Path) -> None:
    assert resolve_prompt_gate_mode(
        cli_prompt_checkup="strict",
        no_prompt_checkup=True,
        project_root=tmp_path,
    ) == "off"


def test_load_prompt_gate_config_default_warn(tmp_path: Path) -> None:
    assert load_prompt_gate_config(tmp_path) == "warn"


def test_run_automatic_prompt_gate_off_is_noop(tmp_path: Path) -> None:
    prompt = tmp_path / "prompts" / "clean_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("% noop\n", encoding="utf-8")
    should_continue, exit_code = run_automatic_prompt_gate(
        [prompt],
        mode="off",
        project_root=tmp_path,
        quiet=True,
    )
    assert should_continue is True
    assert exit_code == 0


def test_run_automatic_prompt_gate_strict_blocks_on_failure(tmp_path: Path) -> None:
    fixtures = Path(__file__).resolve().parent / "fixtures" / "prompt_lint"
    prompt = fixtures / "vague_undefined.prompt"
    should_continue, exit_code = run_automatic_prompt_gate(
        [prompt],
        mode="strict",
        project_root=fixtures,
        quiet=True,
        strict=True,
    )
    assert should_continue is False
    assert exit_code == 2


def test_run_automatic_prompt_gate_warn_continues_on_failure(tmp_path: Path) -> None:
    fixtures = Path(__file__).resolve().parent / "fixtures" / "prompt_lint"
    prompt = fixtures / "vague_undefined.prompt"
    should_continue, exit_code = run_automatic_prompt_gate(
        [prompt],
        mode="warn",
        project_root=fixtures,
        quiet=True,
    )
    assert should_continue is True
    assert exit_code == 0
