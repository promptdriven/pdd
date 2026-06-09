from __future__ import annotations

from pathlib import Path
from unittest.mock import patch

import click
import pytest
import yaml

from pdd.prompt_gate import (
    _normalize_prompt_gate_mode,
    filter_changed_prompt_paths,
    load_prompt_gate_config,
    maybe_run_workflow_prompt_gate,
    parse_prompt_gate_block_exit,
    prompt_gate_block_message,
    resolve_prompt_gate_mode,
    resolve_prompt_gate_project_root,
    run_automatic_prompt_gate,
)


def test_prompt_gate_block_message_round_trip() -> None:
    message = prompt_gate_block_message(2)
    assert parse_prompt_gate_block_exit(message) == 2
    assert parse_prompt_gate_block_exit("unrelated message") is None


def test_resolve_prompt_gate_project_root_anchors_on_prompt(tmp_path: Path) -> None:
    # Nested repo: gate root must resolve to the prompt's own project (.git
    # marker), not the process working directory.
    project = tmp_path / "nested"
    (project / ".git").mkdir(parents=True)
    prompt = project / "prompts" / "foo_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("% test\n", encoding="utf-8")

    resolved = resolve_prompt_gate_project_root([prompt])
    assert resolved == project.resolve()


def test_resolve_prompt_gate_project_root_falls_back(tmp_path: Path) -> None:
    orphan = tmp_path / "no_markers" / "foo_python.prompt"
    orphan.parent.mkdir(parents=True)
    orphan.write_text("% test\n", encoding="utf-8")
    fallback = tmp_path / "fallback"
    fallback.mkdir()

    # No project marker above the prompt => use the provided fallback.
    resolved = resolve_prompt_gate_project_root([orphan], fallback=fallback)
    assert resolved == fallback.resolve()
    # Empty inputs also fall back without raising.
    assert resolve_prompt_gate_project_root([], fallback=fallback) == fallback.resolve()

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


def test_load_prompt_gate_config_prefers_pddrc_over_pyproject(tmp_path: Path) -> None:
    (tmp_path / ".pddrc").write_text(
        yaml.safe_dump(
            {
                "version": 1,
                "contexts": {"default": {"paths": {"prompts": "prompts"}}},
                "checkup": {"prompt_gate": "off"},
            }
        ),
        encoding="utf-8",
    )
    (tmp_path / "pyproject.toml").write_text(
        '[tool.pdd.checkup]\nprompt_gate = "strict"\n',
        encoding="utf-8",
    )
    assert load_prompt_gate_config(tmp_path) == "off"


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


def test_normalize_prompt_gate_mode_yaml_boolean_false_maps_to_off() -> None:
    # PyYAML parses unquoted `off`/`no`/`false` as boolean False; must resolve to "off".
    assert _normalize_prompt_gate_mode(False, source="<test>") == "off"


def test_normalize_prompt_gate_mode_yaml_boolean_true_returns_none_with_warning() -> None:
    # PyYAML parses unquoted `on`/`yes`/`true` as boolean True; no valid mode maps
    # to True, so the function must warn and return None (caller falls back to default).
    assert _normalize_prompt_gate_mode(True, source="<test>") is None


def test_normalize_prompt_gate_mode_integer_zero_not_treated_as_off() -> None:
    # TOML integer 0 must NOT be silently treated as "off" — only Python bool False is.
    assert _normalize_prompt_gate_mode(0, source="<test>") is None


def test_load_prompt_gate_config_unquoted_off_in_pddrc(tmp_path: Path) -> None:
    # Regression: `prompt_gate: off` without quotes is loaded by PyYAML as boolean
    # False; the config reader must still return "off", not fall back to "warn".
    pddrc_content = (
        "version: 1\n"
        "contexts:\n"
        "  default:\n"
        "    paths:\n"
        "      prompts: prompts\n"
        "checkup:\n"
        "  prompt_gate: off\n"
    )
    (tmp_path / ".pddrc").write_text(pddrc_content, encoding="utf-8")
    assert load_prompt_gate_config(tmp_path) == "off"


def test_interactive_gate_exit_is_caught_and_returns_failure(tmp_path: Path) -> None:
    """click.exceptions.Exit from run_interactive_checkup must be caught so pdd generate
    / pdd change do not disappear without a user-visible message (#1519 finding #2)."""
    prompt = tmp_path / "prompts" / "foo_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("% test\n", encoding="utf-8")

    with patch(
        "pdd.checkup_interactive_main.run_interactive_checkup",
        side_effect=click.exceptions.Exit(1),
    ) as _mock_ic, patch(
        "sys.stdin.isatty", return_value=True
    ), patch(
        "sys.stdout.isatty", return_value=True
    ):
        should_continue, exit_code = maybe_run_workflow_prompt_gate(
            [prompt],
            cli_prompt_checkup=None,
            no_prompt_checkup=False,
            project_root=tmp_path,
            interactive=True,
            quiet=True,
        )

    assert should_continue is False
    assert exit_code == 1


def test_interactive_gate_success_returns_continue(tmp_path: Path) -> None:
    """Successful interactive checkup must return (True, 0) — unchanged behavior."""
    prompt = tmp_path / "prompts" / "foo_python.prompt"
    prompt.parent.mkdir(parents=True)
    prompt.write_text("% test\n", encoding="utf-8")

    with patch(
        "pdd.checkup_interactive_main.run_interactive_checkup",
        return_value=("done", 0.0, "mock"),
    ), patch("sys.stdin.isatty", return_value=True), patch(
        "sys.stdout.isatty", return_value=True
    ):
        should_continue, exit_code = maybe_run_workflow_prompt_gate(
            [prompt],
            cli_prompt_checkup=None,
            no_prompt_checkup=False,
            project_root=tmp_path,
            interactive=True,
            quiet=True,
        )

    assert should_continue is True
    assert exit_code == 0
