"""Integration tests for automatic prompt gate workflows (#1420)."""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest
import yaml
from click.testing import CliRunner

from pdd.change_main import change_main
from pdd.commands.checkup import checkup
from pdd.commands.generate import generate
from pdd.commands.modify import change
from pdd.prompt_gate import (
    filter_changed_prompt_paths,
    load_prompt_gate_config,
    maybe_run_workflow_prompt_gate,
)

REPO_ROOT = Path(__file__).resolve().parents[1]
FIXTURES = REPO_ROOT / "tests" / "fixtures" / "prompt_lint"
VAGUE_FIXTURE = FIXTURES / "vague_undefined.prompt"
CLEAN_FIXTURE = FIXTURES / "clean.prompt"


def _cli_env() -> dict[str, str]:
    env = os.environ.copy()
    env.update(
        {
            "PDD_PATH": str(REPO_ROOT / "pdd"),
            "PYTHONPATH": str(REPO_ROOT),
            "PDD_AUTO_UPDATE": "false",
        }
    )
    return env


def test_filter_changed_prompt_paths_ignores_non_prompt_files() -> None:
    paths = filter_changed_prompt_paths(["pdd/foo.py", "prompts/a_python.prompt"])
    assert [path.name for path in paths] == ["a_python.prompt"]


def test_load_prompt_gate_config_from_pddrc(tmp_path: Path) -> None:
    pddrc = tmp_path / ".pddrc"
    pddrc.write_text(
        yaml.safe_dump(
            {
                "version": 1,
                "contexts": {"default": {"paths": {"prompts": "prompts"}}},
                "checkup": {"prompt_gate": "off"},
            }
        ),
        encoding="utf-8",
    )
    assert load_prompt_gate_config(tmp_path) == "off"


def test_maybe_run_workflow_prompt_gate_off_skips_check() -> None:
    should_continue, exit_code = maybe_run_workflow_prompt_gate(
        [str(VAGUE_FIXTURE)],
        cli_prompt_checkup=None,
        no_prompt_checkup=True,
        project_root=REPO_ROOT,
        quiet=True,
    )
    assert should_continue is True
    assert exit_code == 0


def test_maybe_run_workflow_prompt_gate_strict_blocks_vague_prompt() -> None:
    should_continue, exit_code = maybe_run_workflow_prompt_gate(
        [str(VAGUE_FIXTURE)],
        cli_prompt_checkup="strict",
        no_prompt_checkup=False,
        project_root=REPO_ROOT,
        quiet=True,
    )
    assert should_continue is False
    assert exit_code != 0


def test_maybe_run_workflow_prompt_gate_warn_continues() -> None:
    should_continue, exit_code = maybe_run_workflow_prompt_gate(
        [str(VAGUE_FIXTURE)],
        cli_prompt_checkup="warn",
        no_prompt_checkup=False,
        project_root=REPO_ROOT,
        quiet=True,
    )
    assert should_continue is True
    assert exit_code == 0


@patch("pdd.change_main.change_func")
@patch("pdd.change_main.construct_paths")
@patch("pdd.change_main.resolve_effective_config")
def test_change_main_strict_prompt_gate_blocks_after_save(
    mock_resolve_config,
    mock_construct_paths,
    mock_change_func,
    tmp_path: Path,
) -> None:
    prompt_path = tmp_path / "changed_python.prompt"
    prompt_path.write_text(VAGUE_FIXTURE.read_text(encoding="utf-8"), encoding="utf-8")
    code_path = tmp_path / "module.py"
    code_path.write_text("def foo():\n    return 1\n", encoding="utf-8")

    change_prompt = tmp_path / "change_python.prompt"
    change_prompt.write_text("% apply a change\n", encoding="utf-8")

    mock_resolve_config.return_value = {
        "strength": 0.5,
        "temperature": 0.0,
        "time": 0.25,
    }
    mock_construct_paths.return_value = (
        {},
        {
            "change_prompt_file": change_prompt.read_text(encoding="utf-8"),
            "input_code": code_path.read_text(encoding="utf-8"),
            "input_prompt_file": prompt_path.read_text(encoding="utf-8"),
        },
        {"output_prompt_file": str(prompt_path)},
        "python",
    )
    mock_change_func.return_value = (
        prompt_path.read_text(encoding="utf-8"),
        0.1,
        "test-model",
    )

    ctx = MagicMock()
    ctx.obj = {
        "quiet": True,
        "force": True,
        "prompt_checkup": "strict",
        "no_prompt_checkup": False,
    }

    original_cwd = Path.cwd()
    os.chdir(tmp_path)
    try:
        message, _cost, _model = change_main(
            ctx=ctx,
            change_prompt_file=str(change_prompt),
            input_code=str(code_path),
            input_prompt_file=str(prompt_path),
            output=str(prompt_path),
            use_csv=False,
            budget=1.0,
        )
    finally:
        os.chdir(original_cwd)

    assert "Prompt checkup blocked" in message


def test_change_agentic_runs_prompt_gate_on_changed_prompts() -> None:
    runner = CliRunner()
    changed = [str(REPO_ROOT / "prompts" / "foo_python.prompt")]

    with patch("pdd.commands.modify.run_agentic_change") as run_change:
        run_change.return_value = (True, "ok", 0.1, "codex", changed)
        with patch("pdd.commands.modify.maybe_run_workflow_prompt_gate") as gate:
            gate.return_value = (True, 0)
            result = runner.invoke(
                change,
                ["https://github.com/org/repo/issues/42", "--no-prompt-checkup"],
                obj={"quiet": True},
            )

    assert result.exit_code == 0
    gate.assert_called_once()
    assert gate.call_args.kwargs["no_prompt_checkup"] is True


def test_generate_agentic_calls_prompt_gate_after_prompt_writes() -> None:
    runner = CliRunner()
    output_files = [str(REPO_ROOT / "prompts" / "new_feature_python.prompt")]

    with patch("pdd.agentic_architecture.run_agentic_architecture") as run_arch:
        run_arch.return_value = (True, "ok", 0.0, "codex", output_files)
        with patch("pdd.commands.generate._maybe_run_prompt_gate") as gate:
            gate.return_value = True
            result = runner.invoke(
                generate,
                ["https://github.com/org/repo/issues/99", "--prompt-checkup", "warn"],
                obj={"quiet": True, "verbose": False},
            )

    assert result.exit_code == 0
    gate.assert_called_once()
    assert gate.call_args.kwargs["prompt_checkup"] == "warn"


def test_checkup_devunit_target_cli(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.chdir(tmp_path)
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt = prompts_dir / "refund_payment_python.prompt"
    prompt.write_text(CLEAN_FIXTURE.read_text(encoding="utf-8"), encoding="utf-8")

    result = CliRunner().invoke(
        checkup,
        ["refund_payment", "--json"],
        obj={"quiet": True},
    )
    assert result.exit_code in {0, 1}
    payload = json.loads(result.output)
    assert payload["schema"] == "pdd.prompt_source_set_report.v1"


def test_checkup_prompt_directory_json_cli(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.chdir(tmp_path)
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    (prompts_dir / "alpha_python.prompt").write_text(
        CLEAN_FIXTURE.read_text(encoding="utf-8"),
        encoding="utf-8",
    )

    result = CliRunner().invoke(
        checkup,
        ["prompts", "--json"],
        obj={"quiet": True},
    )
    assert result.exit_code in {0, 1}
    payload = json.loads(result.output)
    assert payload["schema"] == "pdd.prompt_source_set_report.v1"
    assert len(payload["reports"]) == 1


def test_checkup_prompt_json_stdout_is_parseable_only() -> None:
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "pdd.cli",
            "checkup",
            str(CLEAN_FIXTURE),
            "--json",
        ],
        cwd=REPO_ROOT,
        env=_cli_env(),
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.stdout.startswith("{")
    payload = json.loads(result.stdout)
    assert payload["schema"] == "pdd.prompt_source_set_report.v1"
    assert "Checking for updates" not in result.stdout
