"""Tests for the `pdd intent` planning command."""
from __future__ import annotations

import json
from pathlib import Path

import click
from click.testing import CliRunner

from pdd.commands import register_commands
from pdd.commands.intent import intent


def test_help_describes_local_planning() -> None:
    runner = CliRunner()

    group_help = runner.invoke(intent, ["--help"])
    plan_help = runner.invoke(intent, ["plan", "--help"])

    assert group_help.exit_code == 0
    assert "ordinary product intent" in group_help.output
    assert plan_help.exit_code == 0
    assert "without GitHub" in plan_help.output
    assert "file changes" in plan_help.output


def test_inline_text_renders_review_card_without_writes(tmp_path: Path) -> None:
    runner = CliRunner()
    before = set(tmp_path.iterdir())

    result = runner.invoke(
        intent,
        [
            "plan",
            "--text",
            "Add a calculator. Never send inputs over the network.",
            "--project-root",
            str(tmp_path),
        ],
    )

    assert result.exit_code == 0, result.output
    assert "What I heard:" in result.output
    assert "Never send inputs over the network." in result.output
    assert "Planning only" in result.output
    assert set(tmp_path.iterdir()) == before


def test_json_output_is_machine_readable_and_has_no_status_prose(
    tmp_path: Path,
) -> None:
    runner = CliRunner()

    result = runner.invoke(
        intent,
        [
            "plan",
            "--text",
            "Create a calculator.",
            "--project-root",
            str(tmp_path),
            "--json",
        ],
    )

    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["schema_version"] == "pdd.intent.plan.v1"
    assert payload["capabilities"]["apply"] is False
    assert "Planning only" not in result.output


def test_local_file_source_is_recorded(tmp_path: Path) -> None:
    runner = CliRunner()
    source = tmp_path / "request.md"
    source.write_text("# Export\n\nAdd PDF export.\n", encoding="utf-8")

    result = runner.invoke(
        intent,
        [
            "plan",
            str(source),
            "--project-root",
            str(tmp_path),
            "--json",
        ],
    )

    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["source"] == {"kind": "file", "ref": str(source.resolve())}
    assert payload["original_request"] == "# Export\n\nAdd PDF export."


def test_piped_stdin_is_supported(tmp_path: Path) -> None:
    runner = CliRunner()

    result = runner.invoke(
        intent,
        ["plan", "--project-root", str(tmp_path), "--json"],
        input="Create an offline report viewer.\n",
    )

    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["source"] == {"kind": "stdin", "ref": "<stdin>"}


def test_source_and_text_are_mutually_exclusive(tmp_path: Path) -> None:
    runner = CliRunner()
    source = tmp_path / "request.md"
    source.write_text("Add export.", encoding="utf-8")

    result = runner.invoke(
        intent,
        [
            "plan",
            str(source),
            "--text",
            "Different request",
            "--project-root",
            str(tmp_path),
        ],
    )

    assert result.exit_code != 0
    assert "either SOURCE or --text" in result.output


def test_empty_input_is_rejected(tmp_path: Path) -> None:
    runner = CliRunner()

    result = runner.invoke(
        intent,
        ["plan", "--project-root", str(tmp_path)],
        input="",
    )

    assert result.exit_code != 0
    assert "must not be empty" in result.output


def test_oversized_input_is_rejected(tmp_path: Path) -> None:
    runner = CliRunner()

    result = runner.invoke(
        intent,
        [
            "plan",
            "--text",
            "x" * 100_001,
            "--project-root",
            str(tmp_path),
        ],
    )

    assert result.exit_code != 0
    assert "100,000-character" in result.output


def test_proposed_project_root_may_not_exist(tmp_path: Path) -> None:
    runner = CliRunner()
    proposed = tmp_path / "packages" / "new_tool"

    result = runner.invoke(
        intent,
        [
            "plan",
            "--text",
            "Create a new tool.",
            "--project-root",
            str(proposed),
            "--json",
        ],
    )

    assert result.exit_code == 0, result.output
    payload = json.loads(result.output)
    assert payload["project"]["exists"] is False
    assert not proposed.exists()


def test_command_is_registered_at_top_level() -> None:
    cli = click.Group()

    register_commands(cli)

    assert "intent" in cli.commands
