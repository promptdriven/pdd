"""CLI command wiring tests for optional evidence receipts."""
from __future__ import annotations

from types import SimpleNamespace
from unittest.mock import patch

from click.testing import CliRunner

from pdd.commands.analysis import detect_change
from pdd.commands.generate import generate, test as pdd_test_command
from pdd.commands.maintenance import sync
from pdd.commands.modify import change
from pdd.commands.utility import verify


def test_generate_evidence_records_completed_output(tmp_path) -> None:
    prompt = tmp_path / "item_python.prompt"
    output = tmp_path / "item.py"
    prompt.write_text("prompt", encoding="utf-8")
    with patch("pdd.commands.generate.code_generator_main", return_value=("code", False, 0.1, "model")), \
         patch("pdd.commands.generate.write_evidence_manifest") as record:
        result = CliRunner().invoke(
            generate,
            [str(prompt), "--output", str(output), "--evidence"],
            obj={"temperature": 0.0, "quiet": True},
        )
    assert result.exit_code == 0, result.output
    assert record.call_args.kwargs["prompt_file"] == str(prompt)
    assert record.call_args.kwargs["output_files"] == [str(output)]


def test_test_evidence_records_manual_generation(tmp_path) -> None:
    prompt = tmp_path / "item_python.prompt"
    source = tmp_path / "item.py"
    prompt.write_text("prompt", encoding="utf-8")
    source.write_text("code", encoding="utf-8")
    generated = SimpleNamespace(content="tests", cost=0.2, model="model")
    with patch("pdd.cmd_test_main.cmd_test_main", return_value=generated), \
         patch("pdd.commands.generate.write_evidence_manifest") as record:
        result = CliRunner().invoke(
            pdd_test_command,
            ["--manual", str(prompt), str(source), "--evidence"],
            obj={"temperature": 0.0, "quiet": True},
        )
    assert result.exit_code == 0, result.output
    assert record.call_args.kwargs["validation"]["unit_tests"] == "passed"


def test_sync_evidence_records_module_run() -> None:
    with patch("pdd.commands.maintenance.sync_main", return_value=({"ok": True}, 0.3, "model")), \
         patch("pdd.commands.maintenance.write_evidence_manifest") as record:
        result = CliRunner().invoke(
            sync,
            ["refund", "--evidence"],
            obj={"temperature": 0.0, "quiet": True},
        )
    assert result.exit_code == 0, result.output
    assert record.call_args.kwargs["basename"] == "refund"


def test_verify_evidence_records_validation_status(tmp_path) -> None:
    files = [tmp_path / name for name in ("item.prompt", "item.py", "verify.py")]
    for path in files:
        path.write_text("input", encoding="utf-8")
    with patch(
        "pdd.commands.utility.fix_verification_main",
        return_value=(True, "program", "code", 1, 0.4, "model"),
    ), patch("pdd.commands.utility.write_evidence_manifest") as record:
        result = CliRunner().invoke(
            verify,
            [*(str(path) for path in files), "--evidence"],
            obj={"temperature": 0.0, "quiet": True},
        )
    assert result.exit_code == 0, result.output
    assert record.call_args.kwargs["validation"]["verify"] == "passed"


def test_detect_stories_evidence_records_validation_status() -> None:
    with patch(
        "pdd.commands.analysis.run_user_story_tests",
        return_value=(True, [], 0.0, "local"),
    ), patch("pdd.commands.analysis.write_evidence_manifest") as record:
        result = CliRunner().invoke(
            detect_change,
            ["--stories", "--evidence"],
            obj={"temperature": 0.0, "quiet": True},
        )
    assert result.exit_code == 0, result.output
    assert record.call_args.kwargs["validation"]["detect_stories"] == "passed"


def test_change_evidence_records_manual_output(tmp_path) -> None:
    change_file = tmp_path / "change.txt"
    source = tmp_path / "item.py"
    prompt = tmp_path / "item_python.prompt"
    output = tmp_path / "changed.prompt"
    for path in (change_file, source, prompt):
        path.write_text("input", encoding="utf-8")
    with patch("pdd.commands.modify.change_main", return_value=("updated", 0.5, "model")), \
         patch("pdd.commands.modify.write_evidence_manifest") as record:
        result = CliRunner().invoke(
            change,
            [
                "--manual",
                str(change_file),
                str(source),
                str(prompt),
                "--output",
                str(output),
                "--evidence",
            ],
            obj={"temperature": 0.0, "quiet": True},
        )
    assert result.exit_code == 0, result.output
    assert record.call_args.kwargs["prompt_file"] == str(prompt)
