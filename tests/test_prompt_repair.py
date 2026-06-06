"""Tests for pdd.prompt_repair bounded repair loop."""
from __future__ import annotations

from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.prompt_repair import (
    PromptRepairConfig,
    _repair_brief,
    _source_set_report,
    _validate_changed_prompt,
    discover_prompt_paths,
    format_token_delta_summary,
    load_prompt_repair_defaults,
    run_prompt_repair_loop,
)

FIXTURES = Path(__file__).parent / "fixtures" / "prompt_lint"


def test_off_mode_skips_repair(tmp_path: Path) -> None:
    prompt = tmp_path / "sample.prompt"
    prompt.write_text((FIXTURES / "vague_undefined.prompt").read_text(encoding="utf-8"), encoding="utf-8")
    before = prompt.read_bytes()

    result = run_prompt_repair_loop(
        prompt,
        PromptRepairConfig(mode="off"),
        cwd=tmp_path,
    )

    assert result.repair_skipped is True
    assert result.rounds_used == 0
    assert prompt.read_bytes() == before


def test_clean_prompt_skips_repair(tmp_path: Path) -> None:
    prompt = tmp_path / "clean.prompt"
    prompt.write_text((FIXTURES / "clean.prompt").read_text(encoding="utf-8"), encoding="utf-8")

    result = run_prompt_repair_loop(
        prompt,
        PromptRepairConfig(mode="best-effort"),
        cwd=tmp_path,
    )

    assert result.repair_skipped is True
    assert result.rounds_used == 0
    assert result.success is True


def test_non_lint_source_set_findings_trigger_change_and_full_recheck(
    tmp_path: Path,
) -> None:
    prompt = tmp_path / "clean.prompt"
    original = (FIXTURES / "clean.prompt").read_text(encoding="utf-8")
    prompt.write_text(original, encoding="utf-8")
    source_set_report = {
        "schema": "pdd.prompt_source_set_report.v1",
        "status": "warn",
        "target": str(prompt),
        "findings": [
            {
                "source_check": "coverage",
                "severity": "warn",
                "code": "unchecked",
                "message": "R1 is not covered",
            },
            {
                "source_check": "gate",
                "severity": "warn",
                "code": "missing_evidence",
                "message": "Required evidence is missing",
            },
        ],
    }
    repaired = original + "\n% R1 coverage and gate evidence documented.\n"

    with (
        patch(
            "pdd.prompt_repair.change",
            return_value=(repaired, 0.0, "mock"),
        ) as mock_change,
        patch(
            "pdd.prompt_repair._recheck_source_set",
            return_value={
                "schema": "pdd.prompt_source_set_report.v1",
                "status": "pass",
                "target": str(prompt),
                "findings": [],
            },
        ) as mock_recheck,
    ):
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort"),
            context={"source_set_report": source_set_report},
            cwd=tmp_path,
            quiet=True,
        )

    assert result.repair_skipped is False
    assert result.rounds_used == 1
    assert result.findings_after == []
    assert prompt.read_text(encoding="utf-8") == repaired
    assert "coverage" in mock_change.call_args.kwargs["change_prompt"]
    assert "gate" in mock_change.call_args.kwargs["change_prompt"]
    mock_recheck.assert_called_once()


def test_repair_adds_vocabulary_and_reclean(tmp_path: Path) -> None:
    prompt = tmp_path / "vague.prompt"
    prompt.write_text((FIXTURES / "vague_undefined.prompt").read_text(encoding="utf-8"), encoding="utf-8")
    repaired = prompt.read_text(encoding="utf-8") + (
        "\n<vocabulary>\nvalid: passes schema and business rules checks\n"
        "reasonable: completes within 2000 ms on CI hardware\n"
        "gracefully: returns HTTP 4xx without raising\n"
        "authorized: caller holds a valid session token\n"
        "duplicate: same idempotency key seen within 24h\n"
        "active: account status is enabled\n"
        "complete: all required fields are non-empty\n</vocabulary>\n"
    )

    with patch(
        "pdd.prompt_repair.change",
        return_value=(repaired, 0.0, "mock"),
    ):
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort", max_rounds=1),
            cwd=tmp_path,
            quiet=True,
        )

    assert result.rounds_used == 1
    assert "<vocabulary>" in prompt.read_text(encoding="utf-8")
    assert result.token_delta >= 0
    assert result.audit_path is not None
    assert result.audit_path.is_file()


def test_max_rounds_respected(tmp_path: Path) -> None:
    prompt = tmp_path / "vague.prompt"
    prompt.write_text((FIXTURES / "vague_undefined.prompt").read_text(encoding="utf-8"), encoding="utf-8")
    calls = {"count": 0}

    def _fake_change(**kwargs):
        calls["count"] += 1
        return kwargs["input_prompt"] + f"\n% repair round {calls['count']}\n", 0.0, "mock"

    with patch("pdd.prompt_repair.change", side_effect=_fake_change):
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort", max_rounds=2),
            cwd=tmp_path,
            quiet=True,
        )

    assert calls["count"] == 2
    assert result.rounds_used <= 2


def test_llm_failure_does_not_raise(tmp_path: Path) -> None:
    prompt = tmp_path / "vague.prompt"
    prompt.write_text((FIXTURES / "vague_undefined.prompt").read_text(encoding="utf-8"), encoding="utf-8")

    with patch(
        "pdd.prompt_repair.change",
        side_effect=RuntimeError("provider error"),
    ):
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort"),
            cwd=tmp_path,
            quiet=True,
        )

    assert result.success is False
    # issues_after must reflect actual remaining issues, not [] (which would cause callers to skip retries)
    assert len(result.issues_after) > 0


def test_strict_mode_fails_with_remaining_issues(tmp_path: Path) -> None:
    prompt = tmp_path / "vague.prompt"
    prompt.write_text((FIXTURES / "vague_undefined.prompt").read_text(encoding="utf-8"), encoding="utf-8")

    with patch(
        "pdd.prompt_repair.change",
        side_effect=lambda **kwargs: (kwargs["input_prompt"], 0.0, "mock"),
    ):
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="strict", max_rounds=1),
            cwd=tmp_path,
            quiet=True,
        )

    assert result.success is False
    assert result.issues_after


def test_best_effort_continues_with_remaining_issues(tmp_path: Path) -> None:
    prompt = tmp_path / "vague.prompt"
    prompt.write_text((FIXTURES / "vague_undefined.prompt").read_text(encoding="utf-8"), encoding="utf-8")

    with patch(
        "pdd.prompt_repair.change",
        side_effect=lambda **kwargs: (kwargs["input_prompt"], 0.0, "mock"),
    ):
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort", max_rounds=1),
            cwd=tmp_path,
            quiet=True,
        )

    assert result.success is True
    assert result.issues_after


def test_token_budget_drops_patches(tmp_path: Path) -> None:
    prompt = tmp_path / "vague.prompt"
    prompt.write_text((FIXTURES / "vague_undefined.prompt").read_text(encoding="utf-8"), encoding="utf-8")
    huge_prompt = prompt.read_text(encoding="utf-8") + ("x" * 5000)

    with patch(
        "pdd.prompt_repair.change",
        return_value=(huge_prompt, 0.0, "mock"),
    ):
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort", max_token_growth=10),
            cwd=tmp_path,
            quiet=True,
        )

    assert result.success is True
    assert result.message == "token budget exceeded"
    assert "<vocabulary>" not in prompt.read_text(encoding="utf-8")


def test_format_token_delta_summary() -> None:
    from pdd.prompt_repair import RepairResult

    summary = format_token_delta_summary(
        RepairResult(
            success=True,
            tokens_before=100,
            tokens_after=150,
            token_delta=50,
            preamble_estimate=40,
        )
    )
    assert "Prompt token delta: +50 tokens" in summary
    assert "40 tokens are reusable contract preamble" in summary


def test_load_prompt_repair_defaults_from_pyproject(tmp_path: Path) -> None:
    (tmp_path / "pyproject.toml").write_text(
        """
[tool.pdd.checkup]
prompt_repair = "best-effort"
max_prompt_repair_rounds = 3
max_prompt_token_growth = 500
max_prompt_repair_seconds = 45.0
""".strip(),
        encoding="utf-8",
    )
    config = load_prompt_repair_defaults(tmp_path)
    assert config.mode == "best-effort"
    assert config.max_rounds == 3
    assert config.max_token_growth == 500
    assert config.max_seconds == 45.0


def test_discover_prompt_paths_fallback_to_prompts_dir(tmp_path: Path) -> None:
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    good = prompts_dir / "feature_python.prompt"
    good.write_text("% sample\n", encoding="utf-8")
    llm_prompt = prompts_dir / "feature_LLM.prompt"
    llm_prompt.write_text("% llm\n", encoding="utf-8")

    with patch("pdd.prompt_repair.subprocess.run", side_effect=OSError("no git")):
        paths = discover_prompt_paths(tmp_path)

    assert good.resolve() in [p.resolve() for p in paths]
    assert all(not p.name.endswith("_LLM.prompt") for p in paths)


def test_validate_changed_prompt_rejects_delimiter_leak() -> None:
    assert _validate_changed_prompt(
        "% original\n",
        "<<<MODIFIED_PROMPT>>>\n% changed\n<<<END_MODIFIED_PROMPT>>>",
    ) is None


def test_source_set_report_requires_schema() -> None:
    assert _source_set_report({"source_set_report": '{"status": "warn"}'}) is None


def test_repair_brief_includes_non_lint_findings() -> None:
    brief = _repair_brief(
        [{"source_check": "coverage", "code": "unchecked"}],
        {"recommended_actions": "pdd checkup coverage sample"},
    )
    assert '"source_check": "coverage"' in brief
    assert "pdd checkup coverage sample" in brief


@patch("pdd.agentic_checkup._check_gh_cli", return_value=True)
@patch("pdd.agentic_checkup._parse_issue_url", return_value=("o", "r", 1))
@patch("pdd.agentic_checkup._run_gh_command", return_value=(True, '{"title":"t","body":"","comments_url":""}'))
@patch("pdd.agentic_checkup._fetch_comments", return_value="")
@patch("pdd.agentic_checkup._find_project_root")
@patch("pdd.agentic_checkup._load_architecture_json", return_value=([], None))
@patch("pdd.agentic_checkup._load_pddrc_content", return_value="")
@patch("pdd.agentic_checkup.discover_prompt_paths")
@patch("pdd.agentic_checkup.run_prompt_repair_loop")
@patch("pdd.checkup_prompt_main.build_prompt_source_set_report")
@patch("pdd.agentic_checkup.run_agentic_checkup_orchestrator")
def test_agentic_checkup_strict_repair_blocks_before_orchestrator(
    mock_orchestrator,
    mock_build_report,
    mock_repair,
    mock_discover,
    *_mocks,
) -> None:
    from pdd.agentic_checkup import run_agentic_checkup
    from pdd.prompt_repair import RepairResult

    mock_discover.return_value = [Path("prompts/x_python.prompt")]
    # Both pre-repair and post-repair structured reports show failure
    failing_report = MagicMock()
    failing_report.passed = False
    failing_report.status = "fail"
    failing_report.as_dict.return_value = {"status": "fail", "findings": []}
    failing_report.recommended_actions.return_value = []
    mock_build_report.return_value = failing_report
    mock_repair.return_value = RepairResult(success=False, issues_after=[])

    success, message, cost, _model = run_agentic_checkup(
        issue_url="https://github.com/o/r/issues/1",
        quiet=True,
        prompt_repair="strict",
    )

    assert success is False
    assert "Prompt repair strict mode" in message
    assert cost == 0.0
    mock_repair.assert_called_once()  # repair ran
    mock_orchestrator.assert_not_called()  # orchestrator blocked by strict failure


@pytest.mark.parametrize("flag", ["--prompt-repair", "--max-prompt-repair-rounds"])
def test_checkup_help_exposes_prompt_repair_flags(flag: str) -> None:
    from click.testing import CliRunner
    from pdd.cli import cli

    result = CliRunner().invoke(cli, ["--quiet", "checkup", "--help"])
    assert result.exit_code == 0
    assert flag in result.output


def test_repair_llm_failure_preserves_existing_issues(tmp_path: Path) -> None:
    """Regression: when the LLM call fails, RepairResult.issues_after must reflect the
    actual remaining issues, not an empty list that would cause callers to skip retries.
    (Issue #1422 fix)"""
    prompt = tmp_path / "vague.prompt"
    prompt.write_text(
        (Path(__file__).parent / "fixtures" / "prompt_lint" / "vague_undefined.prompt")
        .read_text(encoding="utf-8"),
        encoding="utf-8",
    )

    with patch("pdd.prompt_repair.change", side_effect=RuntimeError("failed")):
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort"),
            cwd=tmp_path,
        )

    assert result.success is False
    assert len(result.issues_after) > 0, (
        "issues_after is empty after LLM failure — callers will skip retries incorrectly"
    )
    assert len(result.issues_after) == len(result.issues_before), (
        "issues_after should match issues_before when no repair was applied"
    )
