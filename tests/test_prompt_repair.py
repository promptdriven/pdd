"""Tests for pdd.prompt_repair bounded repair loop."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_common import AgenticTaskResult, AgenticUnsupportedSemanticsError
from pdd.prompt_repair import (
    PromptRepairConfig,
    RepairResult,
    _actionable_findings,
    _lint_findings,
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
    assert result.message != "no lint issues"
    assert result.findings_after == []
    assert prompt.read_text(encoding="utf-8") == repaired
    # coverage is actionable (prompt-fixable) so it must appear in the brief.
    assert "coverage" in mock_change.call_args.kwargs["change_prompt"]
    # gate/missing_evidence is not prompt-fixable and must be filtered from the
    # repair brief so the LLM is not asked to do impossible work.
    assert "missing_evidence" not in mock_change.call_args.kwargs["change_prompt"]
    mock_recheck.assert_called_once()


def _coverage_report(prompt: Path) -> dict:
    """Non-VAGUE source-set report with a single coverage finding for repair loop tests."""
    return {
        "schema": "pdd.prompt_source_set_report.v1",
        "status": "warn",
        "target": str(prompt),
        "findings": [
            {
                "source_check": "coverage",
                "severity": "warn",
                "code": "unchecked",
                "message": "R1 is not covered by any test",
            }
        ],
    }


def _pass_report(prompt: Path) -> dict:
    return {
        "schema": "pdd.prompt_source_set_report.v1",
        "status": "pass",
        "target": str(prompt),
        "findings": [],
    }


def test_exact_codex_repair_exposes_observed_model_usage_and_known_zero_cost(
    tmp_path: Path,
) -> None:
    prompt = tmp_path / "exact.prompt"
    original = (FIXTURES / "clean.prompt").read_text(encoding="utf-8")
    repaired = original + "\n% Exact Codex repair.\n"
    prompt.write_text(original, encoding="utf-8")
    exact_result = AgenticTaskResult(
        True,
        f"<<<MODIFIED_PROMPT>>>\n{repaired}\n<<<END_MODIFIED_PROMPT>>>",
        0.0,
        "openai",
        {"input_tokens": 100, "output_tokens": 20, "cached_input_tokens": 10},
        model_id="gpt-5.6-sol",
        usage_source="provider_reported",
        estimate_method="provider_usage",
    )

    with (
        patch(
            "pdd.prompt_repair._run_exact_prompt_change",
            return_value=exact_result,
        ) as mock_exact,
        patch("pdd.prompt_repair.change") as mock_legacy,
        patch(
            "pdd.prompt_repair._recheck_source_set",
            return_value=_pass_report(prompt),
        ),
    ):
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort"),
            context={"source_set_report": _coverage_report(prompt)},
            cwd=tmp_path,
            quiet=True,
            model="gpt-5.6-sol",
            reasoning_effort="xhigh",
        )

    mock_legacy.assert_not_called()
    assert mock_exact.call_args.kwargs["model"] == "gpt-5.6-sol"
    assert mock_exact.call_args.kwargs["reasoning_effort"] == "xhigh"
    assert result.model_used == "gpt-5.6-sol"
    assert result.cost_usd == 0.0
    assert result.billing_status == "known_zero_subscription"
    assert result.usage == [exact_result.usage]
    assert prompt.read_text(encoding="utf-8").strip() == repaired.strip()
    audit = json.loads(result.audit_path.read_text(encoding="utf-8"))
    assert audit["apply_method"] == "pdd.agentic_common.run_exact_agentic_task"
    assert audit["effective_model"] == "gpt-5.6-sol"
    assert audit["cost_usd"] == 0.0
    assert audit["billing_status"] == "known_zero_subscription"


def test_unsupported_exact_repair_selector_fails_before_inference(
    tmp_path: Path,
) -> None:
    prompt = tmp_path / "unsupported.prompt"
    prompt.write_text("placeholder", encoding="utf-8")
    with (
        patch("pdd.prompt_repair._run_exact_prompt_change") as mock_exact,
        patch("pdd.prompt_repair.change") as mock_legacy,
        pytest.raises(AgenticUnsupportedSemanticsError),
    ):
        run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort"),
            cwd=tmp_path,
            model="claude-opus-4-7",
            reasoning_effort="high",
        )
    mock_exact.assert_not_called()
    mock_legacy.assert_not_called()


def test_repair_adds_vocabulary_and_reclean(tmp_path: Path) -> None:
    prompt = tmp_path / "vague.prompt"
    original = (FIXTURES / "clean.prompt").read_text(encoding="utf-8")
    prompt.write_text(original, encoding="utf-8")
    repaired = original + "\n% R1 coverage documented.\n"

    with (
        patch("pdd.prompt_repair.change", return_value=(repaired, 0.0, "mock")),
        patch("pdd.prompt_repair._recheck_source_set", return_value=_pass_report(prompt)),
    ):
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort", max_rounds=1),
            context={"source_set_report": _coverage_report(prompt)},
            cwd=tmp_path,
            quiet=True,
        )

    assert result.rounds_used == 1
    assert "R1 coverage" in prompt.read_text(encoding="utf-8")
    assert result.token_delta >= 0
    assert result.audit_path is not None
    assert result.audit_path.is_file()


def test_max_rounds_respected(tmp_path: Path) -> None:
    prompt = tmp_path / "vague.prompt"
    prompt.write_text((FIXTURES / "clean.prompt").read_text(encoding="utf-8"), encoding="utf-8")
    calls = {"count": 0}
    report = _coverage_report(prompt)

    def _fake_change(**kwargs):
        calls["count"] += 1
        return kwargs["input_prompt"] + f"\n% repair round {calls['count']}\n", 0.0, "mock"

    with (
        patch("pdd.prompt_repair.change", side_effect=_fake_change),
        patch("pdd.prompt_repair._recheck_source_set", return_value=report),
    ):
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort", max_rounds=2),
            context={"source_set_report": report},
            cwd=tmp_path,
            quiet=True,
        )

    assert calls["count"] == 2
    assert result.rounds_used <= 2


def test_llm_failure_does_not_raise(tmp_path: Path) -> None:
    prompt = tmp_path / "vague.prompt"
    prompt.write_text((FIXTURES / "clean.prompt").read_text(encoding="utf-8"), encoding="utf-8")
    report = _coverage_report(prompt)

    with patch("pdd.prompt_repair.change", side_effect=RuntimeError("provider error")):
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort"),
            context={"source_set_report": report},
            cwd=tmp_path,
            quiet=True,
        )

    assert result.success is False
    # findings_after must reflect remaining findings so callers do not skip retries
    assert len(result.findings_after) > 0


def test_strict_mode_fails_with_remaining_issues(tmp_path: Path) -> None:
    prompt = tmp_path / "vague.prompt"
    original = (FIXTURES / "clean.prompt").read_text(encoding="utf-8")
    prompt.write_text(original, encoding="utf-8")
    report = _coverage_report(prompt)

    with (
        patch("pdd.prompt_repair.change", side_effect=lambda **kwargs: (kwargs["input_prompt"], 0.0, "mock")),
        patch("pdd.prompt_repair._recheck_source_set", return_value=report),
    ):
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="strict", max_rounds=1),
            context={"source_set_report": report},
            cwd=tmp_path,
            quiet=True,
        )

    assert result.success is False
    assert result.findings_after


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
    original = (FIXTURES / "clean.prompt").read_text(encoding="utf-8")
    prompt.write_text(original, encoding="utf-8")
    huge_prompt = original + ("x" * 5000)
    report = _coverage_report(prompt)

    with patch("pdd.prompt_repair.change", return_value=(huge_prompt, 0.0, "mock")):
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort", max_token_growth=10),
            context={"source_set_report": report},
            cwd=tmp_path,
            quiet=True,
        )

    assert result.success is True
    assert result.message == "token budget exceeded"
    assert prompt.read_text(encoding="utf-8") == original


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


def test_load_prompt_repair_defaults_ignores_pddrc(tmp_path: Path) -> None:
    """Defaults come from pyproject.toml [tool.pdd.checkup], not .pddrc."""
    (tmp_path / ".pddrc").write_text(
        """
contexts:
  default:
    checkup:
      prompt_repair: strict
      max_prompt_repair_rounds: 9
""".strip(),
        encoding="utf-8",
    )
    config = load_prompt_repair_defaults(tmp_path)
    assert config.mode == "off"
    assert config.max_rounds == 1


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


def test_coverage_only_clean_lint_triggers_change_path(tmp_path: Path) -> None:
    """Regression: zero lint issues must not skip repair when coverage fails."""
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
                "recommended_action": "Add a coverage line for R1.",
            },
        ],
    }
    repaired = original + "\n% R1: documented requirement.\n"

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
    assert result.message != "no lint issues"
    assert result.message != "no actionable source-set findings"
    mock_change.assert_called_once()
    kwargs = mock_change.call_args.kwargs
    assert kwargs["input_prompt"] == original
    assert "source_set_report" in kwargs["input_code"]
    assert "MODIFIED_PROMPT" in kwargs["change_prompt"] or "change()" in kwargs["change_prompt"]
    mock_recheck.assert_called_once()
    assert result.audit_path is not None
    audit = json.loads(result.audit_path.read_text(encoding="utf-8"))
    assert audit["apply_method"] == "pdd.change.change"
    assert audit["applied_operations"] == ["CHANGE"]


def test_gate_only_missing_evidence_skips_repair(tmp_path: Path) -> None:
    """External-only gate findings cannot be fixed by prompt edits alone."""
    prompt = tmp_path / "clean.prompt"
    prompt.write_text((FIXTURES / "clean.prompt").read_text(encoding="utf-8"), encoding="utf-8")
    source_set_report = {
        "schema": "pdd.prompt_source_set_report.v1",
        "status": "warn",
        "target": str(prompt),
        "findings": [
            {
                "source_check": "gate",
                "severity": "warn",
                "code": "missing_evidence",
                "message": "No evidence manifest",
            },
        ],
    }

    with patch("pdd.prompt_repair.change") as mock_change:
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort"),
            context={"source_set_report": source_set_report},
            cwd=tmp_path,
            quiet=True,
        )

    assert result.repair_skipped is True
    assert result.rounds_used == 0
    assert result.message == "no actionable source-set findings"
    mock_change.assert_not_called()
    # findings_after must match findings_before in the skip path (both empty here
    # because gate findings are filtered out as non-actionable).
    assert result.findings_after == result.findings_before


def test_clarification_findings_skipped_by_non_interactive_repair(tmp_path: Path) -> None:
    """requires_clarification=True findings must not be auto-repaired (#1438)."""
    prompt = tmp_path / "vague.prompt"
    prompt.write_text((FIXTURES / "clean.prompt").read_text(encoding="utf-8"), encoding="utf-8")
    source_set_report = {
        "schema": "pdd.prompt_source_set_report.v1",
        "status": "warn",
        "target": str(prompt),
        "findings": [
            {
                "source_check": "lint",
                "severity": "warn",
                "code": "VAGUE_TERM",
                "message": "Ambiguous term needs clarification",
                "requires_clarification": True,
            },
        ],
    }

    with patch("pdd.prompt_repair.change") as mock_change:
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort"),
            context={"source_set_report": source_set_report},
            cwd=tmp_path,
            quiet=True,
        )

    assert result.repair_skipped is True
    assert result.rounds_used == 0
    assert result.message == "no actionable source-set findings"
    mock_change.assert_not_called()


def test_change_apply_validates_delimiters_before_write(tmp_path: Path) -> None:
    prompt = tmp_path / "vague.prompt"
    original = (FIXTURES / "clean.prompt").read_text(encoding="utf-8")
    prompt.write_text(original, encoding="utf-8")
    leaked = "<<<MODIFIED_PROMPT>>>\n% broken\n<<<END_MODIFIED_PROMPT>>>"
    report = _coverage_report(prompt)

    with patch("pdd.prompt_repair.change", return_value=(leaked, 0.0, "mock")):
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort"),
            context={"source_set_report": report},
            cwd=tmp_path,
            quiet=True,
        )

    assert result.success is True
    assert result.message == "invalid change result"
    assert prompt.read_text(encoding="utf-8") == original


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

    # Regression: is_strict must be forwarded to build_prompt_source_set_report on all
    # calls (initial check and post-repair recheck).  If is_strict is hardcoded False,
    # strict-mode warnings are silently downgraded to non-blocking in both phases.
    assert mock_build_report.call_count > 0, "build_prompt_source_set_report must be called"
    for _call in mock_build_report.call_args_list:
        assert _call.kwargs.get("strict") is True, (
            f"is_strict not forwarded to build_prompt_source_set_report: {_call}"
        )


@pytest.mark.parametrize(
    "flag",
    [
        "--prompt-repair",
        "--max-prompt-repair-rounds",
        "--prompt-repair-model",
        "--prompt-repair-effort",
    ],
)
def test_checkup_help_exposes_prompt_repair_flags(flag: str) -> None:
    from click.testing import CliRunner
    from pdd.cli import cli

    result = CliRunner().invoke(cli, ["--quiet", "checkup", "--help"])
    assert result.exit_code == 0
    assert flag in result.output


def test_checkup_forwards_exact_repair_selectors_and_tracks_known_zero_cost(
    tmp_path: Path,
) -> None:
    from click.testing import CliRunner
    from pdd.cli import cli

    prompt = tmp_path / "exact_cli.prompt"
    prompt.write_text("% prompt", encoding="utf-8")
    report = MagicMock(status="warn")
    report.as_dict.return_value = _coverage_report(prompt)
    report.recommended_actions.return_value = ["add coverage"]
    repair_result = RepairResult(
        success=True,
        model_used="gpt-5.6-sol",
        cost_usd=0.0,
        billing_status="known_zero_subscription",
    )
    with (
        patch(
            "pdd.commands.checkup.run_checkup_prompt",
            side_effect=[
                (False, "failed", 0.0, "", 0),
                (True, "passed", 0.0, "", 0),
            ],
        ),
        patch(
            "pdd.commands.checkup.build_prompt_source_set_report",
            return_value=report,
        ),
        patch(
            "pdd.commands.checkup.run_prompt_repair_loop",
            return_value=repair_result,
        ) as mock_repair,
    ):
        result = CliRunner().invoke(
            cli,
            [
                "--quiet",
                "checkup",
                str(prompt),
                "--project-root",
                str(tmp_path),
                "--prompt-repair",
                "strict",
                "--prompt-repair-model",
                "gpt-5.6-sol",
                "--prompt-repair-effort",
                "xhigh",
            ],
        )

    assert result.exit_code == 0, result.output
    assert mock_repair.call_args.kwargs["model"] == "gpt-5.6-sol"
    assert mock_repair.call_args.kwargs["reasoning_effort"] == "xhigh"


def test_best_effort_max_rounds_zero_is_a_skip_not_failure(tmp_path: Path) -> None:
    """max_rounds=0 with actionable findings must be a skip (success=True) in best-effort."""
    prompt = tmp_path / "vague.prompt"
    prompt.write_text((FIXTURES / "vague_undefined.prompt").read_text(encoding="utf-8"), encoding="utf-8")
    with patch("pdd.prompt_repair.change") as mock_change:
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort", max_rounds=0),
            cwd=tmp_path,
            quiet=True,
        )
    mock_change.assert_not_called()
    assert result.success is True, "best-effort with max_rounds=0 must succeed (skip, not failure)"
    assert result.repair_skipped is True
    assert result.rounds_used == 0
    # Skip path must preserve findings — callers inspect findings_after to decide
    # whether to retry or report; an empty list would silently hide existing issues.
    assert result.findings_after == result.findings_before, (
        "skip path must expose findings_before through findings_after"
    )


def test_repair_llm_failure_preserves_existing_issues(tmp_path: Path) -> None:
    """Regression: when the LLM call fails, RepairResult.findings_after must reflect the
    actual remaining findings, not an empty list that would cause callers to skip retries.
    (Issue #1422 fix)"""
    prompt = tmp_path / "vague.prompt"
    prompt.write_text((FIXTURES / "clean.prompt").read_text(encoding="utf-8"), encoding="utf-8")
    report = _coverage_report(prompt)

    with patch("pdd.prompt_repair.change", side_effect=RuntimeError("failed")):
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort"),
            context={"source_set_report": report},
            cwd=tmp_path,
        )

    assert result.success is False
    assert len(result.findings_after) > 0, (
        "findings_after is empty after LLM failure — callers will skip retries incorrectly"
    )
    assert len(result.findings_after) == len(result.findings_before), (
        "findings_after should match findings_before when no repair was applied"
    )


def test_lint_only_vague_findings_not_auto_repaired(tmp_path: Path) -> None:
    """VAGUE lint findings from the lint-only path must be excluded from auto-repair (#1438).

    When no source_set_report is provided, _lint_findings() builds the finding dicts.
    Those dicts must include requires_clarification=True for VAGUE codes so
    _actionable_findings() correctly excludes them from LLM auto-repair.
    """
    prompt = tmp_path / "vague.prompt"
    prompt.write_text(
        (FIXTURES / "vague_undefined.prompt").read_text(encoding="utf-8"), encoding="utf-8"
    )

    with patch("pdd.prompt_repair.change") as mock_change:
        result = run_prompt_repair_loop(
            prompt,
            PromptRepairConfig(mode="best-effort"),
            # No source_set_report — forces lint-only path
            cwd=tmp_path,
            quiet=True,
        )

    mock_change.assert_not_called()
    assert result.repair_skipped is True
    assert result.rounds_used == 0
    assert result.message == "no actionable source-set findings"


def test_lint_only_non_vague_findings_still_actionable(tmp_path: Path) -> None:
    """Non-VAGUE lint findings from the lint-only path must still be auto-repaired.

    The requires_clarification key must be False for non-VAGUE codes so the repair
    loop is NOT blocked from processing them.
    """
    from pdd.prompt_repair import _actionable_findings, _lint_findings
    from pdd.prompt_lint import LintIssue

    non_vague_issue = LintIssue(
        level="warn",
        term="",
        section="contract_rules",
        line="% no contract",
        message="No contract section found",
        code="MISSING_CONTRACT",
    )
    findings = _lint_findings([non_vague_issue])
    assert findings[0]["requires_clarification"] is False
    actionable = _actionable_findings(findings)
    assert len(actionable) == 1, "Non-VAGUE lint finding must remain actionable"
