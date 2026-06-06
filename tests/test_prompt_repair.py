"""Tests for pdd.prompt_repair bounded repair loop."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.prompt_repair import (
    PromptRepairConfig,
    _apply_patch,
    _extract_json_array_from_text,
    _validate_proposal,
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


def test_repair_adds_vocabulary_and_reclean(tmp_path: Path) -> None:
    prompt = tmp_path / "vague.prompt"
    prompt.write_text((FIXTURES / "vague_undefined.prompt").read_text(encoding="utf-8"), encoding="utf-8")
    proposals = json.dumps([
        {
            "type": "ADD_VOCABULARY",
            "term": "valid",
            "definition": "valid: passes schema and business rules checks",
            "addresses_issue": "undefined vague term 'valid'",
        },
        {
            "type": "ADD_VOCABULARY",
            "term": "reasonable",
            "definition": "reasonable: completes within 2000 ms on CI hardware",
            "addresses_issue": "undefined vague term 'reasonable'",
        },
        {
            "type": "ADD_VOCABULARY",
            "term": "gracefully",
            "definition": "gracefully: returns HTTP 4xx without raising",
            "addresses_issue": "undefined vague term 'gracefully'",
        },
        {
            "type": "ADD_VOCABULARY",
            "term": "authorized",
            "definition": "authorized: caller holds a valid session token",
            "addresses_issue": "undefined vague term 'authorized'",
        },
        {
            "type": "ADD_VOCABULARY",
            "term": "duplicate",
            "definition": "duplicate: same idempotency key seen within 24h",
            "addresses_issue": "undefined vague term 'duplicate'",
        },
        {
            "type": "ADD_VOCABULARY",
            "term": "active",
            "definition": "active: account status is enabled",
            "addresses_issue": "undefined vague term 'active'",
        },
        {
            "type": "ADD_VOCABULARY",
            "term": "complete",
            "definition": "complete: all required fields are non-empty",
            "addresses_issue": "undefined vague term 'complete'",
        },
    ])

    with patch(
        "pdd.prompt_repair._invoke_repair_llm",
        return_value=(True, proposals, 0.0, "mock"),
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

    partial = json.dumps([
        {
            "type": "ADD_VOCABULARY",
            "term": "valid",
            "definition": "valid: passes validation rules",
            "addresses_issue": "valid",
        }
    ])

    def _fake_llm(**_kwargs):
        calls["count"] += 1
        return True, partial, 0.0, "mock"

    with patch("pdd.prompt_repair._invoke_repair_llm", side_effect=_fake_llm):
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
        "pdd.prompt_repair._invoke_repair_llm",
        return_value=(False, "provider error", 0.0, ""),
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

    with patch("pdd.prompt_repair._invoke_repair_llm", return_value=(True, "[]", 0.0, "mock")):
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

    with patch("pdd.prompt_repair._invoke_repair_llm", return_value=(True, "[]", 0.0, "mock")):
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
    huge_definition = "x" * 5000
    proposals = json.dumps([
        {
            "type": "ADD_VOCABULARY",
            "term": "valid",
            "definition": huge_definition,
            "addresses_issue": "valid",
        }
    ])

    with patch("pdd.prompt_repair._invoke_repair_llm", return_value=(True, proposals, 0.0, "mock")):
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


def test_validate_proposal_rejects_unknown_type() -> None:
    assert _validate_proposal({"type": "FULL_REWRITE"}) is False


def test_apply_patch_adds_contract_skeleton() -> None:
    text = "% Goal\nDo something observable.\n"
    patched = _apply_patch(text, {"type": "ADD_CONTRACT_SKELETON"})
    assert "<contract_rules>" in patched


def test_extract_json_array_from_text() -> None:
    text = 'analysis\n```json\n[{"type": "ADD_VOCABULARY"}]\n```'
    parsed = _extract_json_array_from_text(text)
    assert parsed == [{"type": "ADD_VOCABULARY"}]


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

    with patch("pdd.prompt_repair._invoke_repair_llm", return_value=(False, "", 0, 0)):
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
