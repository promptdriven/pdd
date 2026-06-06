from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.checkup_prompt_main import (
    SourceSetFinding,
    build_prompt_source_set_report,
    run_checkup_prompt,
)
from pdd.commands.checkup import checkup


FIXTURES = Path(__file__).resolve().parent / "fixtures" / "prompt_lint"


def test_build_prompt_source_set_report_clean_fixture() -> None:
    prompt = FIXTURES / "clean.prompt"
    report = build_prompt_source_set_report(
        prompt,
        target=str(prompt),
        project_root=FIXTURES,
    )
    assert report.lint is not None
    assert report.lint.error_count == 0
    assert report.deterministic_exit_code() in {0, 1}


def test_run_checkup_prompt_json_schema() -> None:
    prompt = FIXTURES / "clean.prompt"
    runner = CliRunner()
    result = runner.invoke(
        checkup,
        [str(prompt), "--json"],
        obj={"quiet": True},
    )
    assert result.exit_code in {0, 1}
    payload = json.loads(result.output)
    assert payload["schema"] == "pdd.prompt_source_set_report.v1"
    assert payload["deterministic_exit_code"] in {0, 1}
    assert payload["reports"][0]["schema"] == "pdd.prompt_source_set_report.v1"


def test_run_checkup_prompt_strict_exit_on_warnings() -> None:
    prompt = FIXTURES / "vague_undefined.prompt"
    passed, _message, _cost, _model, exit_code = run_checkup_prompt(
        str(prompt),
        strict=True,
        quiet=True,
        project_root=FIXTURES,
    )
    assert not passed
    assert exit_code == 2


def test_build_prompt_source_set_report_records_contract_under_strict() -> None:
    prompt = FIXTURES / "vague_undefined.prompt"
    report = build_prompt_source_set_report(
        prompt,
        target=str(prompt),
        project_root=FIXTURES,
        strict=True,
    )
    contract_checks = [item for item in report.checks if item["name"] == "contract"]
    assert contract_checks == [{"name": "contract", "status": "fail"}]


def test_run_checkup_prompt_json_includes_contract_check_under_strict() -> None:
    prompt = FIXTURES / "vague_undefined.prompt"
    runner = CliRunner()
    result = runner.invoke(
        checkup,
        [str(prompt), "--strict", "--json"],
        obj={"quiet": True},
    )
    assert result.exit_code == 2
    payload = json.loads(result.output)
    contract_checks = [
        item
        for item in payload["reports"][0]["checks"]
        if item["name"] == "contract"
    ]
    assert contract_checks == [{"name": "contract", "status": "fail"}]


def test_source_set_finding_as_dict_exposes_repair_fields() -> None:
    finding = SourceSetFinding(
        finding_id="contract:foo:0:MISSING_MODAL",
        source_check="contract",
        severity="error",
        file=Path("prompts/foo_python.prompt"),
        code="MISSING_MODAL",
        rule_id="S-001",
        confidence=0.75,
    )
    payload = finding.as_dict()
    assert payload["code"] == "MISSING_MODAL"
    assert payload["rule_id"] == "S-001"
    assert payload["requires_clarification"] is False
    assert payload["confidence"] == 0.75


def test_source_set_finding_flags_vague_terms_for_clarification() -> None:
    finding = SourceSetFinding(
        finding_id="lint:foo:0:VAGUE_TERM_UNDEFINED",
        source_check="lint",
        severity="error",
        file=Path("prompts/foo_python.prompt"),
        code="VAGUE_TERM_UNDEFINED",
    )
    assert finding.requires_clarification is True
    assert finding.as_dict()["requires_clarification"] is True
    # Confidence stays absent unless explicitly provided.
    assert "confidence" not in finding.as_dict()


def test_report_json_findings_include_clarification_flag() -> None:
    prompt = FIXTURES / "vague_undefined.prompt"
    report = build_prompt_source_set_report(
        prompt,
        target=str(prompt),
        project_root=FIXTURES,
        strict=True,
    )
    vague = [
        finding
        for finding in report.findings
        if "VAGUE" in finding.code.upper()
    ]
    assert vague, "expected vague-term findings in the fixture"
    assert all(finding.as_dict()["requires_clarification"] for finding in vague)
    assert all("code" in finding.as_dict() for finding in report.findings)


def test_build_prompt_source_set_report_coverage_anchored_to_project_root(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Regression: coverage dirs must be resolved relative to project_root, not
    # the process cwd.  Invoke from outside the project dir to verify.
    project = tmp_path / "myproject"
    project.mkdir()
    prompts_dir = project / "prompts"
    prompts_dir.mkdir()
    (project / "user_stories").mkdir()
    (project / "tests").mkdir()

    # Minimal prompt with a contract_rules section so coverage is attempted.
    prompt = prompts_dir / "simple_python.prompt"
    prompt.write_text(
        "% Simple prompt\n<contract_rules>\nR-001: always return something\n</contract_rules>\n",
        encoding="utf-8",
    )

    monkeypatch.chdir(tmp_path)  # cwd is OUTSIDE the project
    report = build_prompt_source_set_report(
        prompt,
        target="simple",
        project_root=project,
    )

    # Coverage must have run against project/user_stories and project/tests,
    # not tmp_path/user_stories which does not exist.
    assert report.coverage is not None
    # No filesystem error — the correct dirs were found even from a foreign cwd.
    assert report.coverage.error is None


def test_build_prompt_source_set_report_respects_pdd_user_stories_dir(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Regression: PDD_USER_STORIES_DIR must be honoured by checkup, consistent
    # with pdd change/generate/test which all read the same env var.
    project = tmp_path / "proj"
    project.mkdir()
    # Intentionally do NOT create project/user_stories — if the env var is
    # silently ignored the scanner would fall back there and find nothing.
    (project / "tests").mkdir()

    prompt = project / "foo_python.prompt"
    prompt.write_text(
        "% Foo\n<contract_rules>\nR-001: do something\n</contract_rules>\n",
        encoding="utf-8",
    )

    # Place a story in the custom dir that covers R-001.  Stories with no
    # pdd-story-prompts metadata apply to all prompts in the evaluated set.
    custom_stories = tmp_path / "custom_stories"
    custom_stories.mkdir()
    (custom_stories / "story__r001.md").write_text(
        "## Story\nAs a user I want foo.\n\n## Covers\nR-001\n",
        encoding="utf-8",
    )

    monkeypatch.setenv("PDD_USER_STORIES_DIR", str(custom_stories))
    report = build_prompt_source_set_report(
        prompt,
        target="foo",
        project_root=project,
    )
    assert report.coverage is not None
    assert report.coverage.error is None
    # If the env var was honoured the story in custom_stories was scanned and
    # R-001 is story-only (not unchecked).  If ignored, project/user_stories
    # does not exist so the rule stays unchecked — the two paths are distinct.
    from pdd.coverage_contracts import STATUS_UNCHECKED
    rule_statuses = {r.rule_id: r.status for r in report.coverage.rules}
    assert rule_statuses.get("R-001") != STATUS_UNCHECKED, (
        "R-001 was unchecked — PDD_USER_STORIES_DIR was not honoured"
    )


def test_checkup_issue_url_still_uses_agentic_path() -> None:
    runner = CliRunner()
    with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
        run_checkup.return_value = (True, "ok", 0.0, "codex")
        result = runner.invoke(
            checkup,
            ["https://github.com/org/repo/issues/123"],
            obj={"quiet": True},
        )
    assert result.exit_code == 0
    run_checkup.assert_called_once()
