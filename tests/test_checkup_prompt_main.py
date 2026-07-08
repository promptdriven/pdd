from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.checkup_prompt_main import (
    PromptSourceSetReport,
    SourceSetFinding,
    build_prompt_source_set_report,
    run_checkup_prompt,
)
from pdd.checkup_interactive_main import filter_interactive_findings
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


def test_checkup_prompt_directory_e2e_smoke(tmp_path: Path, monkeypatch) -> None:
    """CI-safe e2e smoke for the wired ``pdd checkup <prompt-dir>`` path."""
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    for name in ("alpha_python.prompt", "beta_python.prompt"):
        (prompts_dir / name).write_text(
            "<pdd-reason>Small deterministic smoke prompt.</pdd-reason>\n"
            "% Goal\n"
            "Write a tiny Python helper.\n\n"
            "% Requirements\n"
            "- The implementation MUST return an integer.\n",
            encoding="utf-8",
        )

    monkeypatch.chdir(tmp_path)
    result = CliRunner().invoke(
        checkup,
        ["prompts"],
        obj={"quiet": False},
        catch_exceptions=False,
    )

    assert result.exit_code == 0, result.output
    assert "Checkup: 2 prompt(s) under prompts/" in result.output
    assert "Summary:" in result.output
    assert "Decision: all prompts can continue" in result.output


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
    assert finding.as_dict()["clarification_reason"]
    # Confidence stays absent unless explicitly provided.
    assert "confidence" not in finding.as_dict()


@pytest.mark.parametrize(
    ("code", "source_check", "rule_id"),
    [
        ("DUPLICATE_ID", "contract", "R1"),
        ("story_only_ambiguous", "coverage", "R2"),
        ("waiver_not_allowed", "gate", "R3"),
        ("MALFORMED_WAIVER", "gate", "W1"),
    ],
)
def test_source_set_finding_clarification_reason_for_documented_categories(
    code: str,
    source_check: str,
    rule_id: str,
) -> None:
    finding = SourceSetFinding(
        finding_id=f"{source_check}:foo:0:{code}",
        source_check=source_check,
        severity="warn",
        file=Path("prompts/foo_python.prompt"),
        code=code,
        rule_id=rule_id,
    )

    payload = finding.as_dict()
    assert payload["requires_clarification"] is True
    assert payload["clarification_reason"]


def test_explicit_interactive_routes_all_clarification_categories() -> None:
    prompt = Path("prompts/foo_python.prompt")
    findings = [
        SourceSetFinding(
            finding_id=f"f-{index}",
            source_check=source,
            severity="warn",
            file=prompt,
            code=code,
        )
        for index, (source, code) in enumerate(
            [
                ("lint", "VAGUE_TERM_UNDEFINED"),
                ("contract", "DUPLICATE_ID"),
                ("coverage", "story_only_ambiguous"),
                ("gate", "waiver_not_allowed"),
            ]
        )
    ]
    report = PromptSourceSetReport(
        prompt_path=prompt,
        project_root=Path("."),
        target=str(prompt),
        findings=findings,
    )

    routed = filter_interactive_findings(report, explicit_interactive=False)

    assert [finding.finding_id for finding in routed] == [
        "f-0",
        "f-1",
        "f-2",
        "f-3",
    ]


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
    assert all(finding.as_dict()["clarification_reason"] for finding in vague)
    assert all("code" in finding.as_dict() for finding in report.findings)
    assert all("clarification_reason" in finding.as_dict() for finding in report.findings)


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


def test_checkup_prompt_target_runs_repair_then_full_recheck(tmp_path: Path) -> None:
    """Issue #1422: failed prompt checkup → repair → full re-check."""
    from pdd.prompt_repair import RepairResult

    prompt = tmp_path / "sample_python.prompt"
    prompt.write_text("% Sample\n", encoding="utf-8")

    failing_report = type(
        "Report",
        (),
        {
            "status": "warn",
            "passed": False,
            "as_dict": lambda self: {
                "schema": "pdd.prompt_source_set_report.v1",
                "status": "warn",
                "target": str(prompt),
                "findings": [
                    {
                        "source_check": "coverage",
                        "severity": "warn",
                        "code": "unchecked",
                        "message": "R1 unchecked",
                    }
                ],
            },
            "recommended_actions": lambda self: ["Add coverage for R1."],
        },
    )()

    with (
        patch(
            "pdd.commands.checkup.run_checkup_prompt",
            side_effect=[
                (False, "check failed", 0.0, "mock", 1),
                (True, "check passed", 0.0, "mock", 0),
            ],
        ) as mock_checkup,
        patch(
            "pdd.commands.checkup.build_prompt_source_set_report",
            return_value=failing_report,
        ) as mock_build_report,
        patch(
            "pdd.commands.checkup.run_prompt_repair_loop",
            return_value=RepairResult(
                success=True,
                rounds_used=1,
                repair_skipped=False,
                message="repaired",
            ),
        ) as mock_repair,
    ):
        runner = CliRunner()
        result = runner.invoke(
            checkup,
            [str(prompt), "--prompt-repair", "best-effort"],
            obj={"quiet": True, "verbose": False},
        )

    assert result.exit_code == 0
    assert mock_checkup.call_count == 2
    mock_build_report.assert_called_once()
    mock_repair.assert_called_once()
    repair_context = mock_repair.call_args.kwargs["context"]
    assert "source_set_report" in repair_context
    assert "recommended_actions" in repair_context


def test_source_set_repair_smoke_zero_lint_contract_fix(tmp_path: Path) -> None:
    """End-to-end smoke: zero lint + contract MISSING_MODAL triggers source-set repair.

    Uses the real build_prompt_source_set_report; only the LLM call is mocked.
    Verifies: initial state has zero lint errors but actionable contract findings;
    the repair path is invoked with source_set_report context; the file is updated;
    the post-repair recheck shows fewer (or zero) contract findings.
    """
    original = (FIXTURES / "clean.prompt").read_text(encoding="utf-8")
    prompt = tmp_path / "contract_smoke_python.prompt"
    prompt.write_text(original, encoding="utf-8")

    # Confirm fixture preconditions: zero lint errors, has contract MISSING_MODAL warnings.
    initial_report = build_prompt_source_set_report(
        prompt, target=str(prompt), project_root=tmp_path
    )
    assert initial_report.lint is not None
    assert initial_report.lint.error_count == 0, "fixture must have zero lint errors"
    initial_contract = [f for f in initial_report.findings if f.source_check == "contract"]
    assert len(initial_contract) > 0, "fixture must have contract MISSING_MODAL warnings"
    assert initial_report.status != "pass", "fixture must start with non-pass status"

    # Repaired prompt: add MUST to each contract rule so MISSING_MODAL is resolved.
    repaired = (
        original
        .replace(
            "1. The function returns an integer exit code of 0 on success, 1 on failure.",
            "1. The function MUST return an integer exit code of 0 on success, 1 on failure.",
        )
        .replace(
            "2. If the input file does not exist, raises FileNotFoundError.",
            "2. If the input file does not exist, the function MUST raise FileNotFoundError.",
        )
        .replace(
            "3. Writes output to the path specified by the --output flag.",
            "3. The function MUST write output to the path specified by the --output flag.",
        )
        .replace(
            "4. Logs the request ID to stdout before processing begins.",
            "4. The function MUST log the request ID to stdout before processing begins.",
        )
    )

    with patch("pdd.prompt_repair.change", return_value=(repaired, 0.02, "test-model")) as mock_change:
        runner = CliRunner()
        cli_result = runner.invoke(
            checkup,
            [str(prompt), "--prompt-repair", "best-effort"],
            obj={"quiet": True, "verbose": False},
        )

    # LLM was called exactly once (one repair round).
    mock_change.assert_called_once()
    # The repair brief included the structured source-set report as context.
    call_kwargs = mock_change.call_args.kwargs
    assert "source_set_report" in call_kwargs.get("input_code", ""), (
        "change() must receive source_set_report context, not lint-only"
    )

    # File was updated with the repaired content.
    assert prompt.read_text(encoding="utf-8") == repaired, "prompt file must be rewritten"

    # Post-repair recheck: contract findings reduced (MUST added resolves MISSING_MODAL).
    final_report = build_prompt_source_set_report(
        prompt, target=str(prompt), project_root=tmp_path
    )
    final_contract = [f for f in final_report.findings if f.source_check == "contract"]
    assert len(final_contract) < len(initial_contract), (
        f"contract findings must decrease after repair: {len(initial_contract)} → {len(final_contract)}"
    )

    assert cli_result.exit_code in {0, 1}


def test_checkup_cli_strict_repair_blocks_on_remaining_findings(tmp_path: Path) -> None:
    """--prompt-repair strict must yield non-zero exit when findings persist after repair.

    Regression target: the local checkup.py repair path must propagate a failed
    recheck exit code, and run_prompt_repair_loop must be called with mode='strict'.
    """
    from pdd.prompt_repair import RepairResult

    prompt = tmp_path / "sample_python.prompt"
    prompt.write_text("% Sample\n", encoding="utf-8")

    failing_report = type(
        "Report",
        (),
        {
            "status": "warn",
            "as_dict": lambda self: {
                "schema": "pdd.prompt_source_set_report.v1",
                "status": "warn",
                "target": str(prompt),
                "findings": [{"source_check": "contract", "severity": "warn",
                               "code": "MISSING_MODAL", "message": "rule lacks MUST"}],
            },
            "recommended_actions": lambda self: [],
        },
    )()

    with (
        patch(
            "pdd.commands.checkup.run_checkup_prompt",
            side_effect=[
                (False, "initial check failed", 0.0, "mock", 1),   # first check fails → triggers repair
                (False, "recheck still failing", 0.0, "mock", 1),  # recheck after repair also fails
            ],
        ),
        patch(
            "pdd.commands.checkup.build_prompt_source_set_report",
            return_value=failing_report,
        ),
        patch(
            "pdd.commands.checkup.run_prompt_repair_loop",
            return_value=RepairResult(
                success=False,
                rounds_used=1,
                repair_skipped=False,
                message="findings remain",
            ),
        ) as mock_repair,
    ):
        runner = CliRunner()
        result = runner.invoke(
            checkup,
            [str(prompt), "--prompt-repair", "strict"],
            obj={"quiet": True, "verbose": False},
        )

    # run_prompt_repair_loop was invoked with mode="strict"
    mock_repair.assert_called_once()
    repair_config = mock_repair.call_args.args[1]
    assert repair_config.mode == "strict", (
        f"PromptRepairConfig.mode must be 'strict', got {repair_config.mode!r}"
    )

    # The final exit code is non-zero — recheck after repair still failed
    assert result.exit_code != 0, (
        "CLI must propagate non-zero exit when recheck fails after strict repair"
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


@pytest.mark.timeout(120)
def test_source_set_repair_cli_smoke_script_runs_without_pythonpath() -> None:
    """Regression: smoke script must not require callers to set PYTHONPATH."""
    import os
    import subprocess
    import sys

    repo_root = Path(__file__).resolve().parents[1]
    script = repo_root / "tests" / "scripts" / "source_set_repair_cli_smoke.py"
    env = os.environ.copy()
    env.pop("PYTHONPATH", None)

    proc = subprocess.run(
        [sys.executable, str(script)],
        cwd=repo_root,
        env=env,
        capture_output=True,
        text=True,
        check=False,
        timeout=110,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "PASS" in proc.stdout
    assert "AttributeError" not in proc.stderr
