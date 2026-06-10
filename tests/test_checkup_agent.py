"""Tests for CheckupAgent, CheckupSession, CheckupTool, and checkup_planner.

All tests are offline — no live LLM or network calls.
``LLMPlanner`` is tested via an injected fake ``_call`` callable.
"""

from __future__ import annotations

from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.checkup_agent import (
    AgentEvent,
    CheckupAgent,
    RecordingCheckupSession,
    TerminalCheckupSession,
    discover_prompt_files,
    run_checkup_directory,
)
from pdd.checkup_planner import DeterministicPlanner, LLMPlanner, Plan, make_planner
from pdd.checkup_prompt_main import PromptSourceSetReport, SourceSetFinding
from pdd.checkup_tools import (
    ALL_TOOL_NAMES,
    ALL_TOOLS,
    ContractTool,
    CoverageTool,
    DriftTool,
    GateTool,
    LintTool,
    SnapshotTool,
    ToolResult,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------


@pytest.fixture
def minimal_report(tmp_path: Path) -> PromptSourceSetReport:
    """A PromptSourceSetReport with no findings and all checks skipped."""
    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("% Test prompt\nDo something.\n", encoding="utf-8")
    return PromptSourceSetReport(
        prompt_path=prompt_file,
        project_root=tmp_path,
        target=str(prompt_file),
        findings=[],
        checks=[{"name": t, "status": "skip"} for t in ALL_TOOL_NAMES],
    )


@pytest.fixture
def report_with_lint_finding(tmp_path: Path) -> PromptSourceSetReport:
    """A report that has one lint finding."""
    prompt_file = tmp_path / "vague.prompt"
    prompt_file.write_text("% Vague\nDo something valid.\n", encoding="utf-8")
    finding = SourceSetFinding(
        finding_id="lint-vague-001",
        source_check="lint",
        severity="warn",
        file=prompt_file,
        line="3",
        message="Vague term 'valid'",
        evidence="valid",
        recommended_action="Replace 'valid' with a specific criterion",
        fix_command="",
        code="VAGUE_TERM",
    )
    return PromptSourceSetReport(
        prompt_path=prompt_file,
        project_root=tmp_path,
        target=str(prompt_file),
        findings=[finding],
        checks=[
            {"name": "lint", "status": "warn"},
            *[{"name": t, "status": "skip"} for t in ALL_TOOL_NAMES if t != "lint"],
        ],
    )


# ---------------------------------------------------------------------------
# checkup_tools
# ---------------------------------------------------------------------------


class TestToolExtract:
    def test_lint_tool_extracts_status(self, minimal_report):
        result = LintTool().extract(minimal_report)
        assert result.check_name == "lint"
        assert result.status == "skip"
        assert result.findings == []

    def test_lint_tool_extracts_findings(self, report_with_lint_finding):
        result = LintTool().extract(report_with_lint_finding)
        assert result.status == "warn"
        assert len(result.findings) == 1
        assert result.findings[0].source_check == "lint"

    def test_contract_tool_skips_when_no_contract(self, minimal_report):
        result = ContractTool().extract(minimal_report)
        assert result.status == "skip"

    def test_coverage_tool(self, minimal_report):
        result = CoverageTool().extract(minimal_report)
        assert result.check_name == "coverage"

    def test_gate_tool(self, minimal_report):
        result = GateTool().extract(minimal_report)
        assert result.check_name == "gate"

    def test_snapshot_tool(self, minimal_report):
        result = SnapshotTool().extract(minimal_report)
        assert result.check_name == "snapshot"

    def test_drift_tool(self, minimal_report):
        result = DriftTool().extract(minimal_report)
        assert result.check_name == "drift"

    def test_all_tools_present(self):
        assert set(ALL_TOOLS.keys()) == set(ALL_TOOL_NAMES)

    def test_tool_result_is_clean_for_pass(self, minimal_report):
        minimal_report.checks = [{"name": "lint", "status": "pass"}]
        result = LintTool().extract(minimal_report)
        assert result.is_clean

    def test_tool_result_is_not_clean_for_fail(self, minimal_report):
        minimal_report.checks = [{"name": "lint", "status": "fail"}]
        result = LintTool().extract(minimal_report)
        assert not result.is_clean

    def test_tool_result_has_findings_false_when_empty(self, minimal_report):
        result = LintTool().extract(minimal_report)
        assert not result.has_findings


# ---------------------------------------------------------------------------
# DeterministicPlanner
# ---------------------------------------------------------------------------


class TestDeterministicPlanner:
    def test_returns_all_tools_in_order(self, tmp_path):
        p = DeterministicPlanner()
        plan = p.suggest(tmp_path / "x.prompt", list(ALL_TOOL_NAMES))
        assert plan.tools == list(ALL_TOOL_NAMES)

    def test_filters_to_available_tools(self, tmp_path):
        p = DeterministicPlanner()
        plan = p.suggest(tmp_path / "x.prompt", ["lint", "gate"])
        assert set(plan.tools) == {"lint", "gate"}

    def test_plan_has_rationale(self, tmp_path):
        p = DeterministicPlanner()
        plan = p.suggest(tmp_path / "x.prompt", ["lint"])
        assert plan.rationale

    def test_plan_display_lines(self, tmp_path):
        p = DeterministicPlanner()
        plan = p.suggest(tmp_path / "x.prompt", ["lint", "contract"])
        lines = plan.display_lines()
        assert any("lint" in line for line in lines)
        assert any("contract" in line for line in lines)


# ---------------------------------------------------------------------------
# LLMPlanner (with fake _call — no network)
# ---------------------------------------------------------------------------


class TestLLMPlanner:
    def _make_fake_call(self, tools: list[str], rationale: str = "test"):
        def fake_call(prompt_text, available_tools):
            return {"tools": tools, "rationale": rationale}

        return fake_call

    def test_returns_llm_suggested_tools(self, tmp_path):
        prompt_file = tmp_path / "x.prompt"
        prompt_file.write_text("% Test\nDo something.\n", encoding="utf-8")
        planner = LLMPlanner(_call=self._make_fake_call(["lint", "contract"]))
        plan = planner.suggest(prompt_file, list(ALL_TOOL_NAMES), "prompt text")
        assert plan.tools[:2] == ["lint", "contract"]

    def test_appends_missing_tools_at_end(self, tmp_path):
        prompt_file = tmp_path / "x.prompt"
        prompt_file.write_text("% Test\nDo something.\n", encoding="utf-8")
        planner = LLMPlanner(_call=self._make_fake_call(["lint"]))
        plan = planner.suggest(prompt_file, list(ALL_TOOL_NAMES), "prompt text")
        # lint is first, remaining tools appended
        assert plan.tools[0] == "lint"
        assert set(plan.tools) == set(ALL_TOOL_NAMES)

    def test_falls_back_on_exception(self, tmp_path):
        prompt_file = tmp_path / "x.prompt"
        prompt_file.write_text("% Test\n", encoding="utf-8")

        def bad_call(prompt_text, available_tools):
            raise RuntimeError("LLM down")

        planner = LLMPlanner(_call=bad_call)
        plan = planner.suggest(prompt_file, list(ALL_TOOL_NAMES), "text")
        # Fallback to deterministic
        assert set(plan.tools) == set(ALL_TOOL_NAMES)

    def test_falls_back_when_empty_tool_list(self, tmp_path):
        prompt_file = tmp_path / "x.prompt"
        prompt_file.write_text("% Test\n", encoding="utf-8")
        planner = LLMPlanner(_call=self._make_fake_call([]))
        plan = planner.suggest(prompt_file, list(ALL_TOOL_NAMES), "text")
        assert set(plan.tools) == set(ALL_TOOL_NAMES)

    def test_falls_back_on_invalid_tool_name(self, tmp_path):
        """A hallucinated tool name must degrade to the deterministic plan,
        not crash with ValueError from Plan.__post_init__."""
        prompt_file = tmp_path / "x.prompt"
        prompt_file.write_text("% Test\n", encoding="utf-8")
        planner = LLMPlanner(
            _call=self._make_fake_call(["lint", "not_a_real_tool"])
        )
        plan = planner.suggest(prompt_file, list(ALL_TOOL_NAMES), "text")
        assert set(plan.tools) == set(ALL_TOOL_NAMES)

    def test_reads_file_when_no_prompt_text(self, tmp_path):
        prompt_file = tmp_path / "x.prompt"
        prompt_file.write_text("% Test\n", encoding="utf-8")
        received = []

        def capturing_call(prompt_text, available_tools):
            received.append(prompt_text)
            return {"tools": ["lint"], "rationale": "ok"}

        planner = LLMPlanner(_call=capturing_call)
        planner.suggest(prompt_file, list(ALL_TOOL_NAMES))
        assert received and "% Test" in received[0]

    def test_falls_back_when_file_missing(self, tmp_path):
        missing = tmp_path / "missing.prompt"
        planner = LLMPlanner(_call=self._make_fake_call(["lint"]))
        plan = planner.suggest(missing, list(ALL_TOOL_NAMES))
        assert set(plan.tools) == set(ALL_TOOL_NAMES)


class TestDefaultLLMCallParsing:
    """`_default_llm_call` must parse both pydantic and dict llm_invoke results.

    Regression guard: a real llm_invoke success with output_pydantic returns a
    pydantic instance (no `.get`), which previously raised AttributeError and
    silently degraded the LLM planner to deterministic for the wrong reason.
    All llm_invoke calls are mocked — no network.
    """

    def test_parses_pydantic_result(self):
        from pdd import checkup_planner

        class _FakePlan:
            # Mimics a pydantic instance: attribute access, no `.get`.
            tools = ["contract", "lint"]
            rationale = "pydantic path"

        # llm_invoke is imported inside the function from pdd.llm_invoke.
        with patch("pdd.llm_invoke.llm_invoke", return_value={"result": _FakePlan()}):
            out = checkup_planner._default_llm_call("some prompt", list(ALL_TOOL_NAMES))
        assert out["tools"] == ["contract", "lint"]
        assert out["rationale"] == "pydantic path"

    def test_parses_dict_result(self):
        from pdd import checkup_planner

        with patch(
            "pdd.llm_invoke.llm_invoke",
            return_value={"result": {"tools": ["gate", "drift"], "rationale": "dict path"}},
        ):
            out = checkup_planner._default_llm_call("some prompt", list(ALL_TOOL_NAMES))
        assert out["tools"] == ["gate", "drift"]
        assert out["rationale"] == "dict path"

    def test_drops_hallucinated_tools(self):
        from pdd import checkup_planner

        with patch(
            "pdd.llm_invoke.llm_invoke",
            return_value={"result": {"tools": ["lint", "not_a_tool"], "rationale": "x"}},
        ):
            out = checkup_planner._default_llm_call("p", list(ALL_TOOL_NAMES))
        assert out["tools"] == ["lint"]


# ---------------------------------------------------------------------------
# Plan
# ---------------------------------------------------------------------------


class TestPlan:
    def test_rejects_unknown_tool(self):
        with pytest.raises(ValueError, match="Unknown tool"):
            Plan(tools=["lint", "not_a_real_tool"])

    def test_display_lines_includes_rationale(self):
        plan = Plan(tools=["lint"], rationale="Focus on quality.")
        lines = plan.display_lines()
        assert any("Focus on quality" in line for line in lines)


# ---------------------------------------------------------------------------
# make_planner
# ---------------------------------------------------------------------------


def test_make_planner_deterministic():
    p = make_planner("deterministic")
    assert isinstance(p, DeterministicPlanner)


def test_make_planner_llm():
    p = make_planner("llm")
    assert isinstance(p, LLMPlanner)


def test_make_planner_invalid():
    with pytest.raises(ValueError, match="Unknown planner"):
        make_planner("magic")


# ---------------------------------------------------------------------------
# RecordingCheckupSession
# ---------------------------------------------------------------------------


class TestRecordingCheckupSession:
    def test_records_events(self):
        session = RecordingCheckupSession()
        session.on_event(AgentEvent("plan_ready", {}))
        session.on_event(AgentEvent("session_done", {}))
        assert len(session.events) == 2

    def test_events_of_kind(self):
        session = RecordingCheckupSession()
        session.on_event(AgentEvent("tool_start", {"tool": "lint"}))
        session.on_event(AgentEvent("tool_done", {"tool": "lint"}))
        session.on_event(AgentEvent("plan_ready", {}))
        starts = session.events_of_kind("tool_start")
        assert len(starts) == 1

    def test_confirm_plan_returns_plan_when_confirm_true(self, tmp_path):
        session = RecordingCheckupSession(confirm=True)
        plan = Plan(tools=["lint"], rationale="test")
        result = session.confirm_plan(plan)
        assert result is plan

    def test_confirm_plan_returns_none_when_confirm_false(self, tmp_path):
        session = RecordingCheckupSession(confirm=False)
        plan = Plan(tools=["lint"], rationale="test")
        result = session.confirm_plan(plan)
        assert result is None

    def test_confirm_plan_returns_custom_plan(self, tmp_path):
        custom = Plan(tools=["gate"], rationale="custom")
        session = RecordingCheckupSession(custom_plan=custom)
        plan = Plan(tools=["lint"], rationale="original")
        result = session.confirm_plan(plan)
        assert result is custom


# ---------------------------------------------------------------------------
# CheckupAgent integration (no TTY, no LLM)
# ---------------------------------------------------------------------------


class TestCheckupAgent:
    def test_agent_emits_plan_ready_event(self, tmp_path):
        prompt_file = tmp_path / "test.prompt"
        prompt_file.write_text("% Test\nDo something.\n", encoding="utf-8")

        session = RecordingCheckupSession()
        planner = DeterministicPlanner()

        with patch(
            "pdd.checkup_agent.build_prompt_source_set_report"
        ) as mock_report:
            mock_report.return_value = PromptSourceSetReport(
                prompt_path=prompt_file,
                project_root=tmp_path,
                target=str(prompt_file),
                findings=[],
                checks=[{"name": t, "status": "skip"} for t in ALL_TOOL_NAMES],
            )
            agent = CheckupAgent(planner, session)
            agent.run(str(prompt_file), project_root=tmp_path)

        kinds = [e.kind for e in session.events]
        assert "plan_ready" in kinds
        assert "plan_confirmed" in kinds
        assert "session_done" in kinds

    def test_agent_aborts_when_plan_rejected(self, tmp_path):
        prompt_file = tmp_path / "test.prompt"
        prompt_file.write_text("% Test\n", encoding="utf-8")

        session = RecordingCheckupSession(confirm=False)
        planner = DeterministicPlanner()
        agent = CheckupAgent(planner, session)

        result = agent.run(str(prompt_file), project_root=tmp_path, quiet=True)
        assert "aborted" in result[0].lower()
        # No tool_start events should be emitted
        assert not session.events_of_kind("tool_start")

    def test_agent_respects_custom_plan(self, tmp_path):
        prompt_file = tmp_path / "test.prompt"
        prompt_file.write_text("% Test\n", encoding="utf-8")

        custom_plan = Plan(tools=["lint"], rationale="only lint")
        # Custom plan only applies in interactive mode (where confirm_plan runs).
        session = RecordingCheckupSession(custom_plan=custom_plan)
        planner = DeterministicPlanner()

        with patch(
            "pdd.checkup_agent.build_prompt_source_set_report"
        ) as mock_report:
            mock_report.return_value = PromptSourceSetReport(
                prompt_path=prompt_file,
                project_root=tmp_path,
                target=str(prompt_file),
                findings=[],
                checks=[{"name": "lint", "status": "pass"}],
            )
            agent = CheckupAgent(planner, session)
            agent.run(
                str(prompt_file),
                project_root=tmp_path,
                quiet=True,
                mode="interactive",
            )

        tool_starts = session.events_of_kind("tool_start")
        tool_names = [e.data["tool"] for e in tool_starts]
        assert tool_names == ["lint"]

    def test_agent_raises_for_missing_file(self, tmp_path):
        session = RecordingCheckupSession()
        planner = DeterministicPlanner()
        agent = CheckupAgent(planner, session)

        with pytest.raises(Exception):
            agent.run(str(tmp_path / "nonexistent.prompt"), project_root=tmp_path)

    def test_agent_processes_lint_finding(self, tmp_path):
        prompt_file = tmp_path / "vague.prompt"
        prompt_file.write_text("% Vague\nDo something valid.\n", encoding="utf-8")
        # code contains VAGUE → requires_clarification=True → medium risk.
        finding = SourceSetFinding(
            finding_id="lint-v-001",
            source_check="lint",
            severity="warn",
            file=prompt_file,
            line="2",
            message="Vague term 'valid'",
            evidence="requirements",
            recommended_action="Specify criterion",
            fix_command="",
            code="VAGUE_TERM",
        )

        session = RecordingCheckupSession()
        planner = DeterministicPlanner()

        with patch(
            "pdd.checkup_agent.build_prompt_source_set_report"
        ) as mock_report:
            mock_report.return_value = PromptSourceSetReport(
                prompt_path=prompt_file,
                project_root=tmp_path,
                target=str(prompt_file),
                findings=[finding],
                checks=[{"name": "lint", "status": "warn"}],
            )
            agent = CheckupAgent(planner, session)
            msg, cost, model = agent.run(
                str(prompt_file), project_root=tmp_path, quiet=True, mode="review"
            )

        assert "complete" in msg.lower()
        done = session.events_of_kind("session_done")[0]
        acc = done.data["accounting"]
        assert acc["total"] == 1
        # vague term is medium risk → saved for review, not skipped or applied
        assert acc["saved_for_review"] == 1
        assert acc["skipped_by_user"] == 0
        assert acc["fixed_automatically"] == 0
        # legacy keys retained for back-compat
        assert done.data["total_findings"] == 1


# ---------------------------------------------------------------------------
# CLI flag: --planner (via Click test client)
# ---------------------------------------------------------------------------


def test_cli_planner_flag_invalid(tmp_path):
    """--planner with an invalid value is caught by Click's Choice type."""
    from click.testing import CliRunner

    from pdd.commands.checkup import checkup

    runner = CliRunner()
    result = runner.invoke(checkup, ["--interactive", "--planner", "magic", "x.prompt"])
    assert result.exit_code != 0
    assert "invalid" in result.output.lower() or "error" in result.output.lower()


def test_cli_planner_without_interactive_runs_review_mode(tmp_path):
    """--planner without --interactive runs the agent in non-interactive review mode."""
    from click.testing import CliRunner

    from pdd.commands.checkup import checkup

    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("% Test\nDo something.\n", encoding="utf-8")

    runner = CliRunner()
    with patch("pdd.checkup_agent.CheckupAgent.run") as mock_run:
        mock_run.return_value = ("done", 0.0, "")
        result = runner.invoke(
            checkup,
            ["--planner", "deterministic", str(prompt_file)],
            catch_exceptions=False,
        )
    mock_run.assert_called_once()
    # review mode: non-interactive, not auto
    assert mock_run.call_args.kwargs.get("mode") == "review"
    assert result.exit_code == 0


# ---------------------------------------------------------------------------
# Auto mode and interactive↔auto switching
# ---------------------------------------------------------------------------


def _low_risk_report(tmp_path: Path, n: int = 2) -> PromptSourceSetReport:
    """A report with low-risk lint findings (mechanical, not vague/clarification)."""
    prompt_file = tmp_path / "style.prompt"
    prompt_file.write_text("% Style\nDo something.\n", encoding="utf-8")
    findings = [
        SourceSetFinding(
            finding_id=f"lint-s-{i:03d}",
            source_check="lint",
            severity="warn",
            file=prompt_file,
            line=str(i + 1),
            message=f"Style issue #{i}",
            evidence="prose",
            recommended_action="Tidy wording",
            fix_command="",
            code=f"STYLE_{i}",  # no VAGUE marker → requires_clarification stays False
        )
        for i in range(n)
    ]
    return PromptSourceSetReport(
        prompt_path=prompt_file,
        project_root=tmp_path,
        target=str(prompt_file),
        findings=findings,
        checks=[{"name": "lint", "status": "warn"}],
    )


def _medium_report(tmp_path: Path, n: int = 2) -> PromptSourceSetReport:
    """A report with medium-risk vague-term findings (saved for review)."""
    prompt_file = tmp_path / "vague.prompt"
    prompt_file.write_text("% Vague\n", encoding="utf-8")
    findings = [
        SourceSetFinding(
            finding_id=f"lint-v-{i:03d}",
            source_check="lint",
            severity="warn",
            file=prompt_file,
            line=str(i + 1),
            message=f'Vague term "term{i}" used in [requirements]',
            evidence="requirements",
            recommended_action="Define in <vocabulary>",
            fix_command="",
            code="VAGUE_TERM_UNDEFINED",
        )
        for i in range(n)
    ]
    return PromptSourceSetReport(
        prompt_path=prompt_file,
        project_root=tmp_path,
        target=str(prompt_file),
        findings=findings,
        checks=[{"name": "lint", "status": "warn"}],
    )


class TestAutoMode:
    def test_auto_mode_saves_medium_risk_for_review(self, tmp_path):
        """Auto mode never fabricates vague-term definitions — it saves them."""
        report = _medium_report(tmp_path, n=3)
        session = RecordingCheckupSession()
        planner = DeterministicPlanner()

        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            agent = CheckupAgent(planner, session)
            msg, _, _ = agent.run(
                str(report.prompt_path), project_root=tmp_path, quiet=True, auto=True
            )

        assert "complete" in msg.lower()
        acc = session.events_of_kind("session_done")[0].data["accounting"]
        assert acc["saved_for_review"] == 3
        assert acc["fixed_automatically"] == 0

    def test_auto_mode_applies_low_risk_when_apply(self, tmp_path):
        """Low-risk fixes are auto-applied (fixed_automatically) when --apply."""
        report = _low_risk_report(tmp_path, n=2)
        session = RecordingCheckupSession()
        planner = DeterministicPlanner()

        with patch(
            "pdd.checkup_agent.build_prompt_source_set_report", return_value=report
        ), patch(
            "pdd.checkup_agent.apply_approved_patches", return_value=0
        ) as mock_apply:
            agent = CheckupAgent(planner, session)
            agent.run(
                str(report.prompt_path),
                project_root=tmp_path,
                quiet=True,
                auto=True,
                apply=True,
            )

        mock_apply.assert_called_once()
        acc = session.events_of_kind("session_done")[0].data["accounting"]
        assert acc["fixed_automatically"] == 2
        assert acc["patches_applied"] == 2

    def test_auto_apply_dry_run_counts_low_risk_as_queued(self, tmp_path):
        """Preview validates low-risk patches but must not report applied fixes."""
        report = _low_risk_report(tmp_path, n=2)
        session = RecordingCheckupSession()
        planner = DeterministicPlanner()

        with patch(
            "pdd.checkup_agent.build_prompt_source_set_report", return_value=report
        ), patch(
            "pdd.checkup_agent.apply_approved_patches", return_value=0
        ) as mock_apply:
            agent = CheckupAgent(planner, session)
            agent.run(
                str(report.prompt_path),
                project_root=tmp_path,
                quiet=True,
                auto=True,
                apply=True,
                dry_run=True,
            )

        mock_apply.assert_called_once()
        assert mock_apply.call_args.kwargs["dry_run"] is True
        done = session.events_of_kind("session_done")[0].data
        acc = done["accounting"]
        assert done["applied"] is False
        assert done["verification"] is None
        assert acc["fixed_automatically"] == 0
        assert acc["patches_applied"] == 0
        assert acc["patches_queued"] == 2

    def test_interactive_option_b_records_alternative_patch(self, tmp_path):
        """Choosing Option B records the alternative repair candidate."""
        report = _low_risk_report(tmp_path, n=1)
        session = RecordingCheckupSession(group_decisions=["accept_alt"])
        planner = DeterministicPlanner()

        with patch(
            "pdd.checkup_agent.build_prompt_source_set_report", return_value=report
        ), patch(
            "pdd.checkup_agent.apply_approved_patches", return_value=0
        ) as mock_apply:
            agent = CheckupAgent(planner, session)
            agent.run(
                str(report.prompt_path),
                project_root=tmp_path,
                quiet=True,
                mode="interactive",
                apply=True,
            )

        patches = mock_apply.call_args.args[0]
        assert patches[0].kind == "append_covers"

    def test_low_risk_queued_without_apply(self, tmp_path):
        """Without --apply, low-risk fixes are queued, not applied."""
        report = _low_risk_report(tmp_path, n=2)
        session = RecordingCheckupSession()
        planner = DeterministicPlanner()

        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            agent = CheckupAgent(planner, session)
            agent.run(
                str(report.prompt_path), project_root=tmp_path, quiet=True, auto=True
            )

        acc = session.events_of_kind("session_done")[0].data["accounting"]
        assert acc["patches_queued"] == 2
        assert acc["patches_applied"] == 0

    def test_agent_scopes_all_findings_not_just_clarification(self, tmp_path):
        """The agent groups/risk-gates EVERY finding so auto mode and --llm-repair
        act on coverage/contract findings, not only clarification ones. (The
        clarification-only filter belongs to the workflow-gate path.)"""
        prompt_file = tmp_path / "mixed.prompt"
        prompt_file.write_text("% Mixed\nDo something.\n", encoding="utf-8")
        findings = [
            SourceSetFinding(
                finding_id="cov-1",
                source_check="coverage",
                severity="warn",
                file=prompt_file,
                line="2",
                message="Unchecked rule",
                code="UNCHECKED",  # not clarification, but must be in scope
            ),
            SourceSetFinding(
                finding_id="lint-vague-1",
                source_check="lint",
                severity="warn",
                file=prompt_file,
                line="2",
                message='Vague term "thing" used',
                code="VAGUE_TERM_UNDEFINED",  # requires_clarification
            ),
        ]
        report = PromptSourceSetReport(
            prompt_path=prompt_file,
            project_root=tmp_path,
            target=str(prompt_file),
            findings=findings,
            checks=[
                {"name": "coverage", "status": "warn"},
                {"name": "lint", "status": "warn"},
            ],
        )
        session = RecordingCheckupSession()
        planner = DeterministicPlanner()

        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            agent = CheckupAgent(planner, session)
            agent.run(
                str(report.prompt_path),
                project_root=tmp_path,
                quiet=True,
                auto=True,
                explicit_interactive=False,
            )

        # Both findings are in scope (coverage + vague), not just the clarification one.
        acc = session.events_of_kind("session_done")[0].data["accounting"]
        assert acc["total"] == 2

    def test_switch_to_auto_mid_session(self, tmp_path):
        """Choosing 'auto' on a group switches the rest of the session to auto."""
        report = _medium_report(tmp_path, n=2)
        # Two findings share one (lint, VAGUE_TERM_UNDEFINED) group, so to test a
        # switch we need two groups. Give them distinct codes.
        report.findings[1].code = "VAGUE_TERM_OTHER"
        session = RecordingCheckupSession(group_decisions=["skip", "auto"])
        planner = DeterministicPlanner()

        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            agent = CheckupAgent(planner, session)
            agent.run(
                str(report.prompt_path),
                project_root=tmp_path,
                quiet=True,
                mode="interactive",
            )

        mode_events = session.events_of_kind("mode_switch")
        assert len(mode_events) == 1
        assert mode_events[0].data["to"] == "auto"
        acc = session.events_of_kind("session_done")[0].data["accounting"]
        assert acc["skipped_by_user"] == 1  # first group skipped

    def test_no_auto_emits_no_mode_switch(self, tmp_path):
        """Interactive mode without an 'auto' decision emits no mode_switch."""
        report = _medium_report(tmp_path, n=1)
        session = RecordingCheckupSession(group_decisions=["skip"])
        planner = DeterministicPlanner()

        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            agent = CheckupAgent(planner, session)
            agent.run(
                str(report.prompt_path), project_root=tmp_path, quiet=True, mode="interactive"
            )

        assert not session.events_of_kind("mode_switch")

    def test_cli_auto_flag_without_planner_uses_deterministic(self, tmp_path):
        """--auto without --planner implicitly uses DeterministicPlanner."""
        from click.testing import CliRunner

        from pdd.commands.checkup import checkup

        prompt_file = tmp_path / "test.prompt"
        prompt_file.write_text("% Test\n", encoding="utf-8")

        runner = CliRunner()
        with patch("pdd.commands.checkup._interactive_tty_available", return_value=True), patch(
            "pdd.checkup_agent.CheckupAgent.run"
        ) as mock_run:
            mock_run.return_value = ("done", 0.0, "")
            result = runner.invoke(
                checkup,
                ["--interactive", "--auto", str(prompt_file)],
                catch_exceptions=False,
            )

        # CheckupAgent.run should have been called (not the legacy path)
        mock_run.assert_called_once()
        kwargs = mock_run.call_args.kwargs
        assert kwargs.get("auto") is True


class TestDirectoryDiscoveryAndDryRun:
    def test_discover_prompt_files_is_recursive(self, tmp_path):
        """Discovery must recurse so nested prompt subtrees are covered
        (matches classify_checkup_target's rglob-based directory detection)."""
        top = tmp_path / "prompts"
        (top / "commands").mkdir(parents=True)
        (top / "core").mkdir()
        (top / "top_python.prompt").write_text("% top\n", encoding="utf-8")
        (top / "commands" / "checkup_python.prompt").write_text("% c\n", encoding="utf-8")
        (top / "core" / "cli_python.prompt").write_text("% core\n", encoding="utf-8")
        # *_LLM.prompt scratch files are excluded.
        (top / "core" / "scratch_LLM.prompt").write_text("% x\n", encoding="utf-8")

        found = {p.name for p in discover_prompt_files(top)}
        assert found == {
            "top_python.prompt",
            "checkup_python.prompt",
            "cli_python.prompt",
        }

    def test_directory_honors_dry_run_for_auto_apply(self, tmp_path):
        """pdd checkup <dir> --auto --apply --dry-run must forward dry_run to each
        agent.run so low-risk patches are previewed, not written."""
        prompt = tmp_path / "style.prompt"
        prompt.write_text("% Style\nDo something.\n", encoding="utf-8")
        planner = DeterministicPlanner()

        with patch("pdd.checkup_agent.CheckupAgent.run") as mock_run:
            mock_run.return_value = ("ok", 0.0, "")
            run_checkup_directory(
                planner,
                [prompt],
                project_root=tmp_path,
                apply=True,
                dry_run=True,
                auto=True,
                quiet=True,
            )

        assert mock_run.call_args.kwargs["dry_run"] is True
        assert mock_run.call_args.kwargs["apply"] is True


# ---------------------------------------------------------------------------
# Menu option 7 — LLM draft (live, operator-approved). Offline-safe via an
# injected fake drafter; no real model is ever called in tests.
# ---------------------------------------------------------------------------


class TestAutoLLMRepair:
    """--auto --llm-repair: one full-prompt rewrite, applied once."""

    def _full(self, new_text, cost=0.05, model="fake/model"):
        def drafter_full(groups, *, prompt_text):
            return new_text, cost, model
        return drafter_full

    def test_auto_llm_repair_rewrites_whole_prompt_once(self, tmp_path):
        report = _medium_report(tmp_path, n=3)
        session = RecordingCheckupSession()
        agent = CheckupAgent(
            DeterministicPlanner(),
            session,
            repair_drafter_full=self._full("% Vague\n<vocabulary>fixed</vocabulary>\n"),
        )
        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            msg, cost, model = agent.run(
                str(report.prompt_path),
                project_root=tmp_path,
                quiet=True,
                auto=True,
                llm_repair=True,
            )

        # Whole file replaced by the single rewrite; all 3 findings resolved.
        assert report.prompt_path.read_text(encoding="utf-8") == "% Vague\n<vocabulary>fixed</vocabulary>\n"
        acc = session.events_of_kind("session_done")[0].data["accounting"]
        assert acc["drafted_by_llm"] == 3
        assert acc["patches_applied"] == 1  # one full_rewrite patch, not one per finding
        assert acc["remaining"] == 0
        assert cost == pytest.approx(0.05)  # exactly one model call

    def test_auto_llm_repair_offline_falls_back_to_deterministic(self, tmp_path):
        report = _medium_report(tmp_path, n=3)
        original = report.prompt_path.read_text(encoding="utf-8")
        session = RecordingCheckupSession()
        agent = CheckupAgent(
            DeterministicPlanner(),
            session,
            repair_drafter_full=self._full(None, cost=0.0, model=""),
        )
        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            agent.run(
                str(report.prompt_path),
                project_root=tmp_path,
                quiet=True,
                auto=True,
                llm_repair=True,
            )

        assert report.prompt_path.read_text(encoding="utf-8") == original  # nothing written
        acc = session.events_of_kind("session_done")[0].data["accounting"]
        assert acc["drafted_by_llm"] == 0
        assert acc["saved_for_review"] == 3  # deterministic per-group fallback

    def test_auto_llm_repair_dry_run_writes_nothing(self, tmp_path):
        report = _medium_report(tmp_path, n=2)
        original = report.prompt_path.read_text(encoding="utf-8")
        session = RecordingCheckupSession()
        agent = CheckupAgent(
            DeterministicPlanner(),
            session,
            repair_drafter_full=self._full("% rewritten\n"),
        )
        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            agent.run(
                str(report.prompt_path),
                project_root=tmp_path,
                quiet=True,
                auto=True,
                llm_repair=True,
                dry_run=True,
            )

        assert report.prompt_path.read_text(encoding="utf-8") == original
        acc = session.events_of_kind("session_done")[0].data["accounting"]
        assert acc["drafted_by_llm"] == 0
        assert acc["patches_queued"] >= 1


class TestLLMDraftOption:
    def _drafter(self, snippet, cost=0.01, model="fake/model"):
        # Mirror the real drafter, which prepends a clear "LLM draft" marker.
        def drafter(group, *, prompt_text):
            if snippet is None:
                return None, cost, model
            return f"<!-- LLM draft (pdd checkup) — review -->\n{snippet}", cost, model
        return drafter

    def test_confirmed_draft_is_applied_and_counted(self, tmp_path):
        report = _medium_report(tmp_path, n=2)
        session = RecordingCheckupSession(group_decisions=["llm"], confirm_drafts=True)
        agent = CheckupAgent(
            DeterministicPlanner(),
            session,
            repair_drafter=self._drafter(
                '<vocabulary>\n  <term name="term0">observable</term>\n</vocabulary>'
            ),
        )
        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            msg, cost, model = agent.run(
                str(report.prompt_path),
                project_root=tmp_path,
                quiet=True,
                mode="interactive",
            )

        # The real draft content was written into the prompt file (not a TODO).
        text = report.prompt_path.read_text(encoding="utf-8")
        assert "<vocabulary>" in text
        assert "LLM draft" in text  # the labelled marker
        acc = session.events_of_kind("session_done")[0].data["accounting"]
        assert acc["drafted_by_llm"] == 2  # both findings in the group resolved
        assert acc["patches_applied"] >= 1
        assert cost == pytest.approx(0.01)  # one model call per group (1 grouped call)
        assert model == "fake/model"

    def test_declined_draft_falls_back_to_save_for_review(self, tmp_path):
        report = _medium_report(tmp_path, n=2)
        original = report.prompt_path.read_text(encoding="utf-8")
        session = RecordingCheckupSession(group_decisions=["llm"], confirm_drafts=False)
        agent = CheckupAgent(
            DeterministicPlanner(),
            session,
            repair_drafter=self._drafter("<vocabulary/>"),
        )
        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            agent.run(str(report.prompt_path), project_root=tmp_path, quiet=True, mode="interactive")

        assert report.prompt_path.read_text(encoding="utf-8") == original  # nothing written
        acc = session.events_of_kind("session_done")[0].data["accounting"]
        assert acc["drafted_by_llm"] == 0
        assert acc["saved_for_review"] == 2

    def test_unavailable_draft_falls_back_without_crash(self, tmp_path):
        report = _medium_report(tmp_path, n=2)
        original = report.prompt_path.read_text(encoding="utf-8")
        session = RecordingCheckupSession(group_decisions=["llm"], confirm_drafts=True)
        agent = CheckupAgent(
            DeterministicPlanner(),
            session,
            repair_drafter=self._drafter(None, cost=0.0, model=""),  # offline / no key
        )
        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            agent.run(str(report.prompt_path), project_root=tmp_path, quiet=True, mode="interactive")

        assert report.prompt_path.read_text(encoding="utf-8") == original
        acc = session.events_of_kind("session_done")[0].data["accounting"]
        assert acc["drafted_by_llm"] == 0
        assert acc["saved_for_review"] == 2  # deterministic fallback

    def test_dry_run_confirmed_draft_writes_nothing(self, tmp_path):
        report = _medium_report(tmp_path, n=2)
        original = report.prompt_path.read_text(encoding="utf-8")
        session = RecordingCheckupSession(group_decisions=["llm"], confirm_drafts=True)
        agent = CheckupAgent(
            DeterministicPlanner(),
            session,
            repair_drafter=self._drafter("<vocabulary/>"),
        )
        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            agent.run(
                str(report.prompt_path),
                project_root=tmp_path,
                quiet=True,
                mode="interactive",
                dry_run=True,
            )

        assert report.prompt_path.read_text(encoding="utf-8") == original
        acc = session.events_of_kind("session_done")[0].data["accounting"]
        assert acc["drafted_by_llm"] == 0
        assert acc["patches_queued"] >= 1

    def test_llm_auto_fixes_all_remaining_in_one_rewrite(self, tmp_path):
        """Pressing [f] (llm_auto) fixes every group in ONE coherent rewrite (the
        same mechanism as --auto --llm-repair), not group-by-group."""
        prompt_file = tmp_path / "two.prompt"
        prompt_file.write_text("% two\nDo something.\n", encoding="utf-8")
        findings = [
            SourceSetFinding(
                finding_id="v1", source_check="lint", severity="warn",
                file=prompt_file, line="1", message='Vague term "a"',
                code="VAGUE_TERM_UNDEFINED",
            ),
            SourceSetFinding(
                finding_id="c1", source_check="contract", severity="warn",
                file=prompt_file, line="1", message="contract wording",
                code="CONTRACT_WORDING", recommended_action="tighten wording",
            ),
        ]
        report = PromptSourceSetReport(
            prompt_path=prompt_file, project_root=tmp_path, target=str(prompt_file),
            findings=findings,
            checks=[{"name": "lint", "status": "warn"}, {"name": "contract", "status": "warn"}],
        )

        def full(groups, *, prompt_text):
            return "% two\n<vocabulary>fixed</vocabulary>\n", 0.04, "fake/model"

        # Decide [f] on the first group → one rewrite fixes everything.
        session = RecordingCheckupSession(group_decisions=["llm_auto"])
        agent = CheckupAgent(DeterministicPlanner(), session, repair_drafter_full=full)
        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            _, cost, _ = agent.run(
                str(report.prompt_path), project_root=tmp_path, quiet=True, mode="interactive"
            )

        assert prompt_file.read_text(encoding="utf-8") == "% two\n<vocabulary>fixed</vocabulary>\n"
        acc = session.events_of_kind("session_done")[0].data["accounting"]
        assert acc["drafted_by_llm"] == 2       # both groups resolved
        assert acc["patches_applied"] == 1      # one full-rewrite patch
        assert cost == pytest.approx(0.04)      # exactly one model call
        switches = session.events_of_kind("mode_switch")
        assert any(e.data.get("to") == "llm-auto" for e in switches)


def test_draft_group_replacement_is_offline_safe():
    """A failing/None-returning model must yield None, not raise."""
    from pdd.checkup_interactive_main import draft_group_replacement
    from pdd.checkup_report import group_findings

    finding = SourceSetFinding(
        finding_id="lint-v-0", source_check="lint", severity="warn",
        file=Path("p.prompt"), message='Vague term "x"', code="VAGUE_TERM_UNDEFINED",
        recommended_action="Define x",
    )
    group = group_findings([finding])[0]

    def boom(**kwargs):
        raise RuntimeError("no network")

    snippet, cost, model = draft_group_replacement(group, prompt_text="% p", llm=boom)
    assert snippet is None
    assert cost == 0.0


def test_draft_group_replacement_labels_and_cleans_snippet():
    from pdd.checkup_interactive_main import draft_group_replacement
    from pdd.checkup_report import group_findings

    finding = SourceSetFinding(
        finding_id="lint-v-0", source_check="lint", severity="warn",
        file=Path("p.prompt"), message='Vague term "x"', code="VAGUE_TERM_UNDEFINED",
        recommended_action="Define x",
    )
    group = group_findings([finding])[0]

    def fake_llm(**kwargs):
        return {"result": "```\n<vocabulary/>\n```", "cost": 0.005, "model_name": "m"}

    snippet, cost, model = draft_group_replacement(group, prompt_text="% p", llm=fake_llm)
    assert snippet.startswith("<!-- LLM draft")
    assert "```" not in snippet      # code fences stripped
    assert "<vocabulary/>" in snippet
    assert cost == 0.005 and model == "m"
