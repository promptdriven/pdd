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
        ) as mock_report, patch(
            "pdd.checkup_agent._prompt_agent_menu_choice", return_value=4
        ):
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
        session = RecordingCheckupSession(custom_plan=custom_plan)
        planner = DeterministicPlanner()

        with patch(
            "pdd.checkup_agent.build_prompt_source_set_report"
        ) as mock_report, patch(
            "pdd.checkup_agent._prompt_agent_menu_choice", return_value=4
        ):
            mock_report.return_value = PromptSourceSetReport(
                prompt_path=prompt_file,
                project_root=tmp_path,
                target=str(prompt_file),
                findings=[],
                checks=[{"name": "lint", "status": "pass"}],
            )
            agent = CheckupAgent(planner, session)
            agent.run(str(prompt_file), project_root=tmp_path, quiet=True)

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
        finding = SourceSetFinding(
            finding_id="lint-v-001",
            source_check="lint",
            severity="warn",
            file=prompt_file,
            line="2",
            message="Vague term 'valid'",
            evidence="valid",
            recommended_action="Specify criterion",
            fix_command="",
            code="VAGUE_TERM",
        )

        session = RecordingCheckupSession()
        planner = DeterministicPlanner()

        with patch(
            "pdd.checkup_agent.build_prompt_source_set_report"
        ) as mock_report, patch(
            "pdd.checkup_agent._prompt_agent_menu_choice", return_value=4  # skip
        ):
            mock_report.return_value = PromptSourceSetReport(
                prompt_path=prompt_file,
                project_root=tmp_path,
                target=str(prompt_file),
                findings=[finding],
                checks=[{"name": "lint", "status": "warn"}],
            )
            agent = CheckupAgent(planner, session)
            msg, cost, model = agent.run(str(prompt_file), project_root=tmp_path, quiet=True)

        assert "complete" in msg.lower()
        done_events = session.events_of_kind("session_done")
        assert done_events
        assert done_events[0].data["total_findings"] == 1
        assert done_events[0].data["skipped"] == 1


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


def test_cli_planner_requires_interactive(tmp_path):
    """--planner without --interactive should not invoke CheckupAgent."""
    from click.testing import CliRunner

    from pdd.commands.checkup import checkup

    prompt_file = tmp_path / "test.prompt"
    prompt_file.write_text("% Test\nDo something.\n", encoding="utf-8")

    runner = CliRunner()
    # --planner without --interactive falls through to normal prompt checkup
    # (no crash, just runs non-interactively)
    with patch("pdd.commands.checkup.run_checkup_prompt") as mock_run:
        mock_run.return_value = (True, "ok", 0.0, "", 0)
        result = runner.invoke(
            checkup,
            ["--planner", "deterministic", str(prompt_file)],
            catch_exceptions=False,
        )
    # Should not raise; --planner is silently ignored without --interactive
    assert result.exit_code == 0 or "error" not in result.output.lower()


# ---------------------------------------------------------------------------
# Auto mode and interactive↔auto switching
# ---------------------------------------------------------------------------


class TestAutoMode:
    def _make_report(self, tmp_path: Path, n_findings: int = 2) -> PromptSourceSetReport:
        prompt_file = tmp_path / "vague.prompt"
        prompt_file.write_text("% Vague\nDo something valid.\n", encoding="utf-8")
        findings = [
            SourceSetFinding(
                finding_id=f"lint-v-{i:03d}",
                source_check="lint",
                severity="warn",
                file=prompt_file,
                line=str(i + 1),
                message=f"Vague term 'valid' #{i}",
                evidence="valid",
                recommended_action="Specify criterion",
                fix_command="",
                code="VAGUE_TERM",
            )
            for i in range(n_findings)
        ]
        return PromptSourceSetReport(
            prompt_path=prompt_file,
            project_root=tmp_path,
            target=str(prompt_file),
            findings=findings,
            checks=[{"name": "lint", "status": "warn"}],
        )

    def test_auto_mode_applies_primary_without_menu(self, tmp_path):
        """In auto mode, no menu is shown — findings are auto-applied."""
        prompt_file = tmp_path / "vague.prompt"
        prompt_file.write_text("% Vague\n", encoding="utf-8")
        report = self._make_report(tmp_path, n_findings=2)

        session = RecordingCheckupSession()
        planner = DeterministicPlanner()

        with patch(
            "pdd.checkup_agent.build_prompt_source_set_report", return_value=report
        ), patch(
            "pdd.checkup_agent._prompt_agent_menu_choice"
        ) as mock_menu:
            agent = CheckupAgent(planner, session)
            msg, _, _ = agent.run(
                str(report.prompt_path),
                project_root=tmp_path,
                quiet=True,
                auto=True,
            )

        # Menu should never have been called in auto mode.
        mock_menu.assert_not_called()
        assert "complete" in msg.lower()
        done_events = session.events_of_kind("session_done")
        assert done_events[0].data["auto_applied"] == 2
        assert done_events[0].data["skipped"] == 0

    def test_auto_mode_message_includes_auto_applied(self, tmp_path):
        report = self._make_report(tmp_path, n_findings=1)
        session = RecordingCheckupSession()
        planner = DeterministicPlanner()

        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            agent = CheckupAgent(planner, session)
            msg, _, _ = agent.run(
                str(report.prompt_path),
                project_root=tmp_path,
                quiet=True,
                auto=True,
            )

        assert "auto-applied" in msg

    def test_switch_to_auto_mid_session(self, tmp_path):
        """Choosing [a] mid-session switches subsequent findings to auto mode."""
        prompt_file = tmp_path / "vague.prompt"
        prompt_file.write_text("% Vague\n", encoding="utf-8")
        report = self._make_report(tmp_path, n_findings=3)

        session = RecordingCheckupSession()
        planner = DeterministicPlanner()

        # First finding: interactive (return 4=skip)
        # Second finding: user types 'a' → switch to auto (return 5)
        # Third finding: should be auto-applied without menu call
        menu_returns = iter([4, 5])

        with patch(
            "pdd.checkup_agent.build_prompt_source_set_report", return_value=report
        ), patch(
            "pdd.checkup_agent._prompt_agent_menu_choice",
            side_effect=lambda f, o: next(menu_returns),
        ):
            agent = CheckupAgent(planner, session)
            msg, _, _ = agent.run(
                str(report.prompt_path),
                project_root=tmp_path,
                quiet=True,
                auto=False,
            )

        mode_events = session.events_of_kind("mode_switch")
        assert len(mode_events) == 1
        assert mode_events[0].data["to"] == "auto"

        done = session.events_of_kind("session_done")[0]
        # finding 0: skipped interactively, finding 1: auto (on switch), finding 2: auto
        assert done.data["skipped"] == 1
        assert done.data["auto_applied"] == 2

    def test_no_auto_emits_no_mode_switch(self, tmp_path):
        """Pure interactive mode with skip choices emits no mode_switch events."""
        report = self._make_report(tmp_path, n_findings=1)
        session = RecordingCheckupSession()
        planner = DeterministicPlanner()

        with patch(
            "pdd.checkup_agent.build_prompt_source_set_report", return_value=report
        ), patch("pdd.checkup_agent._prompt_agent_menu_choice", return_value=4):
            agent = CheckupAgent(planner, session)
            agent.run(str(report.prompt_path), project_root=tmp_path, quiet=True, auto=False)

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
