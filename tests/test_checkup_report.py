"""Tests for checkup_report: risk, grouping, accounting, artifacts, plan display.

Plus agent-level behaviours that depend on them (skip reasons, review mode,
verification, risk-gated auto). All offline — no LLM, no network.
"""

from __future__ import annotations

from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.checkup_agent import CheckupAgent, RecordingCheckupSession
from pdd.checkup_planner import DeterministicPlanner
from pdd.checkup_prompt_main import PromptSourceSetReport, SourceSetFinding
from pdd.checkup_report import (
    RISK_HIGH,
    RISK_LOW,
    RISK_MEDIUM,
    CheckupAccounting,
    descriptive_plan_lines,
    group_findings,
    humanize_group_summary,
    repair_risk_for,
    write_artifacts,
)
from pdd.checkup_tools import ALL_TOOLS


def _finding(fid, *, code="X", source="lint", severity="warn", clar=False, msg="m", section="prose"):
    return SourceSetFinding(
        finding_id=fid,
        source_check=source,
        severity=severity,
        file=Path("p.prompt"),
        message=msg,
        evidence=section,
        recommended_action="do it",
        code=code,
        requires_clarification=clar,
    )


# ---------------------------------------------------------------------------
# Risk
# ---------------------------------------------------------------------------


class TestRepairRisk:
    def test_error_is_high(self):
        assert repair_risk_for(_finding("a", severity="error")) == RISK_HIGH

    def test_requires_clarification_is_medium(self):
        assert repair_risk_for(_finding("a", clar=True)) == RISK_MEDIUM

    def test_evidence_check_is_medium(self):
        assert repair_risk_for(_finding("a", source="coverage")) == RISK_MEDIUM
        assert repair_risk_for(_finding("a", source="gate")) == RISK_MEDIUM

    def test_plain_lint_is_low(self):
        assert repair_risk_for(_finding("a", source="lint", code="STYLE")) == RISK_LOW

    def test_none_is_low(self):
        assert repair_risk_for(None) == RISK_LOW


# ---------------------------------------------------------------------------
# Grouping
# ---------------------------------------------------------------------------


class TestGrouping:
    def test_groups_by_check_and_code(self):
        fs = [
            _finding("a", code="VAGUE_TERM_UNDEFINED"),
            _finding("b", code="VAGUE_TERM_UNDEFINED"),
            _finding("c", code="OTHER"),
        ]
        groups = group_findings(fs)
        assert len(groups) == 2
        assert groups[0].size == 2
        assert groups[0].is_grouped
        assert groups[1].size == 1

    def test_preserves_first_seen_order(self):
        fs = [_finding("a", code="B"), _finding("b", code="A")]
        groups = group_findings(fs)
        assert [g.code for g in groups] == ["B", "A"]

    def test_terms_extracted(self):
        fs = [
            _finding("a", code="VAGUE_TERM_UNDEFINED", msg='Vague term "active" used'),
            _finding("b", code="VAGUE_TERM_UNDEFINED", msg='Vague term "valid" used'),
        ]
        group = group_findings(fs)[0]
        assert group.terms() == ["active", "valid"]


class TestHumanWording:
    def test_grouped_vague_summary(self):
        fs = [
            _finding(f"f{i}", code="VAGUE_TERM_UNDEFINED",
                     msg=f'Vague term "t{i}" used', section="requirements")
            for i in range(3)
        ]
        lines = humanize_group_summary(group_findings(fs)[0])
        text = "\n".join(lines)
        assert "Found 3 undefined vague terms" in text
        assert "requirements" in text
        assert "<vocabulary>" in text

    def test_single_finding_summary(self):
        f = _finding("a", code="VAGUE_TERM_UNDEFINED",
                     msg='Vague term "active" used', section="requirements")
        lines = humanize_group_summary(group_findings([f])[0])
        assert any('"active"' in line for line in lines)


# ---------------------------------------------------------------------------
# Accounting
# ---------------------------------------------------------------------------


class TestAccounting:
    def test_remaining_is_total_minus_resolved(self):
        acc = CheckupAccounting(total=10, fixed_manually=2, fixed_automatically=3,
                                skipped_by_user=1)
        assert acc.remaining == 4

    def test_remaining_never_negative(self):
        acc = CheckupAccounting(total=1, fixed_automatically=5)
        assert acc.remaining == 0

    def test_summary_distinguishes_all_categories(self):
        acc = CheckupAccounting(total=10, fixed_manually=1, fixed_automatically=2,
                                skipped_by_user=1, saved_for_review=3,
                                patches_queued=3)
        text = "\n".join(acc.summary_lines("warn"))
        assert "Total: 10" in text
        assert "Fixed manually: 1" in text
        assert "Fixed automatically: 2" in text
        assert "Skipped by user: 1" in text
        assert "Remaining: 6" in text
        assert "Queued: 3" in text
        assert "Saved for review: 3" in text

    def test_summary_applied_mode_shows_failed(self):
        acc = CheckupAccounting(total=2, fixed_automatically=2, patches_applied=2,
                                patches_failed=0)
        text = "\n".join(acc.summary_lines("warn"))
        assert "Applied: 2" in text
        assert "Failed: 0" in text

    def test_summary_includes_artifacts(self):
        acc = CheckupAccounting(total=1, saved_for_review=1)
        text = "\n".join(acc.summary_lines("warn", {"report": "r.md", "patch": "p.patch"}))
        assert "Artifacts:" in text
        assert "r.md" in text
        assert "p.patch" in text


# ---------------------------------------------------------------------------
# Plan display
# ---------------------------------------------------------------------------


def test_descriptive_plan_lines_compact():
    lines = descriptive_plan_lines(["lint", "contract"], {"lint": "hygiene", "contract": "io"})
    assert lines[0] == "Plan:"
    assert any("lint" in line and "hygiene" in line for line in lines)


# ---------------------------------------------------------------------------
# Artifacts
# ---------------------------------------------------------------------------


class TestArtifacts:
    def _patch(self, fid):
        from pdd.checkup_interactive_session import ApprovedPatch

        return ApprovedPatch(
            kind="vocab_definition",
            target=Path("p.prompt"),
            anchor={"finding_id": fid},
            replacement="define it",
            finding_id=fid,
        )

    def test_writes_report_and_patch_when_findings(self, tmp_path):
        fs = [_finding("a", code="VAGUE_TERM_UNDEFINED")]
        groups = group_findings(fs)
        acc = CheckupAccounting(total=1, saved_for_review=1)
        tr = ALL_TOOLS["lint"].extract(
            PromptSourceSetReport(prompt_path=tmp_path / "p.prompt", project_root=tmp_path,
                                  target="p", findings=fs,
                                  checks=[{"name": "lint", "status": "warn"}])
        )
        arts = write_artifacts(
            project_root=tmp_path, prompt_path=tmp_path / "p.prompt", target="p",
            status="warn", tool_results=[tr], groups=groups, accounting=acc,
            patches=[self._patch("a")], applied=False,
        )
        assert arts["report"].is_file()
        assert arts["patch"].is_file()
        assert "Checkup report" in arts["report"].read_text()

    def test_no_artifacts_for_clean_pass(self, tmp_path):
        arts = write_artifacts(
            project_root=tmp_path, prompt_path=tmp_path / "p.prompt", target="p",
            status="pass", tool_results=[], groups=[], accounting=CheckupAccounting(),
            patches=[], applied=False,
        )
        assert arts == {}
        assert not (tmp_path / ".pdd" / "checkup").exists()


# ---------------------------------------------------------------------------
# Agent integration — skip reasons, review mode, verification
# ---------------------------------------------------------------------------


def _report_with(tmp_path, findings, checks):
    pf = tmp_path / "x.prompt"
    pf.write_text("% x\n", encoding="utf-8")
    return PromptSourceSetReport(
        prompt_path=pf, project_root=tmp_path, target=str(pf),
        findings=findings, checks=checks,
    )


class TestAgentIntegration:
    def test_tool_start_carries_skip_reason(self, tmp_path):
        report = _report_with(
            tmp_path, [],
            [{"name": "coverage", "status": "skip", "reason": "no <contract_rules> to cover"}],
        )
        session = RecordingCheckupSession()
        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            CheckupAgent(DeterministicPlanner(), session).run(
                str(report.prompt_path), project_root=tmp_path, quiet=True, mode="review"
            )
        starts = {e.data["tool"]: e.data for e in session.events_of_kind("tool_start")}
        assert starts["coverage"]["status"] == "skip"
        assert "contract_rules" in starts["coverage"]["skip_reason"]

    def test_review_mode_does_not_hang_and_writes_artifacts(self, tmp_path):
        f = _finding("a", code="VAGUE_TERM_UNDEFINED",
                     msg='Vague term "active" used', section="requirements")
        report = _report_with(tmp_path, [f], [{"name": "lint", "status": "warn"}])
        session = RecordingCheckupSession()
        # No stdin provided → if review mode prompted, this would raise.
        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            CheckupAgent(DeterministicPlanner(), session).run(
                str(report.prompt_path), project_root=tmp_path, quiet=True, mode="review"
            )
        done = session.events_of_kind("session_done")[0].data
        assert done["artifacts"].get("report")
        assert (tmp_path / ".pdd" / "checkup").exists()

    def test_high_risk_not_auto_applied(self, tmp_path):
        f = _finding("a", source="coverage", severity="error", code="failed")
        report = _report_with(tmp_path, [f], [{"name": "coverage", "status": "fail"}])
        session = RecordingCheckupSession()
        with patch(
            "pdd.checkup_agent.build_prompt_source_set_report", return_value=report
        ), patch("pdd.checkup_agent.apply_approved_patches", return_value=0) as mock_apply:
            CheckupAgent(DeterministicPlanner(), session).run(
                str(report.prompt_path), project_root=tmp_path, quiet=True,
                auto=True, apply=True,
            )
        # high-risk finding → manual TODO, no patch applied
        mock_apply.assert_not_called()
        acc = session.events_of_kind("session_done")[0].data["accounting"]
        assert acc["manual_todo"] == 1
        assert acc["fixed_automatically"] == 0

    def test_verification_runs_after_applied_fixes(self, tmp_path):
        f = _finding("a", source="lint", code="STYLE")  # low risk
        before = _report_with(tmp_path, [f], [{"name": "lint", "status": "warn"}])
        after = _report_with(tmp_path, [], [{"name": "lint", "status": "pass"}])
        session = RecordingCheckupSession()
        with patch(
            "pdd.checkup_agent.build_prompt_source_set_report",
            side_effect=[before, after],
        ), patch("pdd.checkup_agent.apply_approved_patches", return_value=0):
            CheckupAgent(DeterministicPlanner(), session).run(
                str(before.prompt_path), project_root=tmp_path, quiet=True,
                auto=True, apply=True,
            )
        verifying = session.events_of_kind("verifying")
        assert verifying, "expected a verifying event after applied fixes"
        assert verifying[0].data["results"].get("lint") == "pass"

    def test_no_verification_without_apply(self, tmp_path):
        f = _finding("a", source="lint", code="STYLE")
        report = _report_with(tmp_path, [f], [{"name": "lint", "status": "warn"}])
        session = RecordingCheckupSession()
        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            CheckupAgent(DeterministicPlanner(), session).run(
                str(report.prompt_path), project_root=tmp_path, quiet=True, auto=True
            )
        assert not session.events_of_kind("verifying")
