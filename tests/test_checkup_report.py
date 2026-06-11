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
    decision_for,
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
# Decision (pass/warn → continue, strict → block)
# ---------------------------------------------------------------------------


class TestDecision:
    def test_pass_continues(self):
        text, cont = decision_for("pass", strict=False, blocking=False)
        assert cont is True
        assert "pass → continue" == text

    def test_warn_continues_with_note(self):
        text, cont = decision_for("warn", strict=False, blocking=False)
        assert cont is True
        assert "continue" in text

    def test_strict_blocking_blocks(self):
        text, cont = decision_for("fail", strict=True, blocking=True)
        assert cont is False
        assert "strict failure → block" == text

    def test_nonstrict_blocking_blocks(self):
        text, cont = decision_for("fail", strict=False, blocking=True)
        assert cont is False
        assert "block" in text

    def test_summary_includes_decision(self):
        acc = CheckupAccounting(total=1, saved_for_review=1)
        text = "\n".join(acc.summary_lines("warn", None, decision="warn → continue"))
        assert "Decision:" in text
        assert "warn → continue" in text


class TestAgentDecision:
    def test_warn_does_not_block(self, tmp_path):
        f = _finding("a", code="VAGUE_TERM_UNDEFINED", clar=True, section="requirements")
        report = _report_with(tmp_path, [f], [{"name": "lint", "status": "warn"}])
        session = RecordingCheckupSession()
        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            CheckupAgent(DeterministicPlanner(), session).run(
                str(report.prompt_path), project_root=tmp_path, quiet=True, mode="review"
            )
        done = session.events_of_kind("session_done")[0].data
        assert done["can_continue"] is True
        assert "continue" in done["decision"]

    def test_strict_warn_blocks(self, tmp_path):
        import click

        f = _finding("a", code="VAGUE_TERM_UNDEFINED", clar=True, section="requirements")
        report = _report_with(tmp_path, [f], [{"name": "lint", "status": "warn"}])
        session = RecordingCheckupSession()
        with patch("pdd.checkup_agent.build_prompt_source_set_report", return_value=report):
            with pytest.raises(click.exceptions.Exit):
                CheckupAgent(DeterministicPlanner(), session).run(
                    str(report.prompt_path), project_root=tmp_path, quiet=True,
                    mode="review", strict=True,
                )
        done = session.events_of_kind("session_done")[0].data
        assert done["can_continue"] is False
        assert "strict failure → block" == done["decision"]


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

    def test_patch_preview_keeps_repo_relative_directory_context(self, tmp_path):
        """A repo-relative patch target must keep its directory in the preview, not
        collapse to the basename (#1519 render_patch_preview path bug)."""
        from pdd.checkup_interactive_session import ApprovedPatch
        from pdd.checkup_report import render_patch_preview

        patch_obj = ApprovedPatch(
            kind="vocab_definition",
            target=Path("prompts/sub/foo.prompt"),  # already repo-relative
            anchor={"finding_id": "x", "line": 3},
            replacement="<!-- pdd-checkup TODO (X): note -->",
            finding_id="x",
        )
        text = render_patch_preview([patch_obj], target="p", groups=[], project_root=tmp_path)
        assert "# file: prompts/sub/foo.prompt" in text
        # the directory must not have been stripped down to just the basename
        assert "# file: foo.prompt" not in text

    def test_patch_preview_renders_vocabulary_stub(self):
        from pdd.checkup_report import render_patch_preview

        fs = [
            _finding("a", code="VAGUE_TERM_UNDEFINED", msg='Vague term "active" used'),
            _finding("b", code="VAGUE_TERM_UNDEFINED", msg='Vague term "valid" used'),
            _finding("a", code="VAGUE_TERM_UNDEFINED", msg='Vague term "active" used'),
        ]
        groups = group_findings(fs)
        text = render_patch_preview(
            [self._patch("a"), self._patch("b")], target="p", groups=groups
        )
        # actionable stub with the real, de-duplicated terms
        assert "<vocabulary>" in text
        assert '<term name="active">' in text
        assert '<term name="valid">' in text
        # "active" appears twice in findings but only once in the stub
        assert text.count('<term name="active">') == 1
        # per-finding details retained, but no longer mislabeled as a "replacement"
        assert "per-finding details" in text
        assert "recommended action:" in text

    def test_patch_preview_uses_concrete_known_vague_term_definitions(self):
        from pdd.checkup_report import render_patch_preview

        terms = [
            "active",
            "valid",
            "invalid",
            "unauthorized",
            "graceful",
            "successful",
            "duplicate",
            "untrusted",
            "authorized",
            "trusted",
        ]
        fs = [
            _finding(
                f"f-{term}",
                code="VAGUE_TERM_UNDEFINED",
                msg=f'Vague term "{term}" used',
            )
            for term in terms
        ]
        groups = group_findings(fs)

        text = render_patch_preview([self._patch("a")], target="p", groups=groups)

        assert "TODO" not in text
        assert "placeholder" not in text.lower()
        assert '<term name="valid">the token or session passes signature' in text
        assert '<term name="trusted">the source is in the configured allowlist' in text
        assert '<term name="graceful">the function returns the documented failure value' in text

    def test_patch_preview_without_groups_still_lists_patches(self):
        from pdd.checkup_report import render_patch_preview

        text = render_patch_preview([self._patch("a")], target="p")
        assert "## 1. a" in text
        assert "<vocabulary>" not in text  # no stub without vague-term groups


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
        import click

        f = _finding("a", source="coverage", severity="error", code="failed")
        report = _report_with(tmp_path, [f], [{"name": "coverage", "status": "fail"}])
        session = RecordingCheckupSession()
        with patch(
            "pdd.checkup_agent.build_prompt_source_set_report", return_value=report
        ), patch("pdd.checkup_agent.apply_approved_patches", return_value=0) as mock_apply:
            # An error-severity finding blocks → the agent exits non-zero (gate).
            with pytest.raises(click.exceptions.Exit):
                CheckupAgent(DeterministicPlanner(), session).run(
                    str(report.prompt_path), project_root=tmp_path, quiet=True,
                    auto=True, apply=True,
                )
        # high-risk finding → manual TODO, no patch applied
        mock_apply.assert_not_called()
        done = session.events_of_kind("session_done")[0].data
        assert done["accounting"]["manual_todo"] == 1
        assert done["accounting"]["fixed_automatically"] == 0
        # blocking decision recorded
        assert done["blocking"] is True
        assert done["can_continue"] is False

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
