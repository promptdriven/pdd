"""Unit tests for pdd.checkup_agentic_artifact (pdd.checkup.agentic.v1 builder)."""

from __future__ import annotations

from types import SimpleNamespace

import pytest

from pdd.checkup_agentic_artifact import (
    AGENTIC_AUTHORITY_STATUSES,
    AGENTIC_V1_SCHEMA,
    FINDING_TEXT_MAX_CHARS,
    AgenticFinding,
    AgenticV1Artifact,
    build_agentic_v1_artifact,
    _deduplicate_findings,
    _normalize_findings,
    _resolve_authority,
)


# ---------------------------------------------------------------------------
# _resolve_authority — the 5-way canonical/agentic mapping (R6)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "canonical_status, agentic_blocking, expected",
    [
        ("pass", False, "canonical_pass_agentic_mirror_clean"),
        ("pass", True, "canonical_pass_agentic_mirror_blocking"),
        ("unknown", False, "canonical_unknown_agentic_fallback_pass"),
        ("unknown", True, "canonical_unknown_agentic_fallback_blocking"),
        ("fail", False, "canonical_fail_agentic_not_authoritative"),
        ("fail", True, "canonical_fail_agentic_not_authoritative"),
    ],
)
def test_resolve_authority_table(canonical_status, agentic_blocking, expected):
    assert _resolve_authority(canonical_status, agentic_blocking) == expected


def test_resolve_authority_fail_dominates_agentic_outcome():
    # A canonical fail is authoritative regardless of the agentic mirror.
    assert _resolve_authority("fail", True) == "canonical_fail_agentic_not_authoritative"
    assert _resolve_authority("fail", False) == "canonical_fail_agentic_not_authoritative"


@pytest.mark.parametrize("bogus", ["", "weird", None, "passed", "error", "clean"])
def test_resolve_authority_unrecognized_fails_closed_to_unknown(bogus):
    # Only the exact tokens pass/fail/unknown (case/space-insensitive) are
    # recognized; everything else fails closed to the unknown lane.
    result = _resolve_authority(bogus, agentic_blocking=False)
    assert result == "canonical_unknown_agentic_fallback_pass"
    assert result in AGENTIC_AUTHORITY_STATUSES


def test_resolve_authority_normalizes_case_and_whitespace():
    assert _resolve_authority("PASS ", False) == "canonical_pass_agentic_mirror_clean"
    assert _resolve_authority("  Fail", True) == "canonical_fail_agentic_not_authoritative"


def test_resolve_authority_always_in_closed_vocabulary():
    for cs in ("pass", "fail", "unknown", "garbage"):
        for ab in (True, False):
            assert _resolve_authority(cs, ab) in AGENTIC_AUTHORITY_STATUSES


# ---------------------------------------------------------------------------
# _normalize_findings / _deduplicate_findings
# ---------------------------------------------------------------------------


def test_normalize_findings_extracts_severity_path_line():
    findings = _normalize_findings("blocker src/app.py:42 missing null check", "codex")
    assert len(findings) == 1
    f = findings[0]
    assert f.severity == "blocker"
    assert f.blocking is True
    assert f.path == "src/app.py"
    assert f.line == 42
    assert f.reviewer == "codex"


def test_normalize_findings_empty_on_no_severity():
    assert _normalize_findings("just some prose with no severity tokens", "codex") == []
    assert _normalize_findings("", "codex") == []


def test_normalize_findings_caps_free_text():
    huge = "critical " + ("x" * (FINDING_TEXT_MAX_CHARS + 500))
    findings = _normalize_findings(huge, "codex")
    assert findings
    assert len(findings[0].summary) <= FINDING_TEXT_MAX_CHARS


def test_deduplicate_findings_by_key():
    a = AgenticFinding(reviewer="codex", severity="blocker", blocking=True, path="a.py", line=1)
    b = AgenticFinding(reviewer="codex", severity="blocker", blocking=True, path="a.py", line=1)
    c = AgenticFinding(reviewer="codex", severity="critical", blocking=True, path="a.py", line=2)
    assert len(_deduplicate_findings([a, b, c])) == 2


def test_deduplicate_prose_only_on_summary_prefix():
    a = AgenticFinding(reviewer="codex", severity="low", blocking=False, summary="same summary " * 10)
    b = AgenticFinding(reviewer="codex", severity="low", blocking=False, summary="same summary " * 10)
    assert len(_deduplicate_findings([a, b])) == 1


# ---------------------------------------------------------------------------
# build_agentic_v1_artifact
# ---------------------------------------------------------------------------


def _state(**over):
    base = dict(
        reviewer_status={"codex": "clean", "claude": "fixer"},
        raw_outputs=[],
        findings=[],
        fixes=[],
        fresh_final_status="clean",
        active_reviewer="codex",
        verified_head_sha="0123456789abcdef0123456789abcdef01234567",
        remote_pr_head_sha=None,
        reviewed_head_sha=None,
        stop_reason="",
        max_rounds_reached=False,
        max_cost_reached=False,
        max_duration_reached=False,
    )
    base.update(over)
    return SimpleNamespace(**base)


def _config(**over):
    base = dict(review_only=False, no_fix=False, fresh_final_review_role=None,
                max_rounds=5, max_cost=50.0, max_minutes=90.0)
    base.update(over)
    return SimpleNamespace(**base)


def _context(**over):
    base = dict(pr_owner="promptdriven", pr_repo="pdd", repo_owner="promptdriven",
                repo_name="pdd", pr_number=1790)
    base.update(over)
    return SimpleNamespace(**base)


def test_build_artifact_schema_version_constant_R1():
    art = build_agentic_v1_artifact(
        loop_state=_state(), config=_config(), context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    assert art.schema_version == AGENTIC_V1_SCHEMA
    dumped = art.model_dump()
    assert "schema_version" in dumped and "schema" not in dumped


def test_build_artifact_nofix_never_populates_fix_attempts_R3():
    fixes = [SimpleNamespace(fixer="claude", fixer_result="attempted",
                             changed_files=["a.py"], pushed_head_sha="deadbeef")]
    # no_fix=True must yield empty fix_attempts even with fixes in loop state.
    art = build_agentic_v1_artifact(
        loop_state=_state(fixes=fixes), config=_config(no_fix=True), context=_context(),
        final_gate_report={"layer1_status": "unknown"},
    )
    assert art.mode == "nofix"
    assert art.fix_attempts == []

    # review_only also implies nofix.
    art2 = build_agentic_v1_artifact(
        loop_state=_state(fixes=fixes), config=_config(review_only=True), context=_context(),
        final_gate_report={"layer1_status": "unknown"},
    )
    assert art2.mode == "nofix"
    assert art2.fix_attempts == []


def test_build_artifact_fix_mode_records_attempts():
    fixes = [SimpleNamespace(fixer="claude", fixer_result="attempted",
                             changed_files=["a.py"], pushed_head_sha="deadbeef")]
    art = build_agentic_v1_artifact(
        loop_state=_state(fixes=fixes), config=_config(no_fix=False), context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    assert art.mode == "fix"
    assert len(art.fix_attempts) == 1
    assert art.fix_attempts[0].provider == "claude"


def test_build_artifact_authority_is_closed_and_canonical_owned_R6():
    art = build_agentic_v1_artifact(
        loop_state=_state(), config=_config(), context=_context(),
        final_gate_report={"layer1_status": "fail"},
    )
    # canonical fail dominates regardless of agentic mirror.
    assert art.authority == "canonical_fail_agentic_not_authoritative"
    assert art.authority in AGENTIC_AUTHORITY_STATUSES


def test_build_artifact_degraded_reviewer_on_parse_failure_R4():
    # Reviewer produced non-empty output that yields no parseable findings.
    art = build_agentic_v1_artifact(
        loop_state=_state(
            reviewer_status={"codex": "clean"},
            raw_outputs=[("codex", "some prose without any severity token")],
        ),
        config=_config(), context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    codex = next(r for r in art.reviewers if r.name == "codex")
    assert codex.status == "degraded"


def test_build_artifact_identity_and_budget():
    art = build_agentic_v1_artifact(
        loop_state=_state(max_rounds_reached=True, max_cost_reached=True),
        config=_config(), context=_context(pr_number=1790),
        final_gate_report={"layer1_status": "pass"},
    )
    assert art.owner == "promptdriven" and art.repo == "pdd" and art.pr_number == 1790
    assert art.budget.max_rounds_reached is True
    assert art.budget.max_cost_reached is True
    assert art.budget.max_minutes_reached is False


def test_build_artifact_never_crashes_on_garbage_inputs():
    art = build_agentic_v1_artifact(
        loop_state=SimpleNamespace(), config=SimpleNamespace(),
        context=SimpleNamespace(), final_gate_report=None,
    )
    assert isinstance(art, AgenticV1Artifact)
    assert art.authority in AGENTIC_AUTHORITY_STATUSES
    assert art.schema_version == AGENTIC_V1_SCHEMA
