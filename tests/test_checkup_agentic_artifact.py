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
from pdd.checkup_review_loop import ReviewLoopConfig


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


def test_normalize_findings_clean_json_does_not_parse_summary_severity():
    raw = '{"status":"clean","summary":"No critical issues found","findings":[]}'
    assert _normalize_findings(raw, "codex") == []


def test_normalize_findings_clean_fenced_json_does_not_parse_summary_severity():
    raw = """Reviewer result:
```json
{"status":"clean","summary":"No critical issues found","findings":[]}
```
"""
    assert _normalize_findings(raw, "codex") == []


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
        original_reviewer="codex",
        reviewer_status_details={},
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
    # Production no-fix agentic runs are represented as review_only on the real
    # ReviewLoopConfig; do not rely on a fake no_fix attribute.
    art = build_agentic_v1_artifact(
        loop_state=_state(fixes=fixes),
        config=ReviewLoopConfig(review_only=True, agentic_mode=True),
        context=_context(),
        final_gate_report={"layer1_status": "unknown"},
    )
    assert art.mode == "nofix"
    assert art.fix_attempts == []


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
    assert art.status == "failed"
    assert art.verdict.decision == "block"


def test_build_artifact_budget_and_degraded_reviewer_fail_closed_when_clean():
    budget = build_agentic_v1_artifact(
        loop_state=_state(max_cost_reached=True), config=_config(), context=_context(),
        final_gate_report={"layer1_status": "pass"})
    assert budget.status == "budget_exhausted"
    assert budget.verdict.decision == "block"
    degraded = build_agentic_v1_artifact(
        loop_state=_state(reviewer_status={"codex": "degraded"}),
        config=_config(), context=_context(), final_gate_report={"layer1_status": "pass"})
    assert degraded.status == "needs_human"
    assert degraded.verdict.decision == "block"


def test_build_artifact_push_failure_dominates_attempted_fix():
    fix = SimpleNamespace(fixer="claude", fixer_result="attempted",
                          push_status="push_failed", changed_files=["a.py"],
                          local_fixer_commit_sha="local-only")
    art = build_agentic_v1_artifact(
        loop_state=_state(fixes=[fix]), config=_config(), context=_context(),
        final_gate_report={"layer1_status": "pass"})
    assert art.fix_attempts[0].status == "failed"
    assert art.fix_attempts[0].commit_sha is None


def test_build_artifact_degraded_reviewer_on_parse_failure_R4():
    # Reviewer reported findings but its (compound-keyed, production-format)
    # output could not be parsed into any structured finding -> degraded.
    art = build_agentic_v1_artifact(
        loop_state=_state(
            reviewer_status={"codex": "findings"},
            findings=[],
            raw_outputs=[("review:codex:round1", "prose with no severity token")],
        ),
        config=_config(), context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    codex = next(r for r in art.reviewers if r.name == "codex")
    assert codex.status == "degraded"


def test_build_artifact_clean_reviewer_with_output_stays_clean():
    # A genuinely clean reviewer (no findings) must NOT be marked degraded.
    art = build_agentic_v1_artifact(
        loop_state=_state(
            reviewer_status={"codex": "clean"},
            raw_outputs=[("review:codex:round1", "looks good, nothing to flag")],
        ),
        config=_config(), context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    codex = next(r for r in art.reviewers if r.name == "codex")
    assert codex.status == "clean"


def test_build_artifact_fixer_output_not_parsed_as_reviewer_findings():
    # fix:/sot-repair: outputs are fixer prose, never reviewer findings.
    art = build_agentic_v1_artifact(
        loop_state=_state(
            reviewer_status={"codex": "clean"},
            raw_outputs=[("fix:claude:for:codex:round1", "blocker foo.py:1 bad")],
        ),
        config=_config(), context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    # No reviewer named 'claude' (fixer), and the fixer prose is not a finding.
    assert all(f.reviewer != "claude" for f in art.findings)


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


# ---------------------------------------------------------------------------
# Regression: production always sets a non-empty stop_reason (#1788 review)
# ---------------------------------------------------------------------------


def test_build_artifact_passed_true_despite_nonempty_stop_reason():
    # run_checkup_review_loop sets stop_reason on EVERY exit path, including
    # clean ones. A clean fresh-final + no blocking findings must still pass.
    art = build_agentic_v1_artifact(
        loop_state=_state(
            reviewer_status={"codex": "clean"},
            fresh_final_status="clean",
            stop_reason="Primary reviewer is clean.",
        ),
        config=_config(), context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    assert art.status == "passed"
    assert art.verdict.decision == "pass"
    assert art.verdict.reason == "Primary reviewer is clean."


def test_build_artifact_clean_fix_mode_without_fixer_attempt_passes():
    art = build_agentic_v1_artifact(
        loop_state=_state(
            fixes=[],
            verified_head_sha="",
            fresh_final_status="clean",
            stop_reason="Primary reviewer is clean.",
        ),
        config=_config(no_fix=False),
        context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    assert art.validation_after_fix.status == "not_run"
    assert art.status == "passed"
    assert art.verdict.decision == "pass"


@pytest.mark.parametrize("original_reviewer", ["codex", ""])
def test_build_artifact_clean_fallback_supersedes_failed_primary(original_reviewer):
    art = build_agentic_v1_artifact(
        loop_state=_state(
            reviewer_status={"codex": "failed", "gemini": "clean", "claude": "fixer"},
            active_reviewer="gemini",
            original_reviewer=original_reviewer,
            raw_outputs=[
                ("review:codex:round1", "critical provider failure"),
                (
                    "review:gemini:round1",
                    '```json\n{"status":"clean","findings":[]}\n```',
                ),
            ],
            fixes=[],
            verified_head_sha="",
            fresh_final_status="clean",
            stop_reason="Fallback reviewer is clean.",
        ),
        config=_config(no_fix=False),
        context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    assert {reviewer.name: reviewer.status for reviewer in art.reviewers} == {
        "codex": "failed",
        "gemini": "clean",
    }
    assert any(finding.reviewer == "codex" for finding in art.findings)
    assert art.status == "passed"
    assert art.verdict.decision == "pass"


def test_build_artifact_fixed_blockers_do_not_fail_clean_final_review():
    # A successful fix cycle leaves historical blocker findings in loop state
    # with status="fixed", and raw_outputs may still contain earlier reviewer
    # prose. Those records remain useful artifact history, but they are not open
    # blockers for the final verdict.
    art = build_agentic_v1_artifact(
        loop_state=_state(
            reviewer_status={"codex": "clean"},
            findings=[
                SimpleNamespace(
                    severity="blocker",
                    reviewer="codex",
                    finding="old blocker",
                    required_fix="fix it",
                    location="a.py",
                    status="fixed",
                )
            ],
            raw_outputs=[("review:codex:round1", "blocker a.py:1 old blocker")],
            fresh_final_status="clean",
            stop_reason="Primary reviewer is satisfied after reviewing the fixer response.",
        ),
        config=_config(), context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    assert art.status == "passed"
    assert art.verdict.decision == "pass"
    assert art.authority == "canonical_pass_agentic_mirror_clean"


def test_build_artifact_status_vocab_matches_spec():
    # blocking findings -> failed
    blocking = build_agentic_v1_artifact(
        loop_state=_state(
            reviewer_status={"codex": "findings"},
            findings=[SimpleNamespace(severity="blocker", reviewer="codex",
                                      finding="bad", required_fix="fix", location="a.py")],
            fresh_final_status="findings",
            stop_reason="findings remain",
        ),
        config=_config(), context=_context(), final_gate_report={"layer1_status": "pass"},
    )
    assert blocking.status == "failed"
    # budget exhausted -> budget_exhausted
    budget = build_agentic_v1_artifact(
        loop_state=_state(fresh_final_status="missing", max_cost_reached=True,
                          stop_reason="budget"),
        config=_config(), context=_context(), final_gate_report={"layer1_status": "unknown"},
    )
    assert budget.status == "budget_exhausted"
    # reviewer failed, no content block -> needs_human
    nh = build_agentic_v1_artifact(
        loop_state=_state(reviewer_status={"codex": "failed"}, fresh_final_status="missing",
                          stop_reason="reviewer failed"),
        config=_config(), context=_context(), final_gate_report={"layer1_status": "unknown"},
    )
    assert nh.status == "needs_human"


def test_build_artifact_open_medium_finding_is_blocking_under_default_policy():
    # The artifact's blocking classification must mirror the review-loop policy
    # (ReviewLoopConfig defaults blocking_severities to blocker/critical/medium).
    # An open structured `medium` finding under the default config must NOT be
    # reported as a clean canonical-mirror pass, otherwise hosted consumers get a
    # false clean verdict for a PR the canonical loop still treats as blocked.
    art = build_agentic_v1_artifact(
        loop_state=_state(
            reviewer_status={"codex": "findings"},
            findings=[
                SimpleNamespace(
                    severity="medium",
                    reviewer="codex",
                    finding="material risk",
                    required_fix="address it",
                    location="a.py",
                    status="open",
                )
            ],
            fresh_final_status="clean",
            stop_reason="findings remain",
        ),
        config=ReviewLoopConfig(agentic_mode=True),
        context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    medium = next(f for f in art.findings if f.severity == "medium")
    assert medium.blocking is True
    assert art.status != "passed"
    assert art.verdict.decision == "block"
    assert art.authority == "canonical_pass_agentic_mirror_blocking"


def test_build_artifact_blocking_severities_respects_config_override():
    # A config that narrows blocking_severities to exclude `medium` must make an
    # open medium finding non-blocking, proving the classification is driven by
    # config policy rather than a hardcoded severity set.
    art = build_agentic_v1_artifact(
        loop_state=_state(
            reviewer_status={"codex": "findings"},
            findings=[
                SimpleNamespace(
                    severity="medium",
                    reviewer="codex",
                    finding="minor note",
                    required_fix="optional",
                    location="a.py",
                    status="open",
                )
            ],
            fresh_final_status="clean",
            stop_reason="findings remain",
        ),
        config=ReviewLoopConfig(agentic_mode=True, blocking_severities=("blocker", "critical")),
        context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    medium = next(f for f in art.findings if f.severity == "medium")
    assert medium.blocking is False
    assert art.authority == "canonical_pass_agentic_mirror_clean"


def test_build_artifact_reviewer_command_populated():
    art = build_agentic_v1_artifact(
        loop_state=_state(reviewer_status={"codex": "clean", "claude": "clean"}),
        config=_config(reviewer_commands={"codex": "/review", "claude": "/code-review"}),
        context=_context(), final_gate_report={"layer1_status": "pass"},
    )
    cmds = {r.name: r.command for r in art.reviewers}
    assert cmds["codex"] == "/review"
    assert cmds["claude"] == "/code-review"


def test_build_artifact_fix_status_maps_attempted_to_applied():
    fixes = [SimpleNamespace(fixer="claude", fixer_result="attempted",
                             push_status="pushed", changed_files=["a.py"],
                             pushed_head_sha="deadbeef")]
    art = build_agentic_v1_artifact(
        loop_state=_state(fixes=fixes), config=_config(no_fix=False),
        context=_context(), final_gate_report={"layer1_status": "pass"},
    )
    assert art.fix_attempts[0].status == "applied"


@pytest.mark.parametrize("push_status", ["not_attempted", None])
def test_build_artifact_attempted_fix_without_push_is_not_applied(push_status):
    fixes = [
        SimpleNamespace(
            fixer="claude",
            fixer_result="attempted",
            push_status=push_status,
            changed_files=["a.py"],
            pushed_head_sha=None,
        )
    ]
    art = build_agentic_v1_artifact(
        loop_state=_state(fixes=fixes, verified_head_sha=""),
        config=_config(no_fix=False),
        context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    assert art.fix_attempts[0].status == "skipped"
    assert art.fix_attempts[0].commit_sha is None
    assert art.validation_after_fix.status == "unverified"
    assert art.status != "passed"


def test_build_artifact_layer1_blockers_passed_through():
    art = build_agentic_v1_artifact(
        loop_state=_state(), config=_config(), context=_context(),
        final_gate_report={"layer1_status": "fail", "blockers": ["gate X failed", "test Y failed"]},
    )
    assert art.layer1.blockers == ["gate X failed", "test Y failed"]


# ---------------------------------------------------------------------------
# Additional coverage
# ---------------------------------------------------------------------------



import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

def test_normalize_findings_custom_blocking_severities():
    findings = _normalize_findings(
        "high src/x.py:10 something", "codex", blocking_severities={"high"}
    )
    assert len(findings) == 1
    assert findings[0].blocking is True
    # Under default policy, "high" is NOT blocking.
    default = _normalize_findings("high src/x.py:10 something", "codex")
    assert default[0].blocking is False


def test_normalize_findings_multiple_lines():
    text = "blocker a.py:1 first issue\nlow b.py:2 minor\nprose without severity"
    findings = _normalize_findings(text, "claude")
    assert len(findings) == 2
    severities = {f.severity for f in findings}
    assert severities == {"blocker", "low"}


def test_deduplicate_preserves_first_occurrence_order():
    a = AgenticFinding(reviewer="codex", severity="blocker", blocking=True, path="a.py", line=1)
    b = AgenticFinding(reviewer="codex", severity="critical", blocking=True, path="b.py", line=2)
    dup_a = AgenticFinding(reviewer="codex", severity="blocker", blocking=True, path="a.py", line=1)
    result = _deduplicate_findings([a, b, dup_a])
    assert [f.path for f in result] == ["a.py", "b.py"]


def test_build_artifact_head_sha_fallback_chain():
    art = build_agentic_v1_artifact(
        loop_state=_state(verified_head_sha="", remote_pr_head_sha="remote-sha", reviewed_head_sha="reviewed-sha"),
        config=_config(), context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    assert art.head_sha == "remote-sha"


def test_build_artifact_validation_status_not_run_in_nofix():
    art = build_agentic_v1_artifact(
        loop_state=_state(verified_head_sha=""),
        config=ReviewLoopConfig(review_only=True, agentic_mode=True),
        context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    assert art.validation_after_fix.status == "not_run"


def test_build_artifact_validation_status_verified_with_sha():
    fixes = [
        SimpleNamespace(
            fixer="claude",
            fixer_result="attempted",
            push_status="pushed",
            changed_files=["a.py"],
            pushed_head_sha="abc123",
        )
    ]
    art = build_agentic_v1_artifact(
        loop_state=_state(verified_head_sha="abc123", fixes=fixes),
        config=_config(), context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    assert art.validation_after_fix.status == "verified"
    assert "abc123" in art.validation_after_fix.evidence


def test_build_artifact_fresh_final_reviewer_excluded_from_reviewers():
    art = build_agentic_v1_artifact(
        loop_state=_state(reviewer_status={"codex": "clean", "fresh-final": "clean"}),
        config=_config(), context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    names = {r.name for r in art.reviewers}
    assert "fresh-final" not in names


def test_build_artifact_fix_status_skipped_and_failed():
    fixes = [
        SimpleNamespace(fixer="claude", fixer_result="skipped", push_status=None, changed_files=[]),
        SimpleNamespace(fixer="codex", fixer_result="failed", push_status=None, changed_files=[]),
    ]
    art = build_agentic_v1_artifact(
        loop_state=_state(fixes=fixes), config=_config(no_fix=False),
        context=_context(), final_gate_report={"layer1_status": "pass"},
    )
    statuses = {a.status for a in art.fix_attempts}
    assert statuses == {"skipped", "failed"}


def test_build_artifact_layer1_status_derived_from_gate_report():
    art_pass = build_agentic_v1_artifact(
        loop_state=_state(), config=_config(), context=_context(),
        final_gate_report={"status": "success"},
    )
    assert art_pass.layer1.status == "pass"
    art_fail = build_agentic_v1_artifact(
        loop_state=_state(), config=_config(), context=_context(),
        final_gate_report={"final_gate_status": "blocked"},
    )
    assert art_fail.layer1.status == "fail"


def test_build_artifact_secrets_scrubbed_in_free_text(monkeypatch):
    # Patch the scrubber at its defining module; artifact imports it lazily.
    from pdd import checkup_review_loop
    monkeypatch.setattr(checkup_review_loop, "_scrub_secrets", lambda t: t.replace("SECRET", "[REDACTED]"))
    art = build_agentic_v1_artifact(
        loop_state=_state(
            findings=[SimpleNamespace(severity="blocker", reviewer="codex",
                                      finding="leak SECRET here", required_fix="remove SECRET",
                                      location="a.py", status="open")],
            stop_reason="stop with SECRET token",
        ),
        config=_config(), context=_context(),
        final_gate_report={"layer1_status": "pass", "blockers": ["blocker SECRET line"]},
    )
    assert "SECRET" not in art.findings[0].summary
    assert "[REDACTED]" in art.findings[0].summary
    assert "SECRET" not in art.verdict.reason
    assert "SECRET" not in art.layer1.blockers[0]


def test_build_artifact_artifact_serializes_to_json():
    art = build_agentic_v1_artifact(
        loop_state=_state(), config=_config(), context=_context(),
        final_gate_report={"layer1_status": "pass"},
    )
    dumped = art.model_dump()
    assert dumped["schema_version"] == AGENTIC_V1_SCHEMA
    assert dumped["authority"] in AGENTIC_AUTHORITY_STATUSES
