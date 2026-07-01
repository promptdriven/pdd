from __future__ import annotations

from types import SimpleNamespace

from pdd.checkup_agentic_artifact import AGENTIC_V1_SCHEMA, build_agentic_v1_artifact
from pdd.checkup_review_loop import (
    ReviewFinding,
    ReviewLoopState,
    parse_reviewer_commands,
    parse_reviewers,
)


def test_parse_reviewers_accepts_slash_command_annotations() -> None:
    value = "codex:/review,claude:/code-review"

    assert parse_reviewers(value) == ("codex", "claude")
    assert parse_reviewer_commands(value) == {
        "codex": "/review",
        "claude": "/code-review",
    }


def test_agentic_artifact_bounds_redacts_and_skips_fixes_in_nofix_mode() -> None:
    state = ReviewLoopState(
        reviewer_status={"codex": "findings"},
        active_reviewer="codex",
        agentic_mode=True,
        agentic_no_fix=True,
        agentic_adversarial_prompt="find reasons not to merge " + "x" * 3000,
        agentic_reviewer_commands={"codex": "/review"},
        agentic_fresh_final_review_role="claude",
        agentic_max_rounds=3,
        agentic_max_cost=4.5,
        agentic_max_minutes=6.0,
    )
    finding = ReviewFinding(
        severity="critical",
        reviewer="codex",
        area="api",
        location="pdd/example.py:10",
        evidence="token ghp_abcdefghijklmnopqrstuvwxyz0123456789 leaked",
        finding="runtime path is missing",
        required_fix="implement the runtime contract",
        round_number=1,
    )
    state.findings_by_key[finding.key] = finding
    context = SimpleNamespace(
        pr_url="https://github.com/org/repo/pull/7",
        pr_owner="org",
        pr_repo="repo",
        pr_number=7,
        issue_url="",
        issue_number=7,
        has_issue=False,
    )
    final_state = {
        "reviewer_status": {"codex": "findings"},
        "fresh_final_status": "missing",
        "issue_aligned": "true",
        "stop_reason": "No-fix mode: reviewer reported findings; fixer skipped.",
        "total_cost": 0.25,
        "max_rounds_reached": False,
        "max_cost_reached": False,
        "max_duration_reached": False,
        "remote_pr_head_sha": "abc123",
        "reviewed_head_sha": "abc123",
        "verified_head_sha": None,
        "verification_status_by_round": {},
        "fixes": [
            {
                "fixer": "claude",
                "success": True,
                "summary": "should be omitted in nofix mode",
            }
        ],
    }

    artifact = build_agentic_v1_artifact(
        context=context,
        state=state,
        final_state=final_state,
    )

    assert artifact["schema"] == AGENTIC_V1_SCHEMA
    assert artifact["mode"] == "nofix"
    assert artifact["fix_attempts"] == []
    assert artifact["reviewers"] == [
        {
            "name": "codex",
            "role": "codex",
            "command": "/review",
            "status": "blocking",
            "finding_count": 1,
            "blocking_count": 1,
        }
    ]
    assert artifact["verdict"]["decision"] == "fail"
    assert len(artifact["adversarial_prompt"]) <= 2000
    evidence = artifact["findings"][0]["evidence"]
    assert "ghp_abcdefghijklmnopqrstuvwxyz0123456789" not in evidence
