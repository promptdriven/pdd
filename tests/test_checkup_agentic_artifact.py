from __future__ import annotations

from pdd.checkup_agentic_artifact import (
    CANONICAL_FAIL_AGENTIC_NOT_AUTHORITATIVE,
    CANONICAL_PASS_AGENTIC_MIRROR_BLOCKING,
    CANONICAL_PASS_AGENTIC_MIRROR_CLEAN,
    CANONICAL_UNKNOWN_AGENTIC_FALLBACK_PASS,
    build_agentic_mirror_artifact,
    classify_canonical_result,
)


def test_classify_canonical_result_keeps_content_failure_authoritative() -> None:
    final_state = {
        "reviewer_status": {"codex": "clean"},
        "fresh_final_status": "clean",
        "findings": [
            {
                "status": "open",
                "severity": "critical",
                "finding": "missing regression test",
            }
        ],
    }

    assert (
        classify_canonical_result(
            success=False,
            message="Final gate failed with open findings.",
            final_state=final_state,
        )
        == "fail"
    )
    assert (
        classify_canonical_result(
            success=True,
            message="Canonical claimed success but final-state has open findings.",
            final_state=final_state,
        )
        == "fail"
    )


def test_classify_canonical_result_marks_provider_failure_unknown() -> None:
    assert (
        classify_canonical_result(
            success=False,
            message="Reviewer provider timed out before returning a verdict.",
        )
        == "unknown"
    )


def test_build_agentic_mirror_artifact_status_matrix() -> None:
    clean_state = {
        "reviewer_status": {"codex": "clean"},
        "fresh_final_status": "clean",
        "findings": [],
    }
    blocking_state = {
        "reviewer_status": {"codex": "clean"},
        "fresh_final_status": "clean",
        "findings": [
            {
                "status": "open",
                "reviewer": "codex",
                "severity": "critical",
                "area": "tests",
                "location": "tests/test_demo.py:1",
                "finding": "No regression test covers the fix.",
                "required_fix": "Add a failing-then-passing regression test.",
            }
        ],
    }

    base_kwargs = {
        "owner": "org",
        "repo": "repo",
        "pr_number": 7,
        "pr_url": "https://github.com/org/repo/pull/7",
        "issue_url": "https://github.com/org/repo/issues/6",
        "canonical_message": "canonical ok",
        "canonical_final_state": None,
        "mirror_prompt": "mirror canonical checkup",
        "reviewers": {"codex": "/review"},
        "mode": "fix",
        "total_cost": 0.5,
    }

    artifact = build_agentic_mirror_artifact(
        canonical_success=True,
        mirror_final_state=clean_state,
        **base_kwargs,
    )
    assert artifact["status"] == CANONICAL_PASS_AGENTIC_MIRROR_CLEAN
    assert artifact["verdict"]["decision"] == "pass"
    assert artifact["agentic_mirror"]["authoritative"] is False

    artifact = build_agentic_mirror_artifact(
        canonical_success=True,
        mirror_final_state=blocking_state,
        **base_kwargs,
    )
    assert artifact["status"] == CANONICAL_PASS_AGENTIC_MIRROR_BLOCKING
    assert artifact["verdict"]["decision"] == "fail"
    assert artifact["agentic_mirror"]["findings"][0]["suggested_fix"].startswith(
        "Add a"
    )

    artifact = build_agentic_mirror_artifact(
        canonical_success=False,
        canonical_message="provider timeout",
        mirror_final_state=clean_state,
        **{key: value for key, value in base_kwargs.items() if key != "canonical_message"},
    )
    assert artifact["status"] == CANONICAL_UNKNOWN_AGENTIC_FALLBACK_PASS
    assert artifact["verdict"]["decision"] == "pass"

    artifact = build_agentic_mirror_artifact(
        canonical_success=False,
        canonical_message="tests failed",
        mirror_final_state=None,
        **{key: value for key, value in base_kwargs.items() if key != "canonical_message"},
    )
    assert artifact["status"] == CANONICAL_FAIL_AGENTIC_NOT_AUTHORITATIVE
    assert artifact["verdict"]["decision"] == "fail"
