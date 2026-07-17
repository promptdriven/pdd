"""Example: build a bounded ``pdd.checkup.agentic.v1`` artifact from review-loop state.

Shows the pure data-assembly path — no subprocess/GitHub calls — plus the
authority resolution the hosted ``checkup_verdict_engine`` mirrors verbatim.
"""

import sys
from pathlib import Path
from types import SimpleNamespace

project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.checkup_agentic_artifact import (
    AGENTIC_AUTHORITY_STATUSES,
    AGENTIC_V1_SCHEMA,
    build_agentic_v1_artifact,
    _resolve_authority,
)


def main() -> None:
    """Demonstrate artifact assembly and authority resolution."""
    # Minimal stand-ins for ReviewLoopState / ReviewLoopConfig / ReviewLoopContext.
    loop_state = SimpleNamespace(
        reviewer_status={"codex": "clean", "claude": "fixer"},
        raw_outputs=[("codex", "blocker src/app.py:10 missing null check")],
        findings=[],
        fixes=[],
        fresh_final_status="clean",
        active_reviewer="codex",
        verified_head_sha="0123456789abcdef0123456789abcdef01234567",
        remote_pr_head_sha="0123456789abcdef0123456789abcdef01234567",
        reviewed_head_sha=None,
        stop_reason="",
        max_rounds_reached=False,
        max_cost_reached=False,
        max_duration_reached=False,
    )
    config = SimpleNamespace(
        review_only=False,
        no_fix=False,
        fresh_final_review_role="gemini",
        max_rounds=5,
        max_cost=50.0,
        max_minutes=90.0,
    )
    context = SimpleNamespace(
        pr_owner="promptdriven",
        pr_repo="pdd",
        repo_owner="promptdriven",
        repo_name="pdd",
        pr_number=1790,
    )
    final_gate_report = {"layer1_status": "pass", "blockers": []}

    artifact = build_agentic_v1_artifact(
        loop_state=loop_state,
        config=config,
        context=context,
        final_gate_report=final_gate_report,
    )

    print(f"schema_version : {artifact.schema_version} (== {AGENTIC_V1_SCHEMA})")
    print(f"mode           : {artifact.mode}")
    print(f"authority      : {artifact.authority}")
    print(f"reviewers      : {[(r.name, r.status, r.finding_count) for r in artifact.reviewers]}")
    print(f"findings       : {len(artifact.findings)}")
    print(f"fix_attempts   : {len(artifact.fix_attempts)} (empty in nofix mode)")

    # The authority vocabulary is closed and canonical-owned.
    assert artifact.authority in AGENTIC_AUTHORITY_STATUSES
    # A canonical fail is authoritative regardless of the agentic mirror outcome.
    assert (
        _resolve_authority("fail", agentic_blocking=False)
        == "canonical_fail_agentic_not_authoritative"
    )

    # Serialized JSON uses the ``schema_version`` key (never ``schema``).
    dumped = artifact.model_dump()
    assert "schema_version" in dumped and "schema" not in dumped


if __name__ == "__main__":
    main()
