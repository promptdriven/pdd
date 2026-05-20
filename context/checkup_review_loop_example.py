"""Example interfaces and artifact contract for `pdd.checkup_review_loop`.

This file documents the public contract that callers and downstream verdict
adapters depend on. The runtime implementation lives in
`pdd/checkup_review_loop.py`; here we only spell out shapes, filenames, and
example payloads so other modules' prompts and tests can reason about the
interface without importing the real code.
"""

from __future__ import annotations

import os
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))


# ---------------------------------------------------------------------------
# Dataclasses (shape contract)
# ---------------------------------------------------------------------------


@dataclass
class ReviewFinding:
    """One actionable finding produced by a reviewer."""

    severity: str  # blocker | critical | medium | low | nit | info
    reviewer: str  # role that produced it (e.g., "codex", "claude")
    area: str  # file | module | workflow | prompt | example | architecture | test | security | billing | api | ux | maintainability
    evidence: str  # specific evidence text
    finding: str  # what is wrong
    required_fix: str  # what must change
    location: str = ""  # path:line or empty
    status: str = "open"  # "open" | "fixed"
    round_number: int = 0


@dataclass
class ReviewResult:
    """Normalized output from a single reviewer invocation."""

    reviewer: str
    status: str  # "clean" | "findings" | "failed" | "degraded" | "missing"
    issue_aligned: Optional[bool]
    findings: List[ReviewFinding] = field(default_factory=list)
    summary: str = ""
    raw_output: str = ""
    # Diagnostics surfaced on the final report when the reviewer fails or
    # degrades. ``status_classification`` is a short best-effort tag
    # (``auth``/``network``/``timeout``/``rate-limit``/``crash``/``unknown``).
    # ``status_exit_code`` is parsed best-effort from ``raw_output``
    # (``"no exit code"`` when absent). ``status_reason`` is the last
    # ~20 lines of stderr/stdout for operator triage.
    status_classification: str = ""
    status_exit_code: str = ""
    status_reason: str = ""


@dataclass
class FixResult:
    """Output of one fixer pass for a reviewer's findings.

    ``success`` is the bare fixer-subprocess return flag. It MUST NOT
    be rendered as a leading ``success``/``fixed`` token in the final
    report (issue #1088). The verification-boundary fields are
    populated by the loop around ``_commit_and_push_if_changed`` so the
    rendered ``### Fixes Attempted`` bullet can lead with the
    structured triple ``fixer_result=… push_status=… verification=…``
    rather than the untrusted prose.
    """

    fixer: str
    success: bool
    summary: str
    changed_files: List[str] = field(default_factory=list)
    raw_output: str = ""
    dispositions: Dict[str, str] = field(default_factory=dict)
    rationales: Dict[str, str] = field(default_factory=dict)
    # SHA-backed verification trust boundary (issue #1088).
    # ``fixer_result``: ``"attempted" | "skipped" | "failed"``.
    # ``push_status``: ``"pushed" | "push_failed" | "not_attempted"``.
    # SHAs come from ``git rev-parse HEAD`` in the worktree; the loop
    # MUST NOT infer them from fixer prose.
    fixer_result: Optional[str] = None
    push_status: Optional[str] = None
    local_fixer_commit_sha: Optional[str] = None
    pushed_head_sha: Optional[str] = None
    round_number: int = 0


@dataclass
class ReviewLoopConfig:
    """Configurable knobs for the loop. All have safe defaults."""

    reviewers: Sequence[str] = ("codex", "claude")
    reviewer: Optional[str] = None
    fixer: Optional[str] = None
    reviewer_fallback: Optional[str] = None
    review_only: bool = False
    max_rounds: int = 5
    max_cost: float = 50.0
    max_minutes: float = 90.0
    require_all_reviewers_clean: bool = True
    continue_on_reviewer_limit: bool = False
    require_final_fresh_review: bool = True
    timeout_adder: float = 0.0
    reasoning_time: Optional[float] = None
    blocking_severities: Tuple[str, ...] = ("blocker", "critical", "medium")
    clean_reviewer_states: Tuple[str, ...] = ("clean",)
    # APPENDED — when the primary reviewer ends in ``failed`` or
    # ``missing`` (NOT ``degraded`` — that means reduced quality,
    # don't silently lose signal), run a second review pass using the
    # fixer's identity as a fallback reviewer. The fallback's result
    # is recorded as a real reviewer row so the cloud verdict adapter
    # sees a clean real-reviewer entry rather than the legacy
    # ``fixer`` sentinel. The primary's original failure is preserved
    # in ``ReviewLoopState.reviewer_status_details`` with a
    # ``superseded_by_fallback="true"`` marker so the Reviewer
    # Diagnostics block in the rendered report still shows what
    # failed. MUST stay at the end of the field list so positional
    # callers (e.g., ``ReviewLoopConfig(reviewers, reviewer, fixer, …,
    # clean_reviewer_states)``) keep working unchanged — this contract
    # example mirrors the live dataclass at
    # ``pdd/checkup_review_loop.py``. Off by default.
    fallback_reviewer_on_failure: bool = False
    # Optional secondary fixer invoked at most once across the loop when
    # the primary fixer fails (e.g., subscription-tier credential exhausted).
    # Must differ from the primary fixer and the active reviewer. Kept at
    # the end of the field list so positional callers stay stable.
    fixer_fallback: Optional[str] = None


@dataclass
class ReviewLoopContext:
    """Issue and PR context passed into reviewer prompts."""

    issue_url: str
    issue_content: str
    repo_owner: str
    repo_name: str
    issue_number: int
    issue_title: str
    architecture_json: str
    pddrc_content: str
    pr_url: str
    pr_owner: str
    pr_repo: str
    pr_number: int
    project_root: Path
    pr_content: str = ""


@dataclass
class ReviewLoopState:
    """Mutable state accumulated across review-loop rounds."""

    total_cost: float = 0.0
    last_model: str = "unknown"
    reviewer_status: Dict[str, str] = field(default_factory=dict)
    active_reviewer: Optional[str] = None
    findings_by_key: Dict[str, ReviewFinding] = field(default_factory=dict)
    raw_outputs: List[Tuple[str, str]] = field(default_factory=list)
    fixes: List[FixResult] = field(default_factory=list)
    stop_reason: str = ""
    issue_aligned: Optional[bool] = None
    fresh_final_status: str = "missing"
    max_rounds_reached: bool = False
    max_cost_reached: bool = False
    max_duration_reached: bool = False
    fix_attempts_by_key: Dict[str, int] = field(default_factory=dict)
    dispute_notes_by_key: Dict[str, str] = field(default_factory=dict)
    reviewer_feedback_by_key: Dict[str, str] = field(default_factory=dict)
    reviewer_status_details: Dict[str, Dict[str, str]] = field(default_factory=dict)
    # Set lazily once ``fixer_fallback`` runs and succeeds; from that point on
    # every subsequent round drives the fix step with this role instead of the
    # exhausted primary. Parallel to ``active_reviewer``.
    active_fixer: Optional[str] = None
    # Originally configured primary reviewer captured at loop init and never
    # reassigned. ``active_reviewer`` rotates after a reviewer-fallback takeover;
    # this field preserves the original so the fixer-fallback exclusion check
    # can enforce the documented "must differ from --reviewer" rule even after
    # the active reviewer has rotated.
    original_reviewer: Optional[str] = None
    # SHA-backed verification trust boundary (issue #1088).
    # ``verified_head_sha``: PR head SHA the verifier most recently
    # reviewed as clean. Updated only when the verifier returns clean
    # on the SHA the fixer just pushed.
    # ``remote_pr_head_sha``: PR head SHA observed at final-report
    # render time via a single ``_fetch_pr_metadata`` re-fetch (R-V5).
    # ``verification_status_by_round``: per-round verifier outcome,
    # values in ``{"verified", "unverified", "stale", "skipped"}``.
    # ``reviewed_head_sha``: PR head SHA observed in the worktree at
    # the time the reviewer (primary, fallback, or review-only) ran.
    # Recorded directly from ``git rev-parse HEAD`` in the worktree
    # rather than from PR metadata, so a PR that advances between
    # checkout and the metadata fetch cannot poison the comparison
    # target ``_finalize`` uses at the R-V5 re-fetch.
    # ``final_refetch_attempted``: True when ``_finalize`` actually
    # ran the render-time remote-head re-fetch. Lets the render layer
    # distinguish a missing re-fetch (``remote-pr-head-sha: none``)
    # from a failed re-fetch (``remote-pr-head-sha: unknown``).
    verified_head_sha: Optional[str] = None
    remote_pr_head_sha: Optional[str] = None
    verification_status_by_round: Dict[int, str] = field(default_factory=dict)
    reviewed_head_sha: Optional[str] = None
    final_refetch_attempted: bool = False


# ---------------------------------------------------------------------------
# Public API (signature contract)
# ---------------------------------------------------------------------------


def parse_reviewers(value):
    """Parse legacy `--reviewers` CLI value into normalized role order.

    Aliases: chatgpt|openai -> codex; anthropic -> claude; google -> gemini.
    Unknown role names are dropped. An empty result falls back to
    `("codex", "claude")`.
    """
    return ("codex", "claude")


def run_checkup_review_loop(
    *,
    context: ReviewLoopContext,
    config: ReviewLoopConfig,
    cwd: Path,
    verbose: bool = False,
    quiet: bool = False,
    use_github_state: bool = True,
) -> Tuple[bool, str, float, str]:
    """Run a primary-reviewer/fixer PR loop and return final report data.

    Returns `(success, report_md, total_cost_usd, last_model)`. `success` is
    `True` whenever the loop produced a report. Ship/not-ready classification
    is the caller's job, derived from the `reviewer-status:` line in the
    report header. When `config.review_only` is true, this runs only the
    primary reviewer first pass and never invokes the fixer, commits, or pushes.
    """
    return True, "## Step 7/8: Review Loop Final Report", 0.0, "codex"


# ---------------------------------------------------------------------------
# Artifact contract (filenames + payload shapes that downstream tooling
# depends on; emitted under `<git_root>/.pdd/checkup-review-loop/issue-{N}-pr-{M}/`)
# ---------------------------------------------------------------------------


# Per role/round invocation, three files are written for reviewers/verifiers
# and three for fixers. The mode field is one of:
#   review | verify | fix | fallback
#
# When the opt-in ``--fallback-reviewer-on-failure`` flag promotes the fixer
# role to a fallback reviewer (because the primary ended in ``failed`` or
# ``missing``), the fallback pass writes artifacts using ``mode=fallback``
# and the fixer's role name (e.g., ``round-1-fallback-claude.prompt.txt``).
# A distinct ``fallback`` mode keeps the on-disk record auditable: the
# original primary attempt at ``round-N-review-<primary>.*`` is preserved
# unchanged, and the secondary pass is filed under its own mode rather
# than overwriting or aliasing the primary's slot.
#
# Reviewer/verifier files:
#   round-{N}-{mode}-{role}.prompt.txt    -- exact prompt sent to the role
#   round-{N}-{mode}-{role}.output.txt    -- raw LLM stdout
#   round-{N}-{mode}-{role}.findings.json -- normalized findings (List[Dict])
#
# Fixer files:
#   round-{N}-fix-{fixer}-for-{reviewer}.prompt.txt
#   round-{N}-fix-{fixer}-for-{reviewer}.output.txt
#   round-{N}-fix-{fixer}-for-{reviewer}.findings.json -- {"summary": str, "changed_files": [str], "dispositions": {...}, "rationales": {...}}
#
# Cumulative dedup snapshot (overwritten at each step within a round):
#   dedup-state-round-{N}.json -- list of normalized findings, one per dedup key
#
# Pre-push policy-guard refusal artifacts (written when the corresponding
# guard refuses; persisted alongside the round files so an operator can
# audit which discriminator fired):
#   round-{N}-prompt-source-guard-refusal.txt          -- clause 10a refusal text
#   round-{N}-architecture-registry-guard-refusal.txt  -- clause 10b refusal text
#
# Final outputs at end of loop:
#   final-report.md  -- exact bytes returned by run_checkup_review_loop;
#                       includes the optional ``### Reviewer Diagnostics``
#                       subsection (rendered only when
#                       ``reviewer_status_details`` is non-empty) with
#                       adapter-safe defanging applied to the reason tail
#   final-state.json -- canonical machine-readable verdict (see schema below)


EXAMPLE_NORMALIZED_FINDING: Dict[str, str] = {
    "key": "medium|tests/test_foo.py:1|the pr does not test the new workflow.|add a regression test in tests/test_foo.py covering x.",
    "severity": "medium",
    "reviewer": "codex",
    "area": "test",
    "evidence": "tests/test_foo.py is missing a regression test for X",
    "finding": "The PR does not test the new workflow.",
    "required_fix": "Add a regression test in tests/test_foo.py covering X.",
    "location": "tests/test_foo.py:1",
    "status": "open",
    "round_number": 1,
}


EXAMPLE_FIX_RESULT_PAYLOAD: Dict[str, object] = {
    "summary": "Added regression test and tightened the assertion.",
    "changed_files": ["tests/test_foo.py", "pdd/foo.py"],
    "dispositions": {
        EXAMPLE_NORMALIZED_FINDING["key"]: "fixed",
    },
    "rationales": {
        EXAMPLE_NORMALIZED_FINDING["key"]: "Added the missing regression coverage.",
    },
}


EXAMPLE_DEDUP_STATE_PAYLOAD: List[Dict[str, str]] = [EXAMPLE_NORMALIZED_FINDING]


EXAMPLE_REVIEWER_STATUS_DETAILS: Dict[str, Dict[str, str]] = {
    "codex": {
        "classification": "auth",
        "exit_code": "1",
        "reason": "Error: authentication failed",
        "status": "failed",
        "superseded_by_fallback": "true",
        "fallback_reviewer": "claude",
        "original_status": "failed",
    }
}


EXAMPLE_FINAL_STATE_PAYLOAD: Dict[str, object] = {
    "reviewer_status": {"codex": "clean", "claude": "fixer"},
    "active_reviewer": "codex",
    # Always present in ``final-state.json``. Empty on the happy path;
    # populated for any reviewer that ended in failed/degraded/missing
    # (see ``EXAMPLE_REVIEWER_STATUS_DETAILS`` above for the shape,
    # including the ``superseded_by_fallback`` marker that
    # ``--fallback-reviewer-on-failure`` writes).
    "reviewer_status_details": {},
    "fresh_final_status": "clean",
    "stop_reason": "Primary reviewer is satisfied after reviewing the fixer response.",
    "total_cost": 1.23,
    "last_model": "codex",
    "max_rounds_reached": False,
    "max_cost_reached": False,
    "max_duration_reached": False,
    "fix_attempts_by_key": {},
    "dispute_notes_by_key": {},
    "reviewer_feedback_by_key": {},
    # SHA-backed verification trust boundary (issue #1088). Always
    # present in ``final-state.json`` so downstream consumers can rely
    # on the schema rather than feature-detecting.
    "verified_head_sha": "0123456789abcdef0123456789abcdef01234567",
    "remote_pr_head_sha": "0123456789abcdef0123456789abcdef01234567",
    "reviewed_head_sha": "0123456789abcdef0123456789abcdef01234567",
    "verification_status_by_round": {"1": "verified"},
    "findings": [EXAMPLE_NORMALIZED_FINDING],
    # Each fix entry in ``final-state.json`` carries the structured
    # trust fields so downstream consumers can distinguish "fixer
    # attempted" from "verified on current PR head".
    "fixes": [
        {
            "fixer": "claude",
            "success": True,
            "summary": "Added regression test and tightened the assertion.",
            "changed_files": ["tests/test_foo.py", "pdd/foo.py"],
            "dispositions": {EXAMPLE_NORMALIZED_FINDING["key"]: "fixed"},
            "rationales": {
                EXAMPLE_NORMALIZED_FINDING["key"]: "Added the missing regression coverage.",
            },
            "round_number": 1,
            "fixer_result": "attempted",
            "push_status": "pushed",
            "local_fixer_commit_sha": "0123456789abcdef0123456789abcdef01234567",
            "pushed_head_sha": "0123456789abcdef0123456789abcdef01234567",
        }
    ],
}


# ---------------------------------------------------------------------------
# Final-report header contract
# ---------------------------------------------------------------------------


# The first non-blank line is always:
#   ## Step 7/8: Review Loop Final Report
#
# The header block (before any "###" section) MUST contain, in this order:
#   PR: <pr_url>
#   Issue: <issue_url>
#   issue_aligned: true|false
#   active-reviewer: <role>
#   reviewer-status: <role>=<status> ... fresh-final=<status>
#   fresh-final-review: clean|findings|failed|degraded|missing
#   verified-head-sha: <sha>|none
#   remote-pr-head-sha: <sha>|none|unknown
#   max-rounds-reached: true|false
#   max-cost-reached: true|false
#   max-duration-reached: true|false
#
# The active reviewer is the ship gate. The fixer role appears in the status
# line as `fixer` for traceability but does not independently review the PR.
# Tokens in {"failed", "degraded", "missing"} mean not-clean for the active
# reviewer; a superseded primary failure can remain visible after a clean
# fallback takeover. When that happens, the superseded primary's row in
# `### Per-Reviewer Status` is annotated with `(optional, superseded by
# <fallback>)` so downstream verdict adapters drop the failed primary from
# the required-reviewer set and resolve the report to `ship_degraded`
# instead of `unknown`.
#
# `verified-head-sha:` and `remote-pr-head-sha:` are the SHA-backed
# verification trust boundary (issue #1088). They are always present.
# `verified-head-sha` renders `none` when no verifier pass has cleared a
# pushed head this loop. `remote-pr-head-sha` renders `none` only when
# the final-report re-fetch was not needed (no verifier pin, no clean
# fresh-final reviewer status, no fixed findings, no recorded fixer
# push), `unknown` when an attempted re-fetch returned no head SHA
# (R-V5), and otherwise the observed remote PR head SHA. When the
# observed remote head differs from the SHA the verifier cleared,
# downstream verdict adapters MUST treat the report as stale even if
# `fresh-final-review:` would otherwise be `clean`.
#
# Each `### Fixes Attempted` bullet MUST be rendered in the fixed-field
# form `- round=<N> fixer=<role> fixer_result=<value>
# push_status=<value> local_sha=<short_sha_or_none>
# pushed_sha=<short_sha_or_none> changed_files=<files>
# verification=<value> [summary=<one-line-fixer-summary>]`. The bare
# fixer-subprocess return flag MUST NEVER appear as the leading status
# token (R-V7 — the #1088 failure mode).
#
# Fixer disagreement is not terminal. If the fixer returns `not_valid` or
# `blocked`, the active reviewer either accepts the rationale by omitting the
# finding on verification, or rejects it by re-reporting the finding with a
# reason that is passed back to the fixer. The loop stops after max rounds if
# the reviewer still sees required findings.
EXAMPLE_FINAL_REPORT_HEADER: str = (
    "## Step 7/8: Review Loop Final Report\n"
    "\n"
    "PR: https://github.com/owner/repo/pull/1\n"
    "Issue: https://github.com/owner/repo/issues/2\n"
    "issue_aligned: true\n"
    "active-reviewer: codex\n"
    "reviewer-status: codex=clean claude=fixer fresh-final=clean\n"
    "fresh-final-review: clean\n"
    "verified-head-sha: 0123456789abcdef0123456789abcdef01234567\n"
    "remote-pr-head-sha: 0123456789abcdef0123456789abcdef01234567\n"
    "max-rounds-reached: false\n"
    "max-cost-reached: false\n"
    "max-duration-reached: false\n"
)


def _demo() -> None:
    """Print the public contract this example documents."""
    import sys
    import os
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

    # Verify the runtime module exposes the documented public surface.
    from pdd.checkup_review_loop import (  # noqa: F401
        ReviewLoopContext,
        ReviewLoopConfig,
        ReviewLoopState,
        ReviewFinding,
        ReviewResult,
        FixResult,
        parse_reviewers,
        run_checkup_review_loop,
    )

    print("pdd.checkup_review_loop — public contract demo")
    print()
    print("Dataclasses exported:")
    for name in (
        "ReviewLoopContext",
        "ReviewLoopConfig",
        "ReviewLoopState",
        "ReviewFinding",
        "ReviewResult",
        "FixResult",
    ):
        print(f"  - {name}")
    print()
    print("Role aliases via parse_reviewers():")
    print(f"  parse_reviewers('chatgpt,anthropic') -> {parse_reviewers('chatgpt,anthropic')}")
    print(f"  parse_reviewers('openai,google')     -> {parse_reviewers('openai,google')}")
    print(f"  parse_reviewers(['codex', 'claude']) -> {parse_reviewers(['codex', 'claude'])}")
    print()
    print("Example final-report header:")
    print(EXAMPLE_FINAL_REPORT_HEADER)


if __name__ == "__main__":
    _demo()
