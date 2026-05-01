"""Example interfaces and artifact contract for `pdd.checkup_review_loop`.

This file documents the public contract that callers and downstream verdict
adapters depend on. The runtime implementation lives in
`pdd/checkup_review_loop.py`; here we only spell out shapes, filenames, and
example payloads so other modules' prompts and tests can reason about the
interface without importing the real code.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple


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


@dataclass
class FixResult:
    """Output of one fixer pass for a reviewer's findings."""

    fixer: str
    success: bool
    summary: str
    changed_files: List[str] = field(default_factory=list)
    raw_output: str = ""
    dispositions: Dict[str, str] = field(default_factory=dict)
    rationales: Dict[str, str] = field(default_factory=dict)


@dataclass
class ReviewLoopConfig:
    """Configurable knobs for the loop. All have safe defaults."""

    reviewers: Sequence[str] = ("codex", "claude")
    reviewer: Optional[str] = None
    fixer: Optional[str] = None
    review_only: bool = False
    max_rounds: int = 5
    max_cost: float = 10.0
    max_minutes: float = 90.0
    require_all_reviewers_clean: bool = True
    continue_on_reviewer_limit: bool = False
    require_final_fresh_review: bool = True
    timeout_adder: float = 0.0
    reasoning_time: Optional[float] = None
    blocking_severities: Tuple[str, ...] = ("blocker", "critical", "medium")
    clean_reviewer_states: Tuple[str, ...] = ("clean",)


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
    findings_by_key: Dict[str, ReviewFinding] = field(default_factory=dict)
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
#   review | verify | fix
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
# Final outputs at end of loop:
#   final-report.md  -- exact bytes returned by run_checkup_review_loop
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


EXAMPLE_FINAL_STATE_PAYLOAD: Dict[str, object] = {
    "reviewer_status": {"codex": "clean", "claude": "fixer"},
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
    "findings": [EXAMPLE_NORMALIZED_FINDING],
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
#   reviewer-status: <role>=<status> ... fresh-final=<status>
#   fresh-final-review: clean|findings|failed|degraded|missing
#   max-rounds-reached: true|false
#   max-cost-reached: true|false
#   max-duration-reached: true|false
#
# The primary reviewer is the ship gate. The fixer role appears in the status
# line as `fixer` for traceability but does not independently review the PR.
# Tokens in {"failed", "degraded", "missing"} ALWAYS mean not-clean —
# provider-side outages must never silently ship.
#
# Fixer disagreement is not terminal. If the fixer returns `not_valid` or
# `blocked`, the primary reviewer either accepts the rationale by omitting the
# finding on verification, or rejects it by re-reporting the finding with a
# reason that is passed back to the fixer. The loop stops after max rounds if
# the reviewer still sees required findings.
EXAMPLE_FINAL_REPORT_HEADER: str = (
    "## Step 7/8: Review Loop Final Report\n"
    "\n"
    "PR: https://github.com/owner/repo/pull/1\n"
    "Issue: https://github.com/owner/repo/issues/2\n"
    "issue_aligned: true\n"
    "reviewer-status: codex=clean claude=fixer fresh-final=clean\n"
    "fresh-final-review: clean\n"
    "max-rounds-reached: false\n"
    "max-cost-reached: false\n"
    "max-duration-reached: false\n"
)
