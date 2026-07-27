"""Contract tests for the risk-tiered PR review loop.

Of 91 PRs merged in the two weeks to 2026-07-26, 29 (32%) touched no product
code, at a median of one file each — every `preauthorize` bookkeeping PR, every
fixture stabilization, and the four prose-judge regex widenings that blocked
v0.0.307 for roughly 21 hours. Each paid up to three sequential full-diff
reviews, and any remediation invalidated the clean verdict and restarted the
count.

These tests pin the two properties that fix that (tiering and delta re-review)
and, just as importantly, pin the safety properties that must NOT be traded
away for speed.
"""

from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
RUNBOOK = ROOT / "docs" / "runbooks" / "pr-loop-process.md"


def runbook() -> str:
    """Return the PR loop runbook as checked-in text."""
    return RUNBOOK.read_text(encoding="utf8")


def section(start: str, end: str | None = None) -> str:
    """Extract a runbook section for ordering and content assertions."""
    text = runbook()
    begin = text.index(start)
    return text[begin : text.index(end, begin)] if end else text[begin:]


class TestRiskTiers:
    def test_both_tiers_are_defined_by_what_the_diff_touches(self):
        tiers = section("#### Risk tier", "#### Rounds")
        assert "Tier A" in tiers and "Tier B" in tiers
        # Tier A is keyed on shipped code, not on PR size or author judgement.
        for shipped in ("`pdd/`", "`scripts/`", "`ci/`", "`Makefile`"):
            assert shipped in tiers
        for bookkeeping in ("`tests/`", "`.pdd/`", "`docs/`"):
            assert bookkeeping in tiers

    def test_tier_b_gets_one_round_not_three(self):
        tiers = section("#### Risk tier", "#### Rounds")
        assert re.search(r"Run \*\*one\*\* review round", tiers)

    def test_tier_b_is_less_repetition_not_a_lower_bar(self):
        """The whole diff is still reviewed; only the repetition is cut."""
        tiers = section("#### Risk tier", "#### Rounds")
        compact = " ".join(tiers.split())
        assert "not a lower bar" in compact
        assert "whole diff exhaustively" in compact
        assert "same P1/P2 classification" in compact

    def test_tier_b_must_check_for_weakened_signal(self):
        # The failure mode of fast-tracking test changes is a test that stops
        # catching things. Name it explicitly.
        tiers = section("#### Risk tier", "#### Rounds")
        compact = " ".join(tiers.split())
        assert "weakens a signal" in compact
        assert "loosened assertion" in compact
        assert "widened allowlist" in compact

    def test_any_reviewer_can_promote_and_doubt_promotes(self):
        tiers = section("#### Risk tier", "#### Rounds")
        compact = " ".join(tiers.split())
        assert "may promote" in compact
        assert "When in doubt, promote." in compact


class TestDeltaReReview:
    def test_first_review_is_still_whole_diff(self):
        rounds = section("#### Rounds", "1. **Round 1")
        assert "inspects the whole diff exhaustively" in " ".join(rounds.split())

    def test_re_review_covers_the_delta_plus_its_blast_radius(self):
        rounds = " ".join(section("#### Rounds", "1. **Round 1").split())
        assert "delta since the previous verdict" in rounds
        assert "everything that delta can affect" in rounds
        # Blast radius must be spelled out, or "delta" degrades to "the lines".
        assert "callers of changed functions" in rounds

    def test_unbounded_blast_radius_falls_back_to_full_diff(self):
        rounds = " ".join(section("#### Rounds", "1. **Round 1").split())
        assert "cannot bound the blast radius" in rounds
        assert "reviews the full diff" in rounds

    def test_scope_is_recorded_in_the_verdict(self):
        text = runbook()
        assert "`full-diff`" in text and "delta-since-" in text

    def test_stopping_criterion_requires_full_coverage_with_no_gap(self):
        """Delta reviews must not leave any line unreviewed."""
        criteria = section("## Stopping criteria", "## Dispatch templates")
        compact = " ".join(criteria.split())
        assert "cover every line of the final diff" in compact
        assert "no gap between the last full review and HEAD" in compact

    def test_delta_reviewer_inherits_scope_but_not_judgement(self):
        compact = " ".join(runbook().split())
        assert "inherits *scope* from the previous round, never *judgement*" in compact


class TestSafetyPropertiesSurvive:
    """Speed must not be bought with any of these."""

    def test_reviewer_is_still_independent_and_read_only(self):
        compact = " ".join(runbook().split())
        assert "Remain read-only." in compact
        assert "do not inherit or merely confirm" in compact

    def test_review_rounds_stay_sequential_within_a_pr(self):
        # Rounds review the previous round's remediation, so parallelising them
        # would duplicate round 1 rather than add depth.
        compact = " ".join(section("## Concurrency policy", "## Autonomous workflow").split())
        assert "one Sol-high reviewer at a time per PR" in compact
        assert "would duplicate the first round" in compact

    def test_tier_a_cap_is_unchanged(self):
        compact = " ".join(runbook().split())
        assert "Never exceed three review rounds automatically." in compact

    def test_p1_and_p2_definitions_are_untouched(self):
        compact = " ".join(runbook().split())
        assert "**P1:** blocking correctness, security" in compact
        assert "**P2:** robustness, maintainability" in compact
