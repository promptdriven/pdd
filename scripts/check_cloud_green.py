#!/usr/bin/env python3
"""Assert the cloud-test gate has already gone green for a release candidate.

The release used to run ``make cloud-test`` for the first time on release day.
That made the gate a discovery mechanism: every latent failure surfaced at the
worst possible moment, and each one restarted the release behind a full
fix/review/merge cycle. For v0.0.309 the gate went red twice mid-release; the
discoveries, fixes, and forced re-validation cost about 5.2 of that day's 11.5
hours.

``cloud-test-main.yml`` now runs the same gate on every push to main and on a
schedule, so by release time the answer already exists. This script reads the
run history and refuses the release unless the exact candidate commit is
already proven green and that proof is recent.

Reads the ``gh run list --json headSha,updatedAt,url`` payload on stdin so the
GitHub query stays in the Makefile and the decision stays testable.
"""

from __future__ import annotations

import argparse
import datetime
import json
import math
import subprocess
import sys
from dataclasses import dataclass
from typing import Callable, Iterable, Sequence


class CloudGreenError(Exception):
    """A candidate cannot be released against the recorded gate history."""


@dataclass(frozen=True)
class GreenRun:
    """One successful cloud-test run on main."""

    head_sha: str
    updated_at: datetime.datetime
    url: str

    def age_hours(self, now: datetime.datetime) -> float:
        """Hours elapsed since this run finished."""
        return (now - self.updated_at).total_seconds() / 3600.0


def parse_runs(payload: str) -> list[GreenRun]:
    """Parse a ``gh run list --json headSha,updatedAt,url`` payload.

    Raises CloudGreenError on anything unparseable rather than returning an
    empty list: an unreadable gate history must never look like a clean one.
    """
    text = payload.strip()
    if not text:
        raise CloudGreenError("gate history was empty; gh returned no output")
    try:
        raw = json.loads(text)
    except json.JSONDecodeError as exc:
        raise CloudGreenError(f"gate history was not valid JSON: {exc}") from exc
    if not isinstance(raw, list):
        raise CloudGreenError("gate history was not a JSON list of runs")

    runs: list[GreenRun] = []
    for entry in raw:
        if not isinstance(entry, dict):
            raise CloudGreenError("gate history contained a non-object run")
        try:
            head_sha = entry["headSha"]
            updated_at = entry["updatedAt"]
            url = entry["url"]
        except KeyError as exc:
            raise CloudGreenError(f"gate history run is missing {exc}") from exc
        try:
            parsed = datetime.datetime.fromisoformat(str(updated_at).replace("Z", "+00:00"))
        except ValueError as exc:
            raise CloudGreenError(
                f"gate history run {head_sha} has unparseable updatedAt {updated_at!r}"
            ) from exc
        if parsed.tzinfo is None:
            parsed = parsed.replace(tzinfo=datetime.timezone.utc)
        runs.append(GreenRun(head_sha=str(head_sha), updated_at=parsed, url=str(url)))
    return runs


def select_green(
    runs: Sequence[GreenRun],
    candidate_sha: str,
    max_age_hours: float,
    now: datetime.datetime,
) -> GreenRun:
    """Return the green run proving ``candidate_sha``, or explain the refusal."""
    if not runs:
        raise CloudGreenError(
            "no successful cloud-test-main.yml run found on main.\n"
            "  The cloud gate has never gone green here. Run it and wait:\n"
            "    gh workflow run cloud-test-main.yml --ref main"
        )

    matches = [run for run in runs if run.head_sha == candidate_sha]
    if not matches:
        raise CloudGreenError(
            f"no green cloud-test run for candidate {candidate_sha}.\n"
            f"{_format_recent(runs)}"
            "  If the gate is still running on this commit, wait for it.\n"
            "  If main is red, fix it through the normal PR loop — do not\n"
            "  patch the release worktree and do not skip this check."
        )

    # Several runs can share a SHA (a re-run, or a scheduled run landing on an
    # unchanged main). The newest proof is the one that matters.
    winner = max(matches, key=lambda run: run.updated_at)
    age = winner.age_hours(now)
    # Bound the age on BOTH sides. A negative age means the run is dated in the
    # future, i.e. the local clock is behind (VM resume, bad NTP). Testing only
    # the upper bound would make every green look arbitrarily fresh, and a
    # clock behind by more than the green's true age would pass unconditionally.
    if age < 0:
        raise CloudGreenError(
            f"green for {candidate_sha} is dated {-age:.1f}h in the future.\n"
            "  This machine's clock is behind the run timestamp, so freshness\n"
            "  cannot be judged. Fix the clock (check NTP) and retry."
        )
    if age > max_age_hours:
        raise CloudGreenError(
            f"green for {candidate_sha} is {age:.1f}h old, older than "
            f"CLOUD_GREEN_MAX_AGE_HOURS={max_age_hours:g}.\n"
            "  Re-run the gate:  gh workflow run cloud-test-main.yml --ref main"
        )
    return winner


def validate_max_age(value: float) -> float:
    """Reject a freshness bound that silently disables the freshness check.

    `inf`/`nan` both make every green look fresh — `nan` because every
    comparison against it is False. A non-positive bound can never be
    satisfied. Neither should be expressible by accident from the environment.
    """
    if math.isnan(value) or math.isinf(value):
        raise CloudGreenError(
            f"CLOUD_GREEN_MAX_AGE_HOURS={value} disables the freshness check; "
            "use a finite number of hours."
        )
    if value <= 0:
        raise CloudGreenError(
            f"CLOUD_GREEN_MAX_AGE_HOURS={value:g} can never be satisfied; "
            "use a positive number of hours."
        )
    return value


def _format_recent(runs: Iterable[GreenRun], limit: int = 5) -> str:
    """Render the newest green commits so the operator can retarget."""
    lines = ["  Most recent green commits on main:"]
    ordered = sorted(runs, key=lambda run: run.updated_at, reverse=True)
    for run in ordered[:limit]:
        stamp = run.updated_at.strftime("%Y-%m-%dT%H:%M:%SZ")
        lines.append(f"    {run.head_sha}  {stamp}  {run.url}")
    return "\n".join(lines) + "\n"


def newest_green_ancestor(
    runs: Sequence[GreenRun],
    is_ancestor: "Callable[[str], bool]",
    max_age_hours: float,
    now: datetime.datetime,
) -> GreenRun | None:
    """Return the newest fresh green run contained in the target history.

    The gate matches HEAD exactly — that is the safety property, and it is not
    negotiable, because `make release` tags HEAD. This helper exists only to
    make a refusal actionable: main takes a commit roughly every 7 minutes
    while the gate takes ~2 hours, so HEAD is rarely the blessed SHA. Pointing
    the operator at the newest proven ancestor lets them release proven work
    instead of stalling on an unproven tip.
    """
    fresh = [
        run
        for run in runs
        if 0 <= run.age_hours(now) <= max_age_hours and is_ancestor(run.head_sha)
    ]
    if not fresh:
        return None
    return max(fresh, key=lambda run: run.updated_at)


def git_ancestor_check(ref: str) -> "Callable[[str], bool]":
    """Build an ancestor predicate against ``ref`` using git.

    A SHA git cannot resolve (a run from a force-pushed or pruned commit)
    returns False rather than raising: an unknown commit is not a proven
    ancestor.
    """

    def _is_ancestor(sha: str) -> bool:
        result = subprocess.run(
            ["git", "merge-base", "--is-ancestor", sha, ref],
            capture_output=True,
            check=False,
        )
        return result.returncode == 0

    return _is_ancestor


def main(argv: Sequence[str] | None = None) -> int:
    """Verify the candidate against the gate history supplied on stdin."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate-sha", required=True)
    parser.add_argument("--max-age-hours", type=float, default=24.0)
    parser.add_argument(
        "--suggest-ancestor-of",
        default=None,
        help="On refusal, name the newest proven ancestor of this ref.",
    )
    args = parser.parse_args(argv)

    now = datetime.datetime.now(datetime.timezone.utc)

    # Parsed separately so a suggestion is still possible when only the
    # candidate match failed. A bad bound or unreadable history leaves nothing
    # to suggest from, and must not be papered over with a guess.
    try:
        max_age = validate_max_age(args.max_age_hours)
        runs = parse_runs(sys.stdin.read())
    except CloudGreenError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1

    try:
        winner = select_green(runs, args.candidate_sha, max_age, now)
    except CloudGreenError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        if args.suggest_ancestor_of:
            best = newest_green_ancestor(
                runs, git_ancestor_check(args.suggest_ancestor_of), max_age, now
            )
            if best is None:
                print(
                    f"\n  No proven ancestor of {args.suggest_ancestor_of} within "
                    f"{max_age:g}h either. Wait for the next gate run:\n"
                    "    gh workflow run cloud-test-main.yml --ref main",
                    file=sys.stderr,
                )
            else:
                print(
                    f"\n  Newest proven ancestor: {best.head_sha}"
                    f"  (age {best.age_hours(now):.1f}h)\n"
                    f"  {best.url}\n"
                    "  Release that commit instead — later commits ship next time:\n"
                    f"    git checkout --detach {best.head_sha}\n"
                    "    make release",
                    file=sys.stderr,
                )
        return 1

    print(
        f"Cloud gate green: {winner.head_sha}  "
        f"age={winner.age_hours(now):.1f}h  {winner.url}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
