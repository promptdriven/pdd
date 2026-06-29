from __future__ import annotations

import os
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.commands.checkup import checkup


def test_checkup_review_loop_cli_forwards_reviewer_and_fixer_options() -> None:
    runner = CliRunner()

    with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
        run_checkup.return_value = (True, "clean", 0.25, "codex")

        result = runner.invoke(
            checkup,
            [
                "--pr",
                "https://github.com/org/repo/pull/7",
                "--issue",
                "https://github.com/org/repo/issues/6",
                "--review-loop",
                "--reviewer",
                "codex",
                "--fixer",
                "claude",
                "--reviewer-fallback",
                "gemini",
                "--max-review-rounds",
                "3",
                "--blocking-severities",
                "blocker,critical,medium",
            ],
            obj={"quiet": True, "verbose": False},
        )

    assert result.exit_code == 0
    kwargs = run_checkup.call_args.kwargs
    assert kwargs["review_loop"] is True
    assert kwargs["reviewer"] == "codex"
    assert kwargs["fixer"] == "claude"
    assert kwargs["reviewer_fallback"] == "gemini"
    assert kwargs["allow_same_reviewer_fixer"] is False
    assert kwargs["max_review_rounds"] == 3
    assert kwargs["blocking_severities"] == "blocker,critical,medium"


def test_checkup_review_loop_cli_forwards_same_role_flag() -> None:
    runner = CliRunner()

    with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
        run_checkup.return_value = (True, "clean", 0.25, "codex")

        result = runner.invoke(
            checkup,
            [
                "--pr",
                "https://github.com/org/repo/pull/7",
                "--issue",
                "https://github.com/org/repo/issues/6",
                "--review-loop",
                "--reviewer",
                "codex",
                "--fixer",
                "codex",
                "--allow-same-reviewer-fixer",
            ],
            obj={"quiet": True, "verbose": False},
        )

    assert result.exit_code == 0
    kwargs = run_checkup.call_args.kwargs
    assert kwargs["reviewer"] == "codex"
    assert kwargs["fixer"] == "codex"
    assert kwargs["allow_same_reviewer_fixer"] is True


def test_checkup_review_only_requires_review_loop() -> None:
    runner = CliRunner()

    result = runner.invoke(
        checkup,
        [
            "--pr",
            "https://github.com/org/repo/pull/7",
            "--issue",
            "https://github.com/org/repo/issues/6",
            "--review-only",
        ],
        obj={"quiet": True, "verbose": False},
    )

    assert result.exit_code == 2
    assert "--review-only requires --review-loop" in result.output


def test_checkup_start_step_forwards_override() -> None:
    runner = CliRunner()

    with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
        run_checkup.return_value = (True, "clean", 0.25, "codex")

        result = runner.invoke(
            checkup,
            [
                "--pr",
                "https://github.com/org/repo/pull/7",
                "--issue",
                "https://github.com/org/repo/issues/6",
                "--start-step",
                "7",
            ],
            obj={"quiet": True, "verbose": False},
        )

    assert result.exit_code == 0
    assert run_checkup.call_args.kwargs["start_step_override"] == 7


def test_checkup_start_step_rejected_with_review_loop() -> None:
    runner = CliRunner()

    result = runner.invoke(
        checkup,
        [
            "--pr",
            "https://github.com/org/repo/pull/7",
            "--issue",
            "https://github.com/org/repo/issues/6",
            "--review-loop",
            "--start-step",
            "7",
        ],
        obj={"quiet": True, "verbose": False},
    )

    assert result.exit_code == 2
    assert "--start-step applies to the legacy checkup workflow" in result.output


def test_checkup_test_scope_defaults_to_full() -> None:
    """Default `pdd checkup --pr` must keep the full-suite quality gate."""
    runner = CliRunner()

    with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
        run_checkup.return_value = (True, "clean", 0.25, "codex")

        result = runner.invoke(
            checkup,
            [
                "--pr",
                "https://github.com/org/repo/pull/7",
                "--issue",
                "https://github.com/org/repo/issues/6",
            ],
            obj={"quiet": True, "verbose": False},
        )

    assert result.exit_code == 0
    assert run_checkup.call_args.kwargs["test_scope"] == "full"


def test_checkup_test_scope_targeted_forwarded() -> None:
    runner = CliRunner()

    with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
        run_checkup.return_value = (True, "clean", 0.25, "codex")

        result = runner.invoke(
            checkup,
            [
                "--pr",
                "https://github.com/org/repo/pull/7",
                "--issue",
                "https://github.com/org/repo/issues/6",
                "--test-scope",
                "targeted",
            ],
            obj={"quiet": True, "verbose": False},
        )

    assert result.exit_code == 0
    assert run_checkup.call_args.kwargs["test_scope"] == "targeted"


def test_checkup_test_scope_targeted_requires_pr_mode() -> None:
    """Targeted scope only makes sense with --pr; issue mode rejects it."""
    runner = CliRunner()

    result = runner.invoke(
        checkup,
        [
            "https://github.com/org/repo/issues/6",
            "--test-scope",
            "targeted",
        ],
        obj={"quiet": True, "verbose": False},
    )

    assert result.exit_code == 2
    assert "--test-scope targeted requires --pr" in result.output


def test_checkup_test_scope_rejects_unknown_value() -> None:
    runner = CliRunner()

    result = runner.invoke(
        checkup,
        [
            "--pr",
            "https://github.com/org/repo/pull/7",
            "--issue",
            "https://github.com/org/repo/issues/6",
            "--test-scope",
            "quick",
        ],
        obj={"quiet": True, "verbose": False},
    )

    assert result.exit_code == 2
    assert "'quick'" in result.output or "test-scope" in result.output


# ---------------------------------------------------------------------------
# Issue #1292: make --issue optional in --pr mode (review a PR on its merits)
# ---------------------------------------------------------------------------


def test_checkup_pr_without_issue_runs_merit_review() -> None:
    """`pdd checkup --pr <url>` with no --issue must dispatch a merit review.

    Regression for #1292: PR mode previously hard-required --issue. With no
    issue, the command should still run and forward ``issue_url=None`` so the
    orchestrator reviews the PR on its own merits.
    """
    runner = CliRunner()

    with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
        run_checkup.return_value = (True, "clean", 0.25, "codex")

        result = runner.invoke(
            checkup,
            ["--pr", "https://github.com/org/repo/pull/7"],
            obj={"quiet": True, "verbose": False},
        )

    assert result.exit_code == 0, result.output
    kwargs = run_checkup.call_args.kwargs
    assert kwargs["pr_url"] == "https://github.com/org/repo/pull/7"
    assert kwargs["issue_url"] is None


def test_checkup_pr_with_issue_still_forwards_issue() -> None:
    """With --issue present, PR mode behaviour is unchanged (alignment review)."""
    runner = CliRunner()

    with patch("pdd.commands.checkup.run_agentic_checkup") as run_checkup:
        run_checkup.return_value = (True, "clean", 0.25, "codex")

        result = runner.invoke(
            checkup,
            [
                "--pr",
                "https://github.com/org/repo/pull/7",
                "--issue",
                "https://github.com/org/repo/issues/6",
            ],
            obj={"quiet": True, "verbose": False},
        )

    assert result.exit_code == 0, result.output
    kwargs = run_checkup.call_args.kwargs
    assert kwargs["issue_url"] == "https://github.com/org/repo/issues/6"


def test_checkup_issue_without_pr_rejected() -> None:
    """A bare --issue (no --pr) is rejected; a lone issue belongs in TARGET mode."""
    runner = CliRunner()

    result = runner.invoke(
        checkup,
        ["--issue", "https://github.com/org/repo/issues/6"],
        obj={"quiet": True, "verbose": False},
    )

    assert result.exit_code == 2
    assert "--issue requires --pr" in result.output


def test_checkup_review_loop_requires_issue() -> None:
    """--review-loop keeps requiring --issue (no-issue review loop deferred, #1292)."""
    runner = CliRunner()

    result = runner.invoke(
        checkup,
        [
            "--pr",
            "https://github.com/org/repo/pull/7",
            "--review-loop",
        ],
        obj={"quiet": True, "verbose": False},
    )

    assert result.exit_code == 2
    assert "--review-loop requires --pr and --issue" in result.output


def test_checkup_pr_without_issue_invalid_pr_url_rejected() -> None:
    """An invalid --pr URL is still rejected even when no --issue is supplied."""
    runner = CliRunner()

    result = runner.invoke(
        checkup,
        ["--pr", "not-a-pr-url"],
        obj={"quiet": True, "verbose": False},
    )

    assert result.exit_code == 2
    assert "--pr must be a GitHub pull-request URL" in result.output


# ---------------------------------------------------------------------------
# Issue #1292 acceptance criterion: a real end-to-end run of
# `pdd checkup --pr <PR>` with NO --issue. Opt-in (needs a live PR + gh +
# LLM credentials); skipped in normal/CI runs (`-m "not real"`). Runs with
# --no-fix and GitHub state disabled so it is strictly read-only.
# ---------------------------------------------------------------------------


@pytest.mark.e2e
@pytest.mark.real
def test_checkup_pr_without_issue_real() -> None:
    pr_url = os.environ.get("PDD_REAL_CHECKUP_PR_URL")
    if not pr_url:
        pytest.skip("Set PDD_REAL_CHECKUP_PR_URL to a live PR to run this test.")

    from pdd.agentic_checkup import run_agentic_checkup

    success, message, cost, model = run_agentic_checkup(
        None,  # no --issue: review the PR on its own merits
        pr_url=pr_url,
        no_fix=True,
        use_github_state=False,
        quiet=True,
    )

    # The run must reach a real verdict, not bail out on a missing issue.
    assert isinstance(success, bool)
    assert "Invalid GitHub issue URL" not in message
    assert "must both be provided" not in message
    assert isinstance(cost, float)
