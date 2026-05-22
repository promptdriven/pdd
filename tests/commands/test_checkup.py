from __future__ import annotations

from unittest.mock import patch

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
    assert kwargs["max_review_rounds"] == 3
    assert kwargs["blocking_severities"] == "blocker,critical,medium"


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
