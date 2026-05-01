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
