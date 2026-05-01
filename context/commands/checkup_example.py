from __future__ import annotations

import sys
from pathlib import Path
from unittest.mock import patch

from click.testing import CliRunner

project_root = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(project_root))

from pdd.commands.checkup import checkup


def example_github_issue_mode() -> None:
    """Run checkup in default GitHub issue mode with the agentic call mocked."""
    runner = CliRunner()
    with patch("pdd.commands.checkup.run_agentic_checkup") as mock_run:
        mock_run.return_value = (True, "Issue checkup complete", 1.25, "anthropic")

        result = runner.invoke(
            checkup,
            [
                "https://github.com/org/repo/issues/123",
                "--no-fix",
                "--no-github-state",
            ],
            obj={"quiet": False, "verbose": False},
        )

    print("GitHub issue mode exit code:", result.exit_code)
    print(result.output.strip())


def example_pr_review_loop_mode() -> None:
    """Run PR review-loop mode with the underlying checkup call mocked."""
    runner = CliRunner()
    with patch("pdd.commands.checkup.run_agentic_checkup") as mock_run:
        mock_run.return_value = (True, "PR review loop clean", 2.50, "codex")

        result = runner.invoke(
            checkup,
            [
                "--pr",
                "https://github.com/org/repo/pull/456",
                "--issue",
                "https://github.com/org/repo/issues/123",
                "--review-loop",
                "--reviewer",
                "codex",
                "--fixer",
                "claude",
                "--max-review-rounds",
                "3",
            ],
            obj={"quiet": False, "verbose": True},
        )

    print("PR review-loop mode exit code:", result.exit_code)
    print(result.output.strip())


def example_local_validation_mode() -> None:
    """Run local architecture validation mode with validation mocked."""
    runner = CliRunner()
    with patch(
        "pdd.architecture_include_validation.run_validate_arch_includes_cli"
    ) as mock_validate:
        mock_validate.return_value = None

        result = runner.invoke(
            checkup,
            [
                "--validate-arch-includes",
                "--project-root",
                str(project_root),
                "--strict",
            ],
            obj={"quiet": False, "verbose": False},
        )

    print("Local validation mode exit code:", result.exit_code)
    print(result.output.strip())


if __name__ == "__main__":
    example_github_issue_mode()
    example_pr_review_loop_mode()
    example_local_validation_mode()
