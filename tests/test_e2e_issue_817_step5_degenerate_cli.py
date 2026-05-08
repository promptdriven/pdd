"""CLI-facing regression tests for issue #817.

These tests exercise the same public entry point a user runs:

    pdd generate <github-issue-url>

The LLM is mocked so Step 5 returns the degenerate response from the issue
("Done."). The expected behavior is a fast, user-visible Step 5 failure with no
Step 5b completeness-gate retries.
"""

from __future__ import annotations

import json
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd.cli import cli


@pytest.mark.e2e
def test_generate_issue_url_fails_fast_when_step5_returns_done(tmp_path, monkeypatch):
    """A degenerate Step 5 response must stop before Step 5b from the CLI path."""
    monkeypatch.chdir(tmp_path)

    step_calls: list[str] = []

    def mock_gh_api(args):
        assert args == ["api", "repos/owner/repo/issues/817"]
        return (
            True,
            json.dumps(
                {
                    "title": "Issue 817 regression",
                    "body": (
                        "Build a small application with enough requirements to "
                        "reach agentic architecture generation."
                    ),
                    "user": {"login": "tester"},
                    "comments_url": "",
                }
            ),
        )

    def mock_run_agentic_task(*args, **kwargs):
        label = kwargs.get("label", "")
        step_calls.append(label)
        if label == "step1b":
            return (
                True,
                "COMPLEXITY_RESULT: MANAGEABLE\nComplexity score: 2/14.",
                0.01,
                "mock-model",
            )
        if label == "step5":
            return True, "Done.", 0.01, "mock-model"
        return True, f"Output for {label}", 0.01, "mock-model"

    runner = CliRunner()
    with patch("pdd.agentic_architecture._check_gh_cli", return_value=True), patch(
        "pdd.agentic_architecture._run_gh_command", side_effect=mock_gh_api
    ), patch(
        "pdd.agentic_architecture._ensure_repo_context", return_value=(tmp_path, None)
    ), patch(
        "pdd.agentic_architecture_orchestrator.run_agentic_task",
        side_effect=mock_run_agentic_task,
    ):
        result = runner.invoke(
            cli,
            [
                "generate",
                "--no-github-state",
                "https://github.com/owner/repo/issues/817",
            ],
            env={"PDD_AUTO_UPDATE": "false"},
            obj={"verbose": False, "quiet": False},
        )

    assert result.exit_code == 0, result.output
    assert step_calls == [
        "step1",
        "step1b",
        "step2",
        "step2b",
        "step3",
        "step4",
        "step5",
    ]
    assert "Failed: Step 5 (module design) produced invalid output" in result.output
    assert "step 5 output is shorter than 200 characters" in result.output
    assert "Step 5b" not in result.output
