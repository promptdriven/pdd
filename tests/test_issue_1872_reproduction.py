from unittest.mock import patch

from click.testing import CliRunner

from pdd.cli import cli as pdd_cli


def test_issue_1872_reproduction_failed_story_exits_nonzero():
    """Reproduce #1872: story-mode FAIL output must not exit 0."""
    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            False,
            [
                {
                    "story": "/tmp/issue1872_stories/story__provider_queue_dashboard.md",
                    "passed": False,
                    "prompt_files": ["prompts/provider_queue_dashboard.prompt"],
                },
            ],
            0.046212,
            "gemini/gemini-2.5-flash",
        )

        result = runner.invoke(
            pdd_cli,
            ["--no-core-dump", "detect", "--stories", "--no-fail-fast"],
        )

    assert result.exit_code != 0
    assert "gemini/gemini-2.5-flash" in result.output


def test_issue_1872_reproduction_fatal_story_exception_exits_nonzero():
    """Reproduce #1872: fatal story-mode exceptions must not exit 0."""
    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.side_effect = RuntimeError("provider auth failed")

        result = runner.invoke(pdd_cli, ["--no-core-dump", "detect", "--stories"])

    assert result.exit_code != 0
    assert "provider auth failed" in result.output


def test_issue_1872_reproduction_passing_stories_exit_zero():
    """Passing story-mode validation should remain a successful run."""
    runner = CliRunner()
    with patch("pdd.commands.analysis.run_user_story_tests") as mock_runner:
        mock_runner.return_value = (
            True,
            [
                {
                    "story": "/tmp/issue1872_stories/story__provider_availability_routing.md",
                    "passed": True,
                    "prompt_files": ["prompts/provider_availability_routing.prompt"],
                },
            ],
            0.01,
            "gemini/gemini-2.5-flash",
        )

        result = runner.invoke(pdd_cli, ["--no-core-dump", "detect", "--stories"])

    assert result.exit_code == 0
