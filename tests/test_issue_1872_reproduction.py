from pathlib import Path
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


def test_issue_1872_cli_prints_fail_with_no_fail_fast_and_exits_nonzero():
    """User-level repro: printed story FAIL lines must fail the CLI process."""
    runner = CliRunner()
    with runner.isolated_filesystem():
        prompts_dir = Path("prompts")
        stories_dir = Path("user_stories")

        prompts_dir.mkdir()
        stories_dir.mkdir()
        for prompt_name in (
            "provider_availability_routing.prompt",
            "provider_queue_dashboard.prompt",
            "provider_queue_notification.prompt",
        ):
            (prompts_dir / prompt_name).write_text("prompt", encoding="utf-8")
        for story_name in (
            "story__provider_availability_routing.md",
            "story__provider_queue_dashboard.md",
            "story__provider_queue_notification.md",
        ):
            (stories_dir / story_name).write_text(
                "As a user, I want provider queue behavior.",
                encoding="utf-8",
            )

        with patch("pdd.user_story_tests.detect_change") as mock_detect:
            mock_detect.side_effect = [
                ([], 0.01, "gemini/gemini-2.5-flash"),
                (
                    [
                        {
                            "prompt_name": "provider_queue_dashboard.prompt",
                            "change_instructions": "Prompt drifted from story.",
                        }
                    ],
                    0.02,
                    "gemini/gemini-2.5-flash",
                ),
                ([], 0.01, "gemini/gemini-2.5-flash"),
            ]

            result = runner.invoke(
                pdd_cli,
                [
                    "--no-core-dump",
                    "detect",
                    "--stories",
                    "--stories-dir",
                    str(stories_dir),
                    "--prompts-dir",
                    str(prompts_dir),
                    "--no-fail-fast",
                ],
            )

    assert result.exit_code != 0
    assert "PASS user_stories/story__provider_availability_routing.md" in result.output
    assert "FAIL user_stories/story__provider_queue_dashboard.md" in result.output
    assert "PASS user_stories/story__provider_queue_notification.md" in result.output


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
