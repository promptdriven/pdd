# pylint: disable=missing-module-docstring,missing-function-docstring
"""`pdd story verify` is the front door for story verification (#2389)."""

from unittest.mock import patch

from click.testing import CliRunner

from pdd.commands.story import story


def test_story_verify_is_registered_next_to_the_authoring_commands():
    result = CliRunner().invoke(story, ["--help"], obj={})

    assert result.exit_code == 0
    for name in ("add", "link", "list", "verify"):
        assert name in result.output


def test_story_verify_runs_the_same_story_evaluation_as_detect():
    """It must delegate, not fork: one implementation, two front doors."""
    with patch("pdd.commands.analysis.run_user_story_tests") as runner:
        runner.return_value = (True, [], 0.0, "test-model")
        result = CliRunner().invoke(
            story,
            ["verify", "--stories-dir", "user_stories", "--prompts-dir", "prompts"],
            obj={"quiet": True, "strength": 0.5},
        )

    assert result.exit_code == 0, result.output
    runner.assert_called_once()
    assert runner.call_args.kwargs["legacy_detect"] is False


def test_story_verify_forwards_the_legacy_escape_hatch():
    with patch("pdd.commands.analysis.run_user_story_tests") as runner:
        runner.return_value = (True, [], 0.0, "test-model")
        result = CliRunner().invoke(
            story, ["verify", "--legacy-detect"], obj={"quiet": True}
        )

    assert result.exit_code == 0, result.output
    assert runner.call_args.kwargs["legacy_detect"] is True
