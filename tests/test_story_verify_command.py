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


def test_story_verify_exits_non_zero_when_a_story_fails():
    """Regression: the front door must go red on the failure it exists to catch.

    A plain story FAIL is signalled by RETURNING the payload to the group's
    result callback; `detect`'s own `raise Exit(1)` is guarded on
    `ctx.parent is None` and so cannot fire through `ctx.invoke`. Dropping the
    return value made `story verify` exit 0 while `detect --stories` exited 1.
    """
    from pdd.cli import cli

    failing = (
        False,
        [
            {
                "story": "user_stories/story__x.md",
                "passed": False,
                "changes": [
                    {
                        "prompt_name": "p.prompt",
                        "change_instructions": "AC1 is not satisfied",
                    }
                ],
            }
        ],
        0.01,
        "test-model",
    )

    codes = {}
    for name, args in (
        ("verify", ["story", "verify"]),
        ("detect", ["detect", "--stories"]),
    ):
        with patch("pdd.commands.analysis.run_user_story_tests", return_value=failing):
            result = CliRunner().invoke(cli, ["--quiet", *args, "--no-fail-fast"])
        codes[name] = result.exit_code

    assert codes["verify"] != 0, "story verify must not report success on a FAIL"
    assert codes["verify"] == codes["detect"], (
        f"the two front doors must agree on exit code: {codes}"
    )
