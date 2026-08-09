from click.testing import CliRunner
import pytest

from pdd.commands.generate import test


PDD_STORY_ID = "pdd_test"
PDD_STORY_HASH = "8d7c10cc1b2ca908"


@pytest.mark.story(story_id=PDD_STORY_ID)
def test_story_pdd_test_cli_supports_story_generation_options():
    result = CliRunner().invoke(test, ["--help"])

    assert result.exit_code == 0
    assert "--issue" in result.output
    assert "--from-story" in result.output
