from click.testing import CliRunner
import pytest

from pdd.commands.analysis import bug


PDD_STORY_ID = "pdd_bug"
PDD_STORY_HASH = "19e588bbffc02cf1"


@pytest.mark.story(story_id=PDD_STORY_ID)
def test_story_pdd_bug_cli_surface_is_available():
    result = CliRunner().invoke(bug, ["--help"])

    assert result.exit_code == 0
    assert "bug" in result.output.lower()
    assert "issue" in result.output.lower()
