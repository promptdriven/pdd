from click.testing import CliRunner
import pytest

from pdd.commands.modify import change


PDD_STORY_ID = "pdd_change"
PDD_STORY_HASH = "3d3e24afdcf4ac7e"


@pytest.mark.story(story_id=PDD_STORY_ID)
def test_story_pdd_change_cli_surface_is_available():
    result = CliRunner().invoke(change, ["--help"])

    assert result.exit_code == 0
    assert "change" in result.output.lower()
    assert "issue" in result.output.lower()
