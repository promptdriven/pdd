from click.testing import CliRunner
import pytest

from pdd.commands.modify import update


PDD_STORY_ID = "pdd_update"
PDD_STORY_HASH = "cf0bc4a2189f81bd"


@pytest.mark.story(story_id=PDD_STORY_ID)
def test_story_pdd_update_cli_surface_is_available():
    result = CliRunner().invoke(update, ["--help"])

    assert result.exit_code == 0
    assert "update" in result.output.lower()
    assert "sync" in result.output.lower()
