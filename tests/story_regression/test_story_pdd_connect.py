from click.testing import CliRunner
import pytest

from pdd.commands.connect import connect


PDD_STORY_ID = "pdd_connect"
PDD_STORY_HASH = "263eed0bff2eb6f9"


@pytest.mark.story(story_id=PDD_STORY_ID)
def test_story_pdd_connect_cli_surface_is_available():
    result = CliRunner().invoke(connect, ["--help"])

    assert result.exit_code == 0
    assert "connect" in result.output.lower()
    assert "server" in result.output.lower()
