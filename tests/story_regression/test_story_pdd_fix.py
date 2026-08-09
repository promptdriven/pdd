from click.testing import CliRunner
import pytest

from pdd.commands.fix import fix


PDD_STORY_ID = "pdd_fix"
PDD_STORY_HASH = "b587af4ac2bc2176"


@pytest.mark.story(story_id=PDD_STORY_ID)
def test_story_pdd_fix_cli_surface_is_available():
    result = CliRunner().invoke(fix, ["--help"])

    assert result.exit_code == 0
    assert "fix" in result.output.lower()
    assert "story" in result.output.lower()
