from click.testing import CliRunner
import pytest

from pdd.commands.generate import generate


PDD_STORY_ID = "pdd_generate"
PDD_STORY_HASH = "91888ea32bde8616"


@pytest.mark.story(story_id=PDD_STORY_ID)
def test_story_pdd_generate_cli_surface_is_available():
    result = CliRunner().invoke(generate, ["--help"])

    assert result.exit_code == 0
    assert "Create runnable code from a prompt file" in result.output
    assert "PROMPT_FILE" in result.output
