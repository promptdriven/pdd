from click.testing import CliRunner
import pytest

from pdd.commands.maintenance import sync


PDD_STORY_ID = "pdd_sync"
PDD_STORY_HASH = "db8793f0c80a101b"


@pytest.mark.story(story_id=PDD_STORY_ID)
def test_story_pdd_sync_cli_surface_is_available():
    result = CliRunner().invoke(sync, ["--help"])

    assert result.exit_code == 0
    assert "sync" in result.output.lower()
    assert "synchronize prompts with code and tests" in result.output.lower()
