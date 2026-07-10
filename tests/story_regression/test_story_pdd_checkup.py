from click.testing import CliRunner
import pytest

from pdd.commands.checkup import checkup


PDD_STORY_ID = "pdd_checkup"
PDD_STORY_HASH = "c182aa91b22551eb"


@pytest.mark.story(story_id=PDD_STORY_ID)
def test_story_pdd_checkup_cli_exposes_coverage_and_gate():
    result = CliRunner().invoke(checkup, ["--help"])

    assert result.exit_code == 0
    assert "coverage" in result.output
    assert "gate" in result.output
