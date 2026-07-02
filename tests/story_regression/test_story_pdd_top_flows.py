"""Story-backed public-safe smoke regressions for high-traffic PDD flows."""
from __future__ import annotations

import pytest
from click.testing import CliRunner

from pdd.cli import cli


def _help(command: str):
    return CliRunner().invoke(
        cli,
        ["--no-color", command, "--help"],
        obj={"quiet": True, "verbose": False, "core_dump": False},
    )


@pytest.mark.story(story_id="pdd_generate", story_hash="3660bcd6d6d7e8a8")
def test_story_pdd_generate_help_is_public_safe():
    result = _help("generate")
    assert result.exit_code == 0, result.output
    assert "generate" in result.output.lower()
    assert "--output" in result.output


@pytest.mark.story(story_id="pdd_sync", story_hash="db8793f0c80a101b")
def test_story_pdd_sync_help_is_public_safe():
    result = _help("sync")
    assert result.exit_code == 0, result.output
    assert "sync" in result.output.lower()
    assert "--no-github-state" in result.output


@pytest.mark.story(story_id="pdd_fix", story_hash="b587af4ac2bc2176")
def test_story_pdd_fix_help_is_public_safe():
    result = _help("fix")
    assert result.exit_code == 0, result.output
    assert "fix" in result.output.lower()
    assert "[ARGS]" in result.output
    assert "story-driven prompt fix" in result.output


@pytest.mark.story(story_id="pdd_change", story_hash="3d3e24afdcf4ac7e")
def test_story_pdd_change_help_is_public_safe():
    result = _help("change")
    assert result.exit_code == 0, result.output
    assert "change" in result.output.lower()
    assert "pdd change ISSUE_URL" in result.output


@pytest.mark.story(story_id="pdd_update", story_hash="d633c79daa412aae")
def test_story_pdd_update_help_is_public_safe():
    result = _help("update")
    assert result.exit_code == 0, result.output
    assert "update" in result.output.lower()
