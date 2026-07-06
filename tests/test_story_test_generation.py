from pathlib import Path

from pdd.story_regression import build_story_map
from pdd.story_regression_gate import (
    STATUS_MISSING,
    STATUS_PASSING,
    STATUS_STALE,
    evaluate_story_regression,
)
from pdd.story_test_generation import generate_story_regression_test


def _story(tmp_path: Path) -> Path:
    stories = tmp_path / "user_stories"
    contracts = stories / "contracts"
    contracts.mkdir(parents=True)
    story = stories / "story__checkout_refund.md"
    story.write_text(
        "# User Story: refund\n\n"
        "## Story\n\n"
        "A shopper can refund an eligible checkout.\n",
        encoding="utf-8",
    )
    (contracts / "checkout_refund.contract.md").write_text(
        "## Covers\n\n"
        "- R1\n\n"
        "## Oracle\n\n"
        "- Eligible checkout refunds are accepted.\n\n"
        "## Negative Cases\n\n"
        "- Ineligible checkout refunds are rejected.\n",
        encoding="utf-8",
    )
    return story


def test_generate_story_regression_test_is_marked_and_deterministic(tmp_path: Path) -> None:
    story = _story(tmp_path)

    first = generate_story_regression_test(story)
    second = generate_story_regression_test(story)

    assert first.changed is True
    assert second.changed is False
    text = first.test_file.read_text(encoding="utf-8")
    assert '@pytest.mark.story(story_id=PDD_STORY_ID)' in text
    assert 'PDD_STORY_ID = "checkout_refund"' in text
    assert "Eligible checkout refunds are accepted." in text
    assert "Ineligible checkout refunds are rejected." in text


def test_story_regression_gate_detects_missing_passing_and_stale(tmp_path: Path) -> None:
    story = _story(tmp_path)

    missing = evaluate_story_regression(
        story,
        tests_dir=tmp_path / "tests",
        story_map=build_story_map(tmp_path / "tests"),
    )
    assert missing.status == STATUS_MISSING

    generated = generate_story_regression_test(story)
    story_map = build_story_map(tmp_path / "tests")
    passing = evaluate_story_regression(story, tests_dir=tmp_path / "tests", story_map=story_map)
    assert passing.status == STATUS_PASSING
    assert generated.story_hash == passing.current_hash

    story.write_text(
        story.read_text(encoding="utf-8") + "\nThe refund must be idempotent.\n",
        encoding="utf-8",
    )
    stale = evaluate_story_regression(story, tests_dir=tmp_path / "tests", story_map=story_map)
    assert stale.status == STATUS_STALE


def test_generate_story_regression_test_rejects_malformed_story(tmp_path: Path) -> None:
    """A story with no Oracle/Acceptance/Story sections must fail loudly, not
    emit a vacuous raw-body-pin test (issue #1857 G3)."""
    import pytest

    stories = tmp_path / "user_stories"
    stories.mkdir(parents=True)
    story = stories / "story__malformed.md"
    story.write_text(
        "garbage content with no recognizable headings\n",
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match="has no ## Oracle"):
        generate_story_regression_test(story)

    # No test file may be left behind for the malformed story.
    assert not list(tmp_path.rglob("test_story_*.py"))
