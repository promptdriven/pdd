from pathlib import Path

import pytest

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


def test_generate_routes_to_behavioral_generator_when_entry_point_present(tmp_path: Path) -> None:
    """When the contract declares a ## Entry Point, `pdd test --from-story`
    (generate_story_regression_test) must produce a *behavioral* test that
    calls the entry point and asserts over `result`, not a text-pin."""
    stories = tmp_path / "user_stories"
    contracts = stories / "contracts"
    contracts.mkdir(parents=True)
    (stories / "story__checkout_total.md").write_text(
        "# User Story: checkout_total\n\n## Story\n\nAs a shopper, I can see my total.\n",
        encoding="utf-8",
    )
    (contracts / "checkout_total.contract.md").write_text(
        "# Contract\n\n## Covers\n- R1: total\n\n"
        "## Entry Point\n- module: checkout_app\n- callable: checkout_total\n"
        "- args: [1, 2]\n- kwargs: {}\n\n"
        "## Seams\n- checkout_app.TAX_RATE = 0\n\n"
        '## Oracle\n- result["total"] == 3\n',
        encoding="utf-8",
    )

    result = generate_story_regression_test(stories / "story__checkout_total.md")
    text = result.test_file.read_text(encoding="utf-8")
    assert "result = story_result" in text  # behavioral: invokes the entry point
    assert "@pytest.mark.story(story_id=STORY_ID, story_hash=STORY_HASH)" in text


def test_generate_text_pins_when_no_entry_point(tmp_path: Path) -> None:
    """A contract without an ## Entry Point still yields the text-pinning test."""
    story = _story(tmp_path)  # helper builds a contract with Oracle but no Entry Point
    result = generate_story_regression_test(story)
    text = result.test_file.read_text(encoding="utf-8")
    assert "_bundle_hash() == PDD_STORY_HASH" in text
    assert "result = story_result" not in text


def test_empty_entry_point_errors_instead_of_silent_text_pin(tmp_path: Path) -> None:
    """C-F7 (pdd#1889): a contract that declares ``## Entry Point`` but has an
    EMPTY body must surface the existing validation error, not silently degrade
    to a text-pin (which would give the user a false behavioral oracle)."""
    stories = tmp_path / "user_stories"
    contracts = stories / "contracts"
    contracts.mkdir(parents=True)
    (stories / "story__checkout_total.md").write_text(
        "# User Story: checkout_total\n\n## Story\n\nAs a shopper, I can see my total.\n",
        encoding="utf-8",
    )
    # ## Entry Point present but with NO `- module:`/`- callable:` body yet.
    (contracts / "checkout_total.contract.md").write_text(
        "# Contract\n\n## Covers\n- R1: total\n\n"
        "## Entry Point\n\n"
        '## Oracle\n- result["total"] == 3\n',
        encoding="utf-8",
    )
    with pytest.raises(ValueError, match="Entry Point"):
        generate_story_regression_test(stories / "story__checkout_total.md")
    # And it must NOT have silently emitted a text-pin test.
    assert not (tmp_path / "tests" / "story_regression").exists()


def test_generate_story_regression_test_rejects_malformed_story(tmp_path: Path) -> None:
    """A story with no ## Oracle / ## Acceptance Criteria / ## Story clauses must
    raise rather than emit a tautological (self-satisfying) test."""
    stories = tmp_path / "user_stories"
    stories.mkdir(parents=True)
    bad = stories / "story__bad.md"
    bad.write_text("garbage no sections here", encoding="utf-8")

    with pytest.raises(ValueError, match="no ## Oracle"):
        generate_story_regression_test(bad)
    assert not (tmp_path / "tests" / "story_regression").exists()


def test_generate_story_regression_test_pins_story_sentence_without_contract(tmp_path: Path) -> None:
    """A well-formed human story (## Story only, no contract) still generates,
    pinning the story sentence rather than the whole raw file."""
    stories = tmp_path / "user_stories"
    stories.mkdir(parents=True)
    story = stories / "story__demo.md"
    story.write_text(
        "# User Story: demo\n\n## Story\n\nAs a user, I can run the demo.\n",
        encoding="utf-8",
    )

    result = generate_story_regression_test(story)
    text = result.test_file.read_text(encoding="utf-8")
    assert "As a user, I can run the demo." in text


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
