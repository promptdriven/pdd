"""Runnable example for ``pdd.story_regression_gate`` (issue #1702).

Demonstrates the deterministic, public-safe story-regression gate:

* A user story (``user_stories/story__<id>.md``) is fresh when a regression
  test declares ``@pytest.mark.story(story_id=..., story_hash=...)`` whose
  ``story_hash`` equals the story's current content hash.
* The gate classifies each story as one of:
    - ``story-regression-ok``      -- fresh test exists
    - ``story-regression-missing`` -- no marked test resolves to the story
    - ``story-regression-stale``   -- the story changed after the test was made
* ``off`` skips, ``warn`` reports (exit 0), ``strict`` fails (exit 2) on any
  missing/stale story.

Inputs:  story markdown files + pytest test files (created here in a temp dir).
Outputs: ``StoryRegressionResult`` objects and a ``StoryRegressionGateResult``
         carrying ``mode``, ``ok`` (bool), and ``exit_code`` (int).

No LLM, cloud, or network access is used -- the decision is identical with or
without API credentials.
"""
import sys
import os
import tempfile

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.story_regression_gate import (
    STATUS_STORY_REGRESSION_MISSING,
    STATUS_STORY_REGRESSION_OK,
    STATUS_STORY_REGRESSION_STALE,
    classify_story,
    discover_story_markers,
    evaluate_stories,
    run_story_regression_gate,
    story_id_from_path,
)
from pdd.user_story_tests import _story_content_hash


def _write(path, text):
    """Write *text* to *path*, creating parent directories."""
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as handle:
        handle.write(text)


def build_fixture(root):
    """Create three stories and a tests dir exercising every status.

    Returns the (stories_dir, tests_dir) pair.
    """
    stories_dir = os.path.join(root, "user_stories")
    tests_dir = os.path.join(root, "tests")

    fresh_story = "# Story: refund restores balance\n\nA refund returns the charged amount.\n"
    stale_story = "# Story: checkout applies tax\n\nTax is added at checkout time.\n"
    missing_story = "# Story: export receipt\n\nThe user can export a PDF receipt.\n"

    _write(os.path.join(stories_dir, "story__refund.md"), fresh_story)
    _write(os.path.join(stories_dir, "story__checkout.md"), stale_story)
    _write(os.path.join(stories_dir, "story__export.md"), missing_story)

    # The "refund" test records the CURRENT hash -> fresh / ok.
    fresh_hash = _story_content_hash(fresh_story)
    # The "checkout" test records a STALE hash (story edited since) -> stale.
    stale_recorded_hash = "0000000000000000"

    test_source = (
        "import pytest\n\n"
        "@pytest.mark.story(story_id=\"refund\", story_hash=\"" + fresh_hash + "\")\n"
        "def test_refund_restores_balance():\n"
        "    assert True\n\n"
        "@pytest.mark.story(story_id=\"checkout\", story_hash=\"" + stale_recorded_hash + "\")\n"
        "def test_checkout_applies_tax():\n"
        "    assert True\n"
    )
    # Note: "export" has NO marked test on purpose -> missing.
    _write(os.path.join(tests_dir, "test_story_demo.py"), test_source)
    return stories_dir, tests_dir


def main():
    """Run the demonstration and print results; always exits 0."""
    with tempfile.TemporaryDirectory() as root:
        stories_dir, tests_dir = build_fixture(root)

        print("=== Discovered @pytest.mark.story markers (AST, no execution) ===")
        markers = discover_story_markers(tests_dir)
        for story_id in sorted(markers):
            marker = markers[story_id]
            print(
                "  story_id={0!r:<12} hash={1} -> {2}".format(
                    story_id, marker.story_hash, marker.test_name
                )
            )
        print()

        print("=== Per-story classification ===")
        results = evaluate_stories(stories_dir=stories_dir, tests_dir=tests_dir)
        for result in results:
            print(
                "  {0:<10} {1}".format(result.story_id, result.status)
            )
            print("             {0}".format(result.detail))
        print()

        # Sanity: confirm one of each status was produced.
        by_status = {r.story_id: r.status for r in results}
        assert by_status["refund"] == STATUS_STORY_REGRESSION_OK
        assert by_status["checkout"] == STATUS_STORY_REGRESSION_STALE
        assert by_status["export"] == STATUS_STORY_REGRESSION_MISSING

        print("=== classify_story on a single story (the fresh one) ===")
        single = classify_story(
            os.path.join(stories_dir, "story__refund.md"), markers
        )
        print("  story_id   :", single.story_id)
        print("  status     :", single.status)
        print("  current_hash:", single.current_hash)
        print("  recorded    :", single.recorded_hash)
        print()

        # The gate runs against the whole fixture (scope_to_diff=False avoids
        # needing a git repo for this standalone demo).
        print("=== Gate in 'warn' mode (reports, never fails) ===")
        warn = run_story_regression_gate(
            project_root=root,
            mode="warn",
            stories_dir=stories_dir,
            tests_dir=tests_dir,
            scope_to_diff=False,
        )
        print("  mode      :", warn.mode)
        print("  ok        :", warn.ok)
        print("  exit_code :", warn.exit_code)
        print("  offending :", [r.story_id for r in warn.offending])
        assert warn.ok is True and warn.exit_code == 0
        print()

        print("=== Gate in 'strict' mode (fails on missing/stale) ===")
        strict = run_story_regression_gate(
            project_root=root,
            mode="strict",
            stories_dir=stories_dir,
            tests_dir=tests_dir,
            scope_to_diff=False,
        )
        print("  mode      :", strict.mode)
        print("  ok        :", strict.ok)
        print("  exit_code :", strict.exit_code)
        print("  offending :", sorted(r.story_id for r in strict.offending))
        assert strict.ok is False and strict.exit_code == 2
        print()

        print("=== Gate in 'off' mode (skips entirely) ===")
        off = run_story_regression_gate(
            project_root=root,
            mode="off",
            stories_dir=stories_dir,
            tests_dir=tests_dir,
        )
        print("  mode      :", off.mode)
        print("  ok        :", off.ok)
        print("  exit_code :", off.exit_code)
        print("  results   :", len(off.results))
        assert off.ok is True and off.exit_code == 0 and off.results == ()
        print()

        print("story_id_from_path('story__pdd_sync.md') ->",
              story_id_from_path("story__pdd_sync.md"))
        print()
        print("All assertions passed. The gate is deterministic and needs no secrets.")


if __name__ == "__main__":
    main()
