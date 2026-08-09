"""Runnable example for ``pdd.story_regression``.

Demonstrates the deterministic, marker-traceable story<->test API:

- ``build_story_map(tests_dir)`` -> :class:`StoryTestMap` built by pytest
  ``--collect-only`` (no test bodies run, no LLM call, no e2e side effects).
- ``tests_for_story(story_id) -> set[str]`` : node ids claiming a story.
- ``story_for_test(nodeid) -> str | set[str] | None`` : owning story id(s).
- ``has_regression_test(story_id) -> bool`` : coverage predicate.
- ``stories_without_tests`` / ``markers_without_story`` : orphan diagnostics.

The example fabricates a tiny ``tests/`` tree and ``user_stories/`` directory in
a temp folder so it runs standalone regardless of working directory. No external
services, no input, no network -- it exits 0.

Run:  ``python examples/story_regression_example.py``
"""
import os
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.story_regression import (  # noqa: E402  (sys.path set above)
    build_story_map,
    has_regression_test,
    markers_without_story,
    set_default_map,
    stories_without_tests,
    story_for_test,
    story_id,
    tests_for_story,
)

# A test file using BOTH marker forms the API normalizes:
#   - positional   @pytest.mark.story("checkout_flow")
#   - keyword      @pytest.mark.story(story_id="refund_flow")
#   - stacked      two markers on one test -> one test claims two stories
#   - typo/orphan  a marker naming a story with no story__<slug>.md on disk
SAMPLE_TEST_FILE = "\n".join(
    [
        "import pytest",
        "",
        "",
        '@pytest.mark.story("checkout_flow")',
        "def test_checkout_succeeds():",
        "    assert True",
        "",
        "",
        '@pytest.mark.story("checkout_flow")',
        "def test_checkout_rejects_empty_cart():",
        "    assert True",
        "",
        "",
        '@pytest.mark.story(story_id="refund_flow")',
        "def test_refund_issued():",
        "    assert True",
        "",
        "",
        '@pytest.mark.story("checkout_flow")',
        '@pytest.mark.story("refund_flow")',
        "def test_checkout_and_refund_interplay():",
        "    assert True",
        "",
        "",
        '@pytest.mark.story("typo_flwo")  # references a non-existent story file',
        "def test_orphan_marker():",
        "    assert True",
        "",
        "",
        "def test_unmarked():  # claims no story at all",
        "    assert True",
        "",
    ]
)


def main() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        tests_dir = root / "tests"
        tests_dir.mkdir()
        (tests_dir / "test_demo_stories.py").write_text(SAMPLE_TEST_FILE, encoding="utf-8")

        # Stories that exist on disk. Note: "checkout_flow" and "refund_flow"
        # exist; "shipping_flow" exists but has NO test; "typo_flwo" does NOT
        # exist (the marker above references it -> a validation warning).
        stories_dir = root / "user_stories"
        stories_dir.mkdir()
        for slug in ("checkout_flow", "refund_flow", "shipping_flow"):
            (stories_dir / f"story__{slug}.md").write_text(
                f"## Story\nAs a user I want {slug}.\n", encoding="utf-8"
            )

        # story_id: filename slug is the single identity space.
        print("story_id('user_stories/story__checkout_flow.md') ->",
              story_id(stories_dir / "story__checkout_flow.md"))
        print()

        # Build the map by collection only (the inner pytest run lists items but
        # executes none of the assert bodies above).
        story_map = build_story_map(tests_dir)
        # Install it as the default so the bare resolver functions use it too.
        set_default_map(story_map)

        print("=== tests_for_story (story -> {nodeid}) ===")
        for slug in ("checkout_flow", "refund_flow", "shipping_flow"):
            nodes = sorted(tests_for_story(slug))
            print(f"  {slug}: {nodes}")
        print()

        # checkout_flow is claimed by 3 tests (incl. the stacked one).
        assert len(tests_for_story("checkout_flow")) == 3, tests_for_story("checkout_flow")

        print("=== story_for_test (nodeid -> story | {stories} | None) ===")
        single = "test_demo_stories.py::test_refund_issued"
        multi = "test_demo_stories.py::test_checkout_and_refund_interplay"
        unmarked = "test_demo_stories.py::test_unmarked"
        print(f"  single-claim : {story_for_test(single)!r}")
        print(f"  multi-claim  : {sorted(story_for_test(multi))!r}")
        print(f"  unmarked     : {story_for_test(unmarked)!r}")
        print()

        # One story -> str; many stories -> set; no story -> None.
        assert story_for_test(single) == "refund_flow"
        assert story_for_test(multi) == {"checkout_flow", "refund_flow"}
        assert story_for_test(unmarked) is None

        print("=== has_regression_test (coverage predicate) ===")
        for slug in ("checkout_flow", "shipping_flow"):
            print(f"  {slug}: {has_regression_test(slug)}")
        print()
        assert has_regression_test("checkout_flow") is True
        assert has_regression_test("shipping_flow") is False  # story exists, no test

        print("=== orphan diagnostics ===")
        # shipping_flow has a story file but no claiming test:
        no_tests = stories_without_tests(story_map, stories_dir=str(stories_dir))
        print(f"  stories_without_tests : {sorted(no_tests)}")
        # typo_flwo is named by a marker but has no story file on disk:
        bad_markers = markers_without_story(story_map, stories_dir=str(stories_dir))
        print(f"  markers_without_story : {sorted(bad_markers)}")
        print()
        assert no_tests == {"shipping_flow"}
        assert bad_markers == {"typo_flwo"}

        print("OK: deterministic story<->test traceability verified.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
