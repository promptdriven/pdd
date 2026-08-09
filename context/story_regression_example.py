"""Example demonstrating deterministic pytest story<->test traceability.

This script showcases how to build the StoryTestMap from a test suite,
resolve story IDs from tests (and vice versa), and identify coverage gaps or stale markers.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path
from rich.console import Console

# Import the deterministic story regression tools
from pdd.story_regression import (
    build_story_map,
    stories_without_tests,
    markers_without_story,
)

console = Console()


def main() -> None: 
    # 1. Setup mock directories inside './output'
    output_dir = Path("./output")
    tests_dir = output_dir / "tests"
    stories_dir = output_dir / "user_stories"

    tests_dir.mkdir(parents=True, exist_ok=True)
    stories_dir.mkdir(parents=True, exist_ok=True)

    # 2. Create mock test files decorated with @pytest.mark.story
    # We define two tests: one for 'checkout_flow' and one for 'payment_flow'
    test_file = tests_dir / "test_checkout.py"
    test_file.write_text(
        "import pytest\n\n"
        "@pytest.mark.story('checkout_flow')\n"
        "def test_checkout_success():\n"
        "    assert True\n\n"
        "@pytest.mark.story(story_id='payment_flow')\n"
        "def test_payment_gateway():\n"
        "    assert True\n",
        encoding="utf-8",
    )

    # 3. Create mock user stories on disk
    # - 'checkout_flow' exists on disk and is covered by our test.
    # - 'shipping_flow' exists on disk but has NO claiming test (Coverage Gap).
    # Note: 'payment_flow' is claimed by a test but does NOT exist on disk (Stale Marker).
    (stories_dir / "story__checkout_flow.md").write_text("# Checkout Flow\n...", encoding="utf-8")
    (stories_dir / "story__shipping_flow.md").write_text("# Shipping Flow\n...", encoding="utf-8")

    console.print("[bold green]1. Building Story-Test Map via pytest collection...[/bold green]")
    # build_story_map initiates a safe 'pytest --collect-only' execution over the directory.
    # It imports tests to resolve markers but never runs test bodies or fixtures.
    #
    # Input:
    #   - tests_dir (PathLike | None): Path to the directory containing pytest regression tests.
    # Output:
    #   - StoryTestMap: An immutable, bidirectional registry mapping stories to tests.
    story_map = build_story_map(tests_dir=tests_dir)

    # 4. Query the Map
    console.print("\n[bold blue]2. Querying the Map[/bold blue]")
    
    # Get all stories claimed by at least one marker
    referenced_stories = story_map.referenced_story_ids
    console.print(f"Stories referenced in tests: {referenced_stories}")

    # Resolve tests for a specific story
    # Input: story_ref (str or Path) - the canonical story slug or the filepath
    # Output: set[str] of stable pytest node IDs relative to the test root
    checkout_tests = story_map.tests_for_story("checkout_flow")
    console.print(f"Tests for 'checkout_flow': {checkout_tests}")

    # Resolve the story ID associated with a specific test node ID
    # Input: nodeid (str) - the stable pytest node ID relative to the test root
    # Output: str | set[str] | None - the mapped story ID(s)
    test_node = "test_checkout.py::test_checkout_success"
    mapped_story = story_map.story_for_test(test_node)
    console.print(f"Story for '{test_node}': '{mapped_story}'")

    # Check existence predicate
    has_test = story_map.has_regression_test("checkout_flow")
    console.print(f"Does 'checkout_flow' have a regression test?: [green]{has_test}[/green]")

    # 5. Orphan and Discrepancy Detection
    console.print("\n[bold blue]3. Running Discrepancy Diagnostics[/bold blue]")

    # Find coverage gaps: stories defined on disk that are never claimed by a test
    # Input:
    #   - story_map (StoryTestMap): Our collected registry.
    #   - stories_dir (str | None): Directory containing the story markdown files.
    # Output:
    #   - set[str]: set of orphan story IDs.
    untested = stories_without_tests(story_map=story_map, stories_dir=str(stories_dir))
    console.print(
        f"[yellow]Coverage Gap[/yellow] (Stories on disk with no test): {untested}"
    )

    # Find stale markers: tests claiming stories that do not exist on disk (e.g. due to typos/renames)
    # Input:
    #   - story_map (StoryTestMap): Our collected registry.
    #   - stories_dir (str | None): Directory containing the story markdown files.
    # Output:
    #   - set[str]: set of invalid story IDs.
    stale = markers_without_story(story_map=story_map, stories_dir=str(stories_dir))
    console.print(
        f"[red]Validation Warning[/red] (Markers naming nonexistent stories): {stale}"
    )


if __name__ == "__main__":
    main()