from __future__ import annotations

import os
import sys
from pathlib import Path

# Ensure we can import from the public-pdd package path if needed
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from pdd.story_regression_gate import (
    run_story_regression_gate,
    STATUS_STORY_REGRESSION_MISSING,
    STATUS_STORY_REGRESSION_OK,
    STATUS_STORY_REGRESSION_STALE,
)
from pdd.user_story_tests import _story_content_hash

def setup_mock_project(project_root: Path) -> tuple[Path, Path]:
    """Creates a temporary workspace mirroring a typical project structure.

    Structure:
    ├── mock_project/
    │   ├── user_stories/
    │   │   └── story__sync_feature.md
    │   └── tests/
    │       └── test_sync.py
    """
    stories_dir = project_root / "user_stories"
    tests_dir = project_root / "tests"
    
    stories_dir.mkdir(parents=True, exist_ok=True)
    tests_dir.mkdir(parents=True, exist_ok=True)
    
    # 1. Create a user story
    story_content = """# Sync Feature

As a user, I want my offline data to automatically synchronize when
reconnecting to the internet.
"""
    story_file = stories_dir / "story__sync_feature.md"
    story_file.write_text(story_content, encoding="utf-8")
    
    # 2. Create a test file with a deliberately stale/incorrect hash
    test_content = """
import pytest

@pytest.mark.story(story_id="sync_feature", story_hash="stalehash12345678")
def test_sync_reconnect():
    pass
"""
    test_file = tests_dir / "test_sync.py"
    test_file.write_text(test_content, encoding="utf-8")
    
    return story_file, test_file

def main() -> None:
    # Target directory for output files relative to project root
    output_dir = Path("./output/gate_example_project").resolve()
    
    print("Setting up mock project directory structure...")
    story_file, test_file = setup_mock_project(output_dir)
    
    # Get the current fresh hash of our story content
    story_text = story_file.read_text(encoding="utf-8")
    fresh_hash = _story_content_hash(story_text)
    
    print(f"- Story ID derived: sync_feature")
    print(f"- Current story hash (computed): {fresh_hash}")
    
    # -----------------------------------------------------------------------
    # Case 1: Run the gate in 'warn' mode (non-blocking) with a stale hash
    # -----------------------------------------------------------------------
    print("\n--- Case 1: Executing gate in 'warn' mode with a stale test marker ---")
    warn_result = run_story_regression_gate(
        project_root=output_dir,
        mode="warn",
        stories_dir=str(output_dir / "user_stories"),
        tests_dir=str(output_dir / "tests"),
        scope_to_diff=False,  # Disable git-diff scoping to enforce full check
    )
    
    print(f"Gate overall OK: {warn_result.ok}")
    print(f"Gate Exit Code: {warn_result.exit_code}")
    for result in warn_result.results:
        print(f"\n[Result] Story ID: {result.story_id}")
        print(f"  Status: {result.status} (Expected: {STATUS_STORY_REGRESSION_STALE})")
        print(f"  Detail: {result.detail}")

    # -----------------------------------------------------------------------
    # Case 2: Run the gate in 'strict' mode (blocking) with a stale hash
    # -----------------------------------------------------------------------
    print("\n--- Case 2: Executing gate in 'strict' mode with a stale test marker ---")
    strict_result = run_story_regression_gate(
        project_root=output_dir,
        mode="strict",
        stories_dir=str(output_dir / "user_stories"),
        tests_dir=str(output_dir / "tests"),
        scope_to_diff=False,
    )
    
    print(f"Gate overall OK: {strict_result.ok} (Expected: False)")
    print(f"Gate Exit Code: {strict_result.exit_code} (Expected: 2)")
    
    # -----------------------------------------------------------------------
    # Case 3: Update the test to use the fresh hash and run again in 'strict'
    # -----------------------------------------------------------------------
    print("\n--- Case 3: Updating test marker to the matching hash and re-running ---")
    updated_test_content = f"""
import pytest

@pytest.mark.story(story_id="sync_feature", story_hash="{fresh_hash}")
def test_sync_reconnect():
    pass
"""
    test_file.write_text(updated_test_content, encoding="utf-8")
    
    strict_success_result = run_story_regression_gate(
        project_root=output_dir,
        mode="strict",
        stories_dir=str(output_dir / "user_stories"),
        tests_dir=str(output_dir / "tests"),
        scope_to_diff=False,
    )
    
    print(f"Gate overall OK: {strict_success_result.ok} (Expected: True)")
    print(f"Gate Exit Code: {strict_success_result.exit_code} (Expected: 0)")
    for result in strict_success_result.results:
        print(f"\n[Result] Story ID: {result.story_id}")
        print(f"  Status: {result.status} (Expected: {STATUS_STORY_REGRESSION_OK})")
        print(f"  Detail: {result.detail}")

if __name__ == "__main__":
    main()