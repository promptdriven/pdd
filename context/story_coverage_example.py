import os
import sys
from pathlib import Path

# Add the project root to the python path so we can import 'pdd'
PROJECT_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PROJECT_ROOT))

from pdd.story_coverage import emit_story_coverage

def main() -> None:
    # We will use the './output' directory to house our mock project structure
    mock_project_root = PROJECT_ROOT / "output"
    stories_dir = mock_project_root / "user_stories"
    tests_dir = mock_project_root / "tests"

    # Create directories
    stories_dir.mkdir(parents=True, exist_ok=True)
    tests_dir.mkdir(parents=True, exist_ok=True)

    # 1. Create a mock user story file
    # The file name must match the pattern 'story__*.md'
    story_file = stories_dir / "story__user_authentication.md"
    story_content = """# Story: User Authentication
As a registered user,
I want to log in securely,
So that I can access my dashboard.
"""
    story_file.write_text(story_content, encoding="utf-8")
    print(f"Created mock story: {story_file.relative_to(PROJECT_ROOT)}")

    # 2. Create a mock test file with pytest.mark.story
    # The test references the story ID ('user_authentication')
    test_file = tests_dir / "test_auth.py"
    test_content = """import pytest

@pytest.mark.story("user_authentication")
def test_login_success():
    assert True
"""
    test_file.write_text(test_content, encoding="utf-8")
    print(f"Created mock test: {test_file.relative_to(PROJECT_ROOT)}")

    # 3. Compute and emit story-regression coverage
    # This discovers the stories, scans tests for '@pytest.mark.story',
    # computes coverage metrics, writes JSON artifacts, and prints a summary.
    print("\n--- Running Story Coverage Emission ---")
    coverage_result = emit_story_coverage(
        project_root=mock_project_root,
        stories_dir=stories_dir,
        tests_dir=tests_dir,
        run_id="example_run_12345"
    )

    # 4. Examine the returned structured data
    print("\n--- Processed Metrics Details ---")
    print(f"Schema Version:     {coverage_result.schema_version}")
    print(f"Status:             {coverage_result.status}")
    print(f"Total Stories:      {coverage_result.story_count}")
    print(f"Covered Stories:    {coverage_result.stories_covered}")
    print(f"Coverage Percent:   {coverage_result.story_coverage_pct}%")
    print(f"Story Backed Tests: {coverage_result.story_backed_test_count}")

    # 5. Locate the generated JSON artifacts
    latest_artifact = mock_project_root / ".pdd" / "evidence" / "stories" / "coverage.latest.json"
    snapshot_artifact = mock_project_root / ".pdd" / "evidence" / "stories" / "runs" / "example_run_12345.json"

    print("\n--- Generated Artifacts ---")
    print(f"Latest coverage artifact: {latest_artifact.relative_to(PROJECT_ROOT)}")
    print(f"Snapshot run artifact:   {snapshot_artifact.relative_to(PROJECT_ROOT)}")


if __name__ == "__main__":
    main()
