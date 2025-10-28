#!/usr/bin/env python3
"""
Test that PR link is included in the generated comment.
"""

from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).parent.parent))

from scripts.run_all_tests_with_results import TestRunner


def test_pr_link_in_comment():
    """Test that PR link appears in the generated comment."""
    
    # Create runner with PR information
    runner = TestRunner(
        Path.cwd(),
        pr_number="123",
        pr_url="https://github.com/gltanaka/pdd/pull/123"
    )
    
    # Set up mock test results
    runner.results = {
        "timestamp": "2025-01-15T10:00:00",
        "pr_number": "123",
        "pr_url": "https://github.com/gltanaka/pdd/pull/123",
        "test_suites": {
            "unit_tests": {
                "name": "Unit Tests",
                "exit_code": 0,
                "passed": 10,
                "failed": 0,
                "duration_seconds": 5.0,
                "failures": []
            }
        },
        "summary": {
            "total_passed": 10,
            "total_failed": 0,
            "total_skipped": 0,
            "duration_seconds": 5.0,
            "all_passed": True
        }
    }
    
    # Generate comment
    comment = runner.generate_github_comment()
    
    print("=" * 60)
    print("GENERATED COMMENT WITH PR LINK")
    print("=" * 60)
    print(comment)
    print("=" * 60)
    
    # Verify PR link is in the comment
    assert "https://github.com/gltanaka/pdd/pull/123" in comment, \
        "PR URL not found in comment"
    
    assert "Pull Request:" in comment, \
        "Pull Request label not found in comment"
    
    print("\nVERIFICATION PASSED")
    print("- PR URL is included in comment")
    print("- Pull Request label is present")
    
    # Test with just PR number (no URL)
    runner2 = TestRunner(Path.cwd(), pr_number="456")
    runner2.results = runner.results.copy()
    runner2.results["pr_number"] = "456"
    runner2.results["pr_url"] = None
    
    comment2 = runner2.generate_github_comment()
    
    print("\n" + "=" * 60)
    print("GENERATED COMMENT WITH PR NUMBER ONLY")
    print("=" * 60)
    print(comment2)
    print("=" * 60)
    
    assert "#456" in comment2, "PR number not found in comment"
    
    print("\nVERIFICATION PASSED")
    print("- PR number is included in comment")
    
    # Test without PR information
    runner3 = TestRunner(Path.cwd())
    runner3.results = runner.results.copy()
    runner3.results["pr_number"] = None
    runner3.results["pr_url"] = None
    
    comment3 = runner3.generate_github_comment()
    
    print("\n" + "=" * 60)
    print("GENERATED COMMENT WITHOUT PR INFO")
    print("=" * 60)
    print(comment3)
    print("=" * 60)
    
    assert "Pull Request:" not in comment3, \
        "PR info should not be in comment when not provided"
    
    print("\nVERIFICATION PASSED")
    print("- No PR info when not provided")
    
    print("\n" + "=" * 60)
    print("ALL TESTS PASSED")
    print("=" * 60)


if __name__ == "__main__":
    test_pr_link_in_comment()

