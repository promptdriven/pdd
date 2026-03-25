"""Regression tests for Issue #953 / #722: _extract_test_files() directory scan
triggers even when regex (or other discovery paths) already found test files.

Root cause: the guard checked `len(test_files) == count_before_git` (whether the
git step added new files), not whether ANY files were already discovered. When
regex found a file and git found the same file (deduplicated), the count didn't
change, so the full directory scan triggered — pulling 241 files into
_verify_tests_independently() and causing 4+ hour verification times.

Fix: changed the guard to `if not test_files` so the directory scan is a true
last-resort fallback that only runs when all other discovery paths found nothing.
"""

from pathlib import Path
from typing import Dict, List, Optional
from unittest.mock import patch

import pytest

from pdd.agentic_e2e_fix_orchestrator import _extract_test_files


@pytest.fixture
def large_test_dir(tmp_path):
    """Create a project with 2 issue-specific test files and 50 unrelated ones.

    Simulates a real repo where regex finds the issue-specific files but the
    buggy guard would trigger a full scan of the tests/ directory.
    """
    tests_dir = tmp_path / "tests"
    tests_dir.mkdir()

    # The 2 files that regex should find from issue_content
    (tests_dir / "test_agentic_bug_orchestrator.py").write_text(
        "def test_bug(): assert True\n"
    )
    (tests_dir / "test_concurrent_label_race.py").write_text(
        "def test_race(): assert True\n"
    )

    # 50 unrelated test files that should NOT be pulled in
    for i in range(50):
        (tests_dir / f"test_unrelated_module_{i}.py").write_text(
            f"def test_m{i}(): assert True\n"
        )

    return tmp_path


class TestDirectoryScanDoesNotTriggerWhenFilesFound:
    """The directory scan must only run when NO discovery path found ANY files."""

    def test_regex_found_files_prevents_directory_scan(self, large_test_dir):
        """When regex extracts test files from issue_content, the directory scan
        must NOT trigger — even if git finds the same files (deduplicated).

        This is the exact bug from #953: regex found 1 file, git found the same
        file, count didn't change, directory scan triggered, 241 files returned.
        """
        issue_content = (
            "The fix modifies tests/test_agentic_bug_orchestrator.py "
            "and tests/test_concurrent_label_race.py to address the race."
        )

        # Mock _get_modified_and_untracked to return the SAME files regex found
        # (simulating git finding the same files → deduplication → count unchanged)
        with patch(
            "pdd.agentic_e2e_fix_orchestrator._get_modified_and_untracked",
            return_value=[
                "tests/test_agentic_bug_orchestrator.py",
                "tests/test_concurrent_label_race.py",
            ],
        ):
            result = _extract_test_files(
                issue_content,
                changed_files=[],
                cwd=large_test_dir,
                initial_file_hashes=None,
            )

        # Should return only the 2 issue-specific files, NOT all 52
        assert len(result) == 2, (
            f"Expected 2 issue-specific test files, got {len(result)}. "
            f"Directory scan likely triggered incorrectly. Files: {result}"
        )
        assert "tests/test_agentic_bug_orchestrator.py" in result
        assert "tests/test_concurrent_label_race.py" in result

    def test_changed_files_found_prevents_directory_scan(self, large_test_dir):
        """When changed_files contains test files, directory scan must not trigger.

        The sibling scan is also capped (>10 files skips the directory), so
        with 52 files in tests/ only the 1 changed file is returned.
        """
        with patch(
            "pdd.agentic_e2e_fix_orchestrator._get_modified_and_untracked",
            return_value=[],
        ):
            result = _extract_test_files(
                issue_content="",
                changed_files=["tests/test_agentic_bug_orchestrator.py"],
                cwd=large_test_dir,
                initial_file_hashes=None,
            )

        assert "tests/test_agentic_bug_orchestrator.py" in result
        # Should NOT have all 52 — both directory scan and sibling scan
        # are suppressed (sibling scan capped at 10 files per directory)
        assert len(result) == 1, (
            f"Expected only the 1 changed file, got {len(result)}. "
            f"Sibling or directory scan likely triggered incorrectly. Files: {result}"
        )

    def test_hash_detection_found_prevents_directory_scan(self, large_test_dir):
        """When hash detection finds test files, directory scan must not trigger."""
        current_hashes = {
            "tests/test_agentic_bug_orchestrator.py": "abc123",
        }
        with patch(
            "pdd.agentic_e2e_fix_orchestrator._get_file_hashes",
            return_value=current_hashes,
        ), patch(
            "pdd.agentic_e2e_fix_orchestrator._get_modified_and_untracked",
            return_value=[],
        ):
            result = _extract_test_files(
                issue_content="",
                changed_files=[],
                cwd=large_test_dir,
                initial_file_hashes={},  # empty = nothing existed before
            )

        assert "tests/test_agentic_bug_orchestrator.py" in result
        # Should NOT have all 52 files
        assert len(result) == 1, (
            f"Expected only the 1 hash-detected file, got {len(result)}. "
            f"Directory scan likely triggered incorrectly. Files: {result}"
        )


class TestDirectoryScanTriggersWhenNothingFound:
    """The directory scan MUST run when no other discovery path found anything."""

    def test_fallback_scan_runs_when_all_paths_empty(self, large_test_dir):
        """When issue_content is empty, changed_files is empty, hash detection
        is disabled, and git finds nothing — directory scan should find files.
        """
        with patch(
            "pdd.agentic_e2e_fix_orchestrator._get_modified_and_untracked",
            return_value=[],
        ):
            result = _extract_test_files(
                issue_content="",
                changed_files=[],
                cwd=large_test_dir,
                initial_file_hashes=None,
            )

        # All 52 test files should be found via directory scan
        assert len(result) == 52, (
            f"Expected all 52 test files from directory scan, got {len(result)}"
        )
