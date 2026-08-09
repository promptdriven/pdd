"""Reproduction tests for Issue #794: _extract_test_files() misses test files
from multi-commit bug steps, and _verify_tests_independently() only checks
files it is given (no full-directory scan).

These tests demonstrate:
1. Hash-based detection CAN find test files not in issue_content/changed_files
2. When hash detection is disabled (initial_file_hashes=None), those files are MISSED
3. _verify_tests_independently() only runs pytest on the files passed to it,
   so any file missed by _extract_test_files() escapes verification entirely.
"""
import os
import hashlib
from pathlib import Path
from typing import Dict, List, Optional
from unittest.mock import patch, MagicMock

import pytest

from pdd.agentic_e2e_fix_orchestrator import (
    _extract_test_files,
    _verify_tests_independently,
)


@pytest.fixture
def tmp_project(tmp_path):
    """Create a temporary project directory with test files on disk."""
    # Simulate two test files created by multi-commit bug workflow
    test1 = tmp_path / "test_trigger_logic.py"
    test1.write_text("def test_trigger(): assert True\n")

    test2 = tmp_path / "test_concurrent_label_race_issue_613.py"
    test2.write_text("def test_race(): assert True\n")

    return tmp_path


class TestExtractTestFilesHashDetection:
    """Test _extract_test_files with hash-based disk change detection."""

    def test_hash_detection_finds_new_test_files_on_disk(self, tmp_project):
        """When initial_file_hashes is provided (empty = nothing existed before),
        hash detection should discover new test files that appeared on disk,
        even if they are NOT in issue_content or changed_files.

        This simulates the 'second commit' scenario where commit 2 creates
        test_concurrent_label_race_issue_613.py but it is not tracked in
        issue_content or changed_files.
        """
        issue_content = ""  # No markers at all
        changed_files: List[str] = []  # Nothing tracked

        # initial_file_hashes is empty dict = snapshot before any test files existed
        initial_file_hashes: Dict[str, Optional[str]] = {}

        # Mock _get_file_hashes to return current state (both test files exist)
        current_hashes = {
            "test_trigger_logic.py": hashlib.md5(
                b"def test_trigger(): assert True\n"
            ).hexdigest(),
            "test_concurrent_label_race_issue_613.py": hashlib.md5(
                b"def test_race(): assert True\n"
            ).hexdigest(),
        }

        with patch(
            "pdd.agentic_e2e_fix_orchestrator._get_file_hashes",
            return_value=current_hashes,
        ):
            result = _extract_test_files(
                issue_content, changed_files, tmp_project, initial_file_hashes
            )

        # Both files should be found via hash detection
        assert "test_trigger_logic.py" in result
        assert "test_concurrent_label_race_issue_613.py" in result

    def test_discovers_test_files_when_initial_hashes_is_none(self, tmp_project):
        """When initial_file_hashes is None, the function should still discover
        test files that exist on disk via a directory scan or branch diff.

        Test files committed during pdd bug must be found regardless of whether
        hash detection is enabled. The fix should add a fallback discovery path
        (e.g., glob scan or git diff against base branch) so that committed test
        files are never missed.
        """
        issue_content = ""
        changed_files: List[str] = []

        # initial_file_hashes=None — function should still find test files
        result = _extract_test_files(
            issue_content, changed_files, tmp_project, initial_file_hashes=None
        )

        # After fix: test files on disk should be discovered
        assert len(result) > 0, (
            "Expected test files to be discovered even when hash detection is "
            "disabled. The function should have a fallback discovery path "
            "(e.g., directory scan) for committed test files. "
            f"Got: {result}"
        )

    def test_partial_tracking_finds_second_commit_file(self, tmp_project):
        """Simulate: commit 1 file is in changed_files, commit 2 file is not.
        After the fix, both files should be discovered via hash detection.

        In production, initial_file_hashes is always a dict (never None),
        so hash detection catches files created during the workflow even when
        they're not in changed_files or issue_content.
        """
        issue_content = ""
        # Only the first commit's file is tracked
        changed_files = ["test_trigger_logic.py"]

        # Production scenario: empty dict = snapshot before workflow started
        current_hashes = {
            "test_trigger_logic.py": hashlib.md5(
                b"def test_trigger(): assert True\n"
            ).hexdigest(),
            "test_concurrent_label_race_issue_613.py": hashlib.md5(
                b"def test_race(): assert True\n"
            ).hexdigest(),
        }
        with patch(
            "pdd.agentic_e2e_fix_orchestrator._get_file_hashes",
            return_value=current_hashes,
        ), patch(
            "pdd.agentic_e2e_fix_orchestrator._get_modified_and_untracked",
            return_value=[],
        ):
            result = _extract_test_files(
                issue_content, changed_files, tmp_project, initial_file_hashes={}
            )

        # Both files should be found after the fix
        assert "test_trigger_logic.py" in result
        assert "test_concurrent_label_race_issue_613.py" in result, (
            "Second commit file should be found via hash detection. "
            f"Got: {result}"
        )


class TestVerifyTestsIndependentlyScope:
    """Verify that _verify_tests_independently only checks files given to it,
    confirming that missed files from _extract_test_files escape verification.
    """

    def test_verify_only_runs_given_files(self, tmp_project):
        """_verify_tests_independently should only run pytest on the files
        explicitly passed to it. It does NOT do a directory scan.

        If _extract_test_files misses a file, _verify_tests_independently
        will never see it, and the orchestrator can report ALL_TESTS_PASS
        while missed test files still fail.
        """
        # Create a failing test file that should be caught but won't be
        failing_test = tmp_project / "test_concurrent_label_race_issue_613.py"
        failing_test.write_text(
            "def test_race_condition():\n    assert False, 'bug not fixed'\n"
        )

        # Only pass the first test file (simulating _extract_test_files missing the second)
        test_files_given = ["test_trigger_logic.py"]

        # Mock run_pytest_and_capture_output to return pass for the given file
        mock_result = {
            "test_results": [
                {
                    "passed": 1,
                    "failures": 0,
                    "errors": 0,
                    "standard_output": "1 passed",
                }
            ]
        }

        with patch(
            "pdd.agentic_e2e_fix_orchestrator.run_pytest_and_capture_output",
            return_value=mock_result,
        ) as mock_pytest:
            all_passed, output = _verify_tests_independently(
                test_files_given, tmp_project
            )

        # Verification reports ALL PASSED
        assert all_passed is True, (
            "Expected all_passed=True since we only gave it the passing file"
        )

        # Critically: pytest was NEVER called on the failing test file
        called_paths = [call.args[0] for call in mock_pytest.call_args_list]
        failing_abs_path = str(tmp_project / "test_concurrent_label_race_issue_613.py")
        assert failing_abs_path not in called_paths, (
            "The failing test file should NOT have been checked — "
            "_verify_tests_independently does not scan the directory"
        )

        # Only one file was checked
        assert len(called_paths) == 1
        assert called_paths[0] == str(tmp_project / "test_trigger_logic.py")

    def test_verify_catches_failing_test_on_disk(self, tmp_project):
        """End-to-end scenario: after the fix, _extract_test_files discovers all
        test files (including committed ones) via hash detection, and
        _verify_tests_independently detects failures in them.

        1. Two test files exist on disk (one failing)
        2. _extract_test_files discovers BOTH files (via hash detection)
        3. _verify_tests_independently checks both files
        4. Result: failure is detected, not a false ALL_TESTS_PASS
        """
        # Make the second test file a FAILING test
        failing_test = tmp_project / "test_concurrent_label_race_issue_613.py"
        failing_test.write_text(
            "def test_race_condition():\n    assert False, 'bug not fixed'\n"
        )

        # Step 1: Extract test files (production scenario: hash detection enabled)
        issue_content = ""
        changed_files = ["test_trigger_logic.py"]  # Only first commit tracked

        current_hashes = {
            "test_trigger_logic.py": hashlib.md5(
                b"def test_trigger(): assert True\n"
            ).hexdigest(),
            "test_concurrent_label_race_issue_613.py": hashlib.md5(
                b"def test_race_condition():\n    assert False, 'bug not fixed'\n"
            ).hexdigest(),
        }
        with patch(
            "pdd.agentic_e2e_fix_orchestrator._get_file_hashes",
            return_value=current_hashes,
        ), patch(
            "pdd.agentic_e2e_fix_orchestrator._get_modified_and_untracked",
            return_value=[],
        ):
            discovered_files = _extract_test_files(
                issue_content, changed_files, tmp_project, initial_file_hashes={}
            )

        # After fix: both files should be discovered
        assert len(discovered_files) >= 2, (
            f"Expected both test files to be discovered. Got: {discovered_files}"
        )
        assert "test_trigger_logic.py" in discovered_files
        assert "test_concurrent_label_race_issue_613.py" in discovered_files

        # Step 2: Verify all discovered files — mock shows failure for the failing test
        mock_result = {
            "test_results": [
                {
                    "passed": 0,
                    "failures": 1,
                    "errors": 0,
                    "standard_output": "1 failed",
                }
            ]
        }

        with patch(
            "pdd.agentic_e2e_fix_orchestrator.run_pytest_and_capture_output",
            return_value=mock_result,
        ):
            all_passed, output = _verify_tests_independently(
                discovered_files, tmp_project
            )

        # After fix: failure should be caught
        assert all_passed is False, (
            "Orchestrator should detect failing test in "
            "test_concurrent_label_race_issue_613.py, not report ALL_TESTS_PASS"
        )

    def test_empty_file_list_reports_all_passed(self, tmp_project):
        """If _extract_test_files returns empty list, _verify_tests_independently
        trivially reports all passed (vacuous truth). This is another edge case
        where the orchestrator can falsely report success.
        """
        all_passed, output = _verify_tests_independently([], tmp_project)

        # Empty list = vacuous truth = all_passed
        assert all_passed is True, (
            "Expected all_passed=True for empty file list (vacuous truth)"
        )
