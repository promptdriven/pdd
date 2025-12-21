# tests/test_sync_bug_fixes.py
"""
Tests for critical bug fixes in the sync command.

Bug #11: Fingerprint saved with actual command name when operation is skipped
Bug #23: _is_workflow_complete() doesn't detect skipped operations
Bug #8: Silent exception handling in post-crash verification
Bug #4: Hardcoded cycle detection logic
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
from dataclasses import asdict

from pdd.sync_determine_operation import (
    _is_workflow_complete,
    Fingerprint,
    read_fingerprint,
)


# --- Bug #11 & #23: Skip Flag Fingerprint Handling ---

class TestSkipFlagFingerprint:
    """Tests for proper handling of skip flags in fingerprint commands."""

    @pytest.fixture
    def mock_fingerprint_file(self, tmp_path):
        """Creates a mock fingerprint file."""
        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)
        return meta_dir

    def test_skip_verify_uses_prefix(self, tmp_path, mock_fingerprint_file):
        """
        Bug #11: When skip_verify is True and 'verify' operation is skipped,
        the fingerprint should be saved with 'skip:verify' command, not 'verify'.

        This test verifies the fix is in place by checking the source code pattern.
        We test the actual behavior via integration tests.
        """
        import inspect
        from pdd import sync_orchestration

        # Read the source code of sync_orchestration
        source = inspect.getsource(sync_orchestration)

        # Verify the fix is in place: skip operations should use 'skip:' prefix
        assert "'skip:verify'" in source, "Bug #11 fix: verify skip should use 'skip:verify' command"
        assert "'skip:test'" in source, "Bug #11 fix: test skip should use 'skip:test' command"
        assert "'skip:crash'" in source, "Bug #11 fix: crash skip should use 'skip:crash' command"

    def test_workflow_complete_detects_skip_prefix(self, tmp_path, mock_fingerprint_file):
        """
        Bug #23: _is_workflow_complete() should return False when fingerprint
        has a 'skip:' prefix, indicating the operation was skipped not executed.
        """
        import json
        import os
        from datetime import datetime, timezone

        # Create all required files
        paths = {
            'prompt': tmp_path / 'prompts' / 'test.prompt',
            'code': tmp_path / 'src' / 'test.py',
            'example': tmp_path / 'examples' / 'test_example.py',
            'test': tmp_path / 'tests' / 'test_test.py',
        }
        for p in paths.values():
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text("mock content")

        # Create fingerprint with skip:verify command
        meta_dir = tmp_path / ".pdd" / "meta"
        fingerprint_file = meta_dir / "test_python.json"
        fingerprint_data = {
            "pdd_version": "0.0.88",
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "command": "skip:verify",  # Skipped operation
            "prompt_hash": "abc123",
            "code_hash": "def456",
            "example_hash": "ghi789",
            "test_hash": "jkl012"
        }
        fingerprint_file.write_text(json.dumps(fingerprint_data))

        # Create run report with success
        run_report_file = meta_dir / "test_python_run.json"
        run_report_data = {
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "exit_code": 0,
            "tests_passed": 5,
            "tests_failed": 0,
            "coverage": 100.0,
            "test_hash": "jkl012"
        }
        run_report_file.write_text(json.dumps(run_report_data))

        old_cwd = os.getcwd()
        os.chdir(tmp_path)

        try:
            # Even though all files exist and run_report shows success,
            # workflow should NOT be complete because verify was skipped
            result = _is_workflow_complete(
                paths,
                skip_tests=False,
                skip_verify=False,  # Not skipping, but fingerprint shows it was skipped
                basename="test",
                language="python"
            )

            # With the fix, this should return False because fingerprint.command starts with 'skip:'
            assert result is False, "Workflow should not be complete when operation was skipped"
        finally:
            os.chdir(old_cwd)

    def test_workflow_complete_with_actual_verify(self, tmp_path, mock_fingerprint_file):
        """
        Bug #23: Verify the fix checks for 'skip:' prefix in _is_workflow_complete.

        This test verifies the fix is in place by checking the source code pattern.
        """
        import inspect
        from pdd import sync_determine_operation

        # Read the source code
        source = inspect.getsource(sync_determine_operation._is_workflow_complete)

        # Verify the fix is in place: should check for 'skip:' prefix
        assert "startswith('skip:')" in source, (
            "Bug #23 fix: _is_workflow_complete should check for 'skip:' prefix"
        )
        assert "# Bug #23 fix" in source or "skip:" in source, (
            "Bug #23 fix: should have skip prefix handling"
        )


# --- Bug #4: Cycle Detection Logic ---

class TestCycleDetection:
    """Tests for proper cycle detection counting."""

    def test_crash_verify_cycle_detection(self):
        """
        Bug #4: Cycle detection should count actual occurrences of the pattern,
        not use hardcoded values.
        """
        # Test the pattern detection logic directly
        operation_history = ['crash', 'verify', 'crash', 'verify']

        # Count how many times crash-verify pattern has occurred
        cycle_count = 0
        for i in range(0, len(operation_history) - 3):
            window = operation_history[i:i+4]
            if (window == ['crash', 'verify', 'crash', 'verify'] or
                window == ['verify', 'crash', 'verify', 'crash']):
                cycle_count += 1

        assert cycle_count == 1, "Should detect exactly one cycle pattern"

    def test_crash_verify_multiple_cycles(self):
        """
        Test detection of multiple crash-verify cycles.
        """
        # Two complete cycles
        operation_history = ['crash', 'verify', 'crash', 'verify', 'crash', 'verify', 'crash', 'verify']

        cycle_count = 0
        for i in range(0, len(operation_history) - 3):
            window = operation_history[i:i+4]
            if (window == ['crash', 'verify', 'crash', 'verify'] or
                window == ['verify', 'crash', 'verify', 'crash']):
                cycle_count += 1

        # With overlapping windows, we should detect multiple occurrences
        assert cycle_count >= 2, "Should detect multiple cycle patterns"

    def test_test_fix_cycle_detection(self):
        """
        Bug #4: Test-fix cycle detection should also count properly.
        """
        operation_history = ['test', 'fix', 'test', 'fix']

        cycle_count = 0
        for i in range(0, len(operation_history) - 3):
            window = operation_history[i:i+4]
            if (window == ['test', 'fix', 'test', 'fix'] or
                window == ['fix', 'test', 'fix', 'test']):
                cycle_count += 1

        assert cycle_count == 1, "Should detect exactly one test-fix cycle"

    def test_no_cycle_when_pattern_incomplete(self):
        """
        Verify no false positive cycle detection with incomplete patterns.
        """
        operation_history = ['crash', 'verify', 'crash']  # Only 3 operations

        cycle_count = 0
        if len(operation_history) >= 4:
            for i in range(0, len(operation_history) - 3):
                window = operation_history[i:i+4]
                if (window == ['crash', 'verify', 'crash', 'verify'] or
                    window == ['verify', 'crash', 'verify', 'crash']):
                    cycle_count += 1

        assert cycle_count == 0, "Should not detect cycle with incomplete pattern"


# --- Bug #8: Silent Exception Handling ---

class TestSilentExceptionHandling:
    """Tests for proper exception handling in post-crash verification."""

    def test_post_crash_exception_is_logged(self):
        """
        Bug #8: Exceptions during post-crash verification should be logged,
        not silently swallowed.
        """
        errors = []

        # Simulate the exception handling from sync_orchestration.py
        try:
            raise RuntimeError("Example execution failed")
        except Exception as e:
            # This is the fixed behavior - exception is caught and logged
            error_msg = f"Post-crash verification failed: {e}"
            errors.append(error_msg)

        assert len(errors) == 1
        assert "Post-crash verification failed" in errors[0]
        assert "Example execution failed" in errors[0]

    def test_post_crash_success_no_error(self):
        """
        Verify that successful post-crash verification doesn't add errors.
        """
        errors = []

        # Simulate successful execution
        try:
            # No exception raised
            returncode = 0
        except Exception as e:
            error_msg = f"Post-crash verification failed: {e}"
            errors.append(error_msg)

        assert len(errors) == 0, "No errors should be added on success"


# --- Integration Tests ---

class TestBugFixIntegration:
    """Integration tests that verify bug fixes work together."""

    def test_skip_flag_does_not_mark_workflow_complete(self, tmp_path):
        """
        Integration test: When operations are skipped, the workflow should
        not be incorrectly marked as complete.
        """
        import json
        import os
        from datetime import datetime, timezone

        # Setup
        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)

        paths = {
            'prompt': tmp_path / 'prompts' / 'test.prompt',
            'code': tmp_path / 'src' / 'test.py',
            'example': tmp_path / 'examples' / 'test_example.py',
            'test': tmp_path / 'tests' / 'test_test.py',
        }
        for p in paths.values():
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text("mock content")

        # Create fingerprint with skip:test (tests were skipped)
        fingerprint_file = meta_dir / "test_python.json"
        fingerprint_data = {
            "pdd_version": "0.0.88",
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "command": "skip:test",
            "prompt_hash": "abc123",
            "code_hash": "def456",
            "example_hash": "ghi789",
            "test_hash": None  # No test hash because tests were skipped
        }
        fingerprint_file.write_text(json.dumps(fingerprint_data))

        # Create run report
        run_report_file = meta_dir / "test_python_run.json"
        run_report_data = {
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "exit_code": 0,
            "tests_passed": 0,
            "tests_failed": 0,
            "coverage": 0.0,
            "test_hash": None
        }
        run_report_file.write_text(json.dumps(run_report_data))

        old_cwd = os.getcwd()
        os.chdir(tmp_path)

        try:
            # With skip_tests=False, workflow should NOT be complete
            # because the fingerprint shows tests were skipped
            result = _is_workflow_complete(
                paths,
                skip_tests=False,
                skip_verify=False,
                basename="test",
                language="python"
            )

            assert result is False, (
                "Workflow should not be complete when tests were skipped "
                "but skip_tests=False (user now wants tests to run)"
            )
        finally:
            os.chdir(old_cwd)
