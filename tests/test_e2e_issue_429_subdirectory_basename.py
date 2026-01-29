"""
E2E Test for Issue #429: Basename Sanitization in CLI Mode

This test verifies that subdirectory basenames (e.g., 'core/cloud') work correctly
in CLI mode by ensuring that operation_log.py creates files at sanitized paths
matching what sync_determine_operation.py expects to read.

Root cause: operation_log.py was missing basename sanitization, causing:
- CLI mode to crash with FileNotFoundError
- Reader/writer path mismatch between modules
- TUI mode to work while CLI mode fails

This E2E test exercises path generation functions directly without LLM calls.

Run with: pytest tests/test_e2e_issue_429_subdirectory_basename.py -v
"""

from __future__ import annotations

import json
import tempfile
from pathlib import Path
from typing import Dict, Any

import pytest

# Import the modules under test
from pdd.operation_log import (
    get_log_path,
    get_fingerprint_path,
    get_run_report_path,
    append_log_entry,
    save_fingerprint,
)
from pdd.sync_determine_operation import read_fingerprint


class TestIssue429SubdirectoryBasenameE2E:
    """E2E tests verifying subdirectory basenames create sanitized file paths."""

    # =========================================================================
    # Test 1: Path sanitization - basic subdirectory case
    # =========================================================================
    def test_subdirectory_basename_path_sanitization(self, tmp_path: Path, monkeypatch):
        """
        E2E: Verify that get_*_path functions sanitize subdirectory basenames.

        This is the core bug - operation_log.py must convert slashes to underscores
        in file paths, matching the behavior in sync_determine_operation.py and
        sync_orchestration.py.
        """
        # Set META_DIR to temp directory
        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)

        monkeypatch.setenv('HOME', str(tmp_path))
        from pdd import operation_log
        operation_log.META_DIR = str(meta_dir)

        basename = "core/cloud"
        language = "python"

        # Get paths from operation_log
        log_path = get_log_path(basename, language)
        fingerprint_path = get_fingerprint_path(basename, language)
        report_path = get_run_report_path(basename, language)

        # CRITICAL: All paths must be SANITIZED (underscores, not slashes)
        safe_basename = "core_cloud"  # NOT "core/cloud"

        # Expected sanitized paths
        expected_log = meta_dir / f"{safe_basename}_{language}_sync.log"
        expected_fingerprint = meta_dir / f"{safe_basename}_{language}.json"
        expected_report = meta_dir / f"{safe_basename}_{language}_run.json"

        # Assert paths are sanitized
        assert log_path == expected_log, (
            f"Log path not sanitized!\n"
            f"Expected: {expected_log}\n"
            f"Got: {log_path}\n"
            f"Bug: operation_log.py is not sanitizing basename '{basename}'"
        )

        assert fingerprint_path == expected_fingerprint, (
            f"Fingerprint path not sanitized!\n"
            f"Expected: {expected_fingerprint}\n"
            f"Got: {fingerprint_path}\n"
            f"Bug: operation_log.py is not sanitizing basename '{basename}'"
        )

        assert report_path == expected_report, (
            f"Run report path not sanitized!\n"
            f"Expected: {expected_report}\n"
            f"Got: {report_path}\n"
            f"Bug: operation_log.py is not sanitizing basename '{basename}'"
        )

        # Verify NO unsanitized subdirectories were created
        unsanitized_dir = meta_dir / "core"
        assert not unsanitized_dir.exists(), (
            f"Bug detected! Unsanitized subdirectory created: {unsanitized_dir}"
        )

    # =========================================================================
    # Test 2: File write operations with subdirectory basename
    # =========================================================================
    def test_write_operations_with_subdirectory_basename(self, tmp_path: Path, monkeypatch):
        """
        E2E: Verify that write operations (log, fingerprint) succeed with subdirectory basenames.

        Before the fix, these operations would fail with FileNotFoundError because
        operation_log.py tried to create files in non-existent subdirectories.
        """
        # Set META_DIR to temp directory
        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)

        monkeypatch.setenv('HOME', str(tmp_path))
        from pdd import operation_log
        operation_log.META_DIR = str(meta_dir)

        basename = "backend/utils/credit_helpers"
        language = "python"

        # Test 1: Append log entry - should NOT raise FileNotFoundError
        entry = {
            "operation": "test_operation",
            "invocation_mode": "test",
            "success": True,
            "metadata": {"test": "data"}
        }
        try:
            append_log_entry(
                basename=basename,
                language=language,
                entry=entry
            )
        except FileNotFoundError as e:
            pytest.fail(
                f"append_log_entry raised FileNotFoundError!\n"
                f"This indicates operation_log.py is trying to write to an unsanitized path.\n"
                f"Error: {e}"
            )

        # Verify log file was created at SANITIZED path
        safe_basename = "backend_utils_credit_helpers"
        log_path = meta_dir / f"{safe_basename}_{language}_sync.log"
        assert log_path.exists(), (
            f"Log file not created at sanitized path: {log_path}\n"
            f"Files in meta dir: {list(meta_dir.glob('*'))}"
        )

        # Test 2: Save fingerprint - should NOT raise FileNotFoundError
        fingerprint_data = {
            "files": {"test.py": {"hash": "abc123"}},
            "version": "1.0"
        }

        try:
            save_fingerprint(
                basename=basename,
                language=language,
                fingerprint=fingerprint_data
            )
        except FileNotFoundError as e:
            pytest.fail(
                f"save_fingerprint raised FileNotFoundError!\n"
                f"This indicates operation_log.py is trying to write to an unsanitized path.\n"
                f"Error: {e}"
            )

        # Verify fingerprint was created at SANITIZED path
        fingerprint_path = meta_dir / f"{safe_basename}_{language}.json"
        assert fingerprint_path.exists(), (
            f"Fingerprint not created at sanitized path: {fingerprint_path}\n"
            f"Files in meta dir: {list(meta_dir.glob('*'))}"
        )

        # Verify NO unsanitized subdirectories were created
        for subdir_name in ["backend", "utils", "credit_helpers"]:
            unsanitized_dir = meta_dir / subdir_name
            assert not unsanitized_dir.exists(), (
                f"Bug detected! Unsanitized subdirectory created: {unsanitized_dir}"
            )

    # =========================================================================
    # Test 3: Reader-writer consistency
    # =========================================================================
    def test_reader_writer_consistency(self, tmp_path: Path, monkeypatch):
        """
        E2E: Verify that fingerprints written by operation_log.py can be read by
        sync_determine_operation.py using the same path.

        This is the exact bug scenario - before the fix:
        - Writer (operation_log.py): .pdd/meta/core/cloud_python.json
        - Reader (sync_determine_operation.py): .pdd/meta/core_cloud_python.json
        - Result: Reader returns None, state desynchronization
        """
        # Set META_DIR to temp directory
        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)

        monkeypatch.setenv('HOME', str(tmp_path))
        from pdd import operation_log
        operation_log.META_DIR = str(meta_dir)

        basename = "core/cloud"
        language = "python"

        # Write fingerprint using operation_log (the writer)
        fingerprint_data = {
            "files": {
                "cloud.py": {"hash": "test123", "size": 100}
            },
            "prompt_hash": "prompt456",
            "version": "1.0"
        }

        save_fingerprint(basename, language, fingerprint_data)

        # Read fingerprint using sync_determine_operation (the reader)
        # Note: read_fingerprint uses get_meta_dir() internally, so we need to mock that
        from pdd.sync_determine_operation import get_meta_dir as sync_get_meta_dir
        monkeypatch.setattr('pdd.sync_determine_operation.get_meta_dir', lambda: meta_dir)
        read_result = read_fingerprint(basename, language)

        # CRITICAL: Reader must be able to find what writer created
        assert read_result is not None, (
            f"Reader/writer path mismatch!\n"
            f"Writer (operation_log.save_fingerprint) created fingerprint,\n"
            f"but Reader (sync_determine_operation.read_fingerprint) returned None.\n"
            f"This indicates the two modules are using different file paths.\n"
            f"Files in meta dir: {list(meta_dir.glob('*'))}"
        )

        # Verify content matches what was written
        assert read_result == fingerprint_data, (
            f"Fingerprint content mismatch!\n"
            f"Expected: {fingerprint_data}\n"
            f"Got: {read_result}"
        )

    # =========================================================================
    # Test 4: Edge case - deeply nested basename
    # =========================================================================
    def test_deeply_nested_basename(self, tmp_path: Path, monkeypatch):
        """
        E2E: Verify that deeply nested basenames (multiple slashes) are fully sanitized.

        Edge case from Step 8 verification where Path() interprets each slash
        as a directory separator.
        """
        # Set META_DIR to temp directory
        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True)

        monkeypatch.setenv('HOME', str(tmp_path))
        from pdd import operation_log
        operation_log.META_DIR = str(meta_dir)

        basename = "a/b/c/d"
        language = "python"

        # Get paths
        log_path = get_log_path(basename, language)
        fingerprint_path = get_fingerprint_path(basename, language)

        # ALL slashes must be converted to underscores
        safe_basename = "a_b_c_d"  # NOT "d" (partial) or "a/b/c/d" (unsanitized)

        expected_log = meta_dir / f"{safe_basename}_{language}_sync.log"
        expected_fingerprint = meta_dir / f"{safe_basename}_{language}.json"

        assert log_path == expected_log, (
            f"Deep nesting not fully sanitized in log path!\n"
            f"Expected: {expected_log}\n"
            f"Got: {log_path}"
        )

        assert fingerprint_path == expected_fingerprint, (
            f"Deep nesting not fully sanitized in fingerprint path!\n"
            f"Expected: {expected_fingerprint}\n"
            f"Got: {fingerprint_path}"
        )

        # Try writing to verify no subdirectories are created
        try:
            append_log_entry(basename, language, {"operation": "test", "success": True})
        except FileNotFoundError as e:
            pytest.fail(f"Write failed for deeply nested basename: {e}")

        # Verify NO subdirectories were created at any level
        for subdir_name in ["a", "b", "c", "d"]:
            unsanitized_dir = meta_dir / subdir_name
            assert not unsanitized_dir.exists(), (
                f"Subdirectory created at level '{subdir_name}': {unsanitized_dir}"
            )
