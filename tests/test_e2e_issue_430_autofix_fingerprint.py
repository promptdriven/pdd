"""
E2E Test for Issue #430: Auto-fix skips fingerprint save causing incomplete metadata.

This test verifies the bug where the auto-fix success path in sync_orchestration.py
skips fingerprint saves due to a continue statement at line 1412.
"""

import pytest
import json
from pathlib import Path
from unittest.mock import patch, MagicMock, call
import datetime


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory for all tests in this module."""
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


@pytest.mark.e2e
class TestAutoFixFingerprintSaveE2E:
    """E2E tests for Issue #430: Verify auto-fix success path saves complete metadata."""

    def test_auto_fix_success_saves_complete_metadata(
        self, tmp_path, monkeypatch
    ):
        """Verify that auto-fix success saves fingerprint and operations_completed."""
        from pdd.sync_orchestration import (
            _save_fingerprint_atomic,
            _save_run_report_atomic,
            log_event
        )
        from pdd.sync_determine_operation import RunReport
        from dataclasses import asdict

        monkeypatch.chdir(tmp_path)

        basename = "factorial_python"
        language = "python"

        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True, exist_ok=True)

        logs_dir = tmp_path / ".pdd" / "logs"
        logs_dir.mkdir(parents=True, exist_ok=True)

        prompt_file = tmp_path / f"{basename}.prompt"
        prompt_file.write_text("Write a factorial function")

        code_file = tmp_path / f"{basename}.py"
        code_file.write_text("def factorial(n): return 1 if n <= 1 else n * factorial(n-1)")

        example_file = tmp_path / f"{basename}_example.py"
        example_file.write_text("from factorial_python import factorial\nprint(factorial(5))")

        test_file = tmp_path / f"{basename}_test.py"
        test_file.write_text("import pytest")

        pdd_files = {
            'prompt': prompt_file,
            'code': code_file,
            'example': example_file,
            'test': test_file
        }

        initial_fingerprint = {
            "basename": basename,
            "language": language,
            "command": "example",
            "model": "gpt-4o-mini",
            "cost": 0.05,
            "operations_completed": ["generate", "example"]
        }

        fingerprint_file = meta_dir / f"{basename}_{language}.json"
        with open(fingerprint_file, 'w') as f:
            json.dump(initial_fingerprint, f, indent=2)

        auto_fix_msg = "Fixed import error"
        log_event(basename, language, "auto_fix_success",
                 {"message": auto_fix_msg}, invocation_mode="sync")

        test_hash = None
        report = RunReport(
            datetime.datetime.now(datetime.timezone.utc).isoformat(),
            exit_code=0,
            tests_passed=1,
            tests_failed=0,
            coverage=0.0,
            test_hash=test_hash
        )
        _save_run_report_atomic(asdict(report), basename, language)

        _save_fingerprint_atomic(
            basename,
            language,
            'crash',
            pdd_files,
            0.0,
            'auto-fix',
            atomic_state=None
        )

        log_event(basename, language, "operation_complete",
                 {"operation": "crash", "cost": 0.0, "model": "auto-fix"},
                 invocation_mode="sync")

        assert fingerprint_file.exists(), (
            f"Fingerprint file should exist at {fingerprint_file}"
        )

        with open(fingerprint_file, 'r') as f:
            saved_fingerprint = json.load(f)

        saved_command = saved_fingerprint.get('command')
        assert saved_command == 'crash', (
            f"Fingerprint command should be 'crash', got '{saved_command}'"
        )

        run_report_file = meta_dir / f"{basename}_{language}_run.json"
        assert run_report_file.exists(), "Run report should be saved"

        with open(run_report_file, 'r') as f:
            saved_report = json.load(f)

        assert saved_report['exit_code'] == 0, "Run report should show success"

        log_file = logs_dir / f"{basename}_{language}_sync.log"
        if log_file.exists():
            log_content = log_file.read_text()

            assert 'auto_fix_success' in log_content, (
                "Event log should contain 'auto_fix_success' event"
            )

            assert 'operation_complete' in log_content, (
                "Event log should contain 'operation_complete' event"
            )


    def test_auto_fix_follows_same_pattern_as_other_early_exits(
        self, tmp_path, monkeypatch
    ):
        """Verify auto-fix follows the same metadata save pattern as other early exits."""
        from pdd.sync_orchestration import _save_fingerprint_atomic

        monkeypatch.chdir(tmp_path)

        basename = "test_pattern"
        language = "python"

        meta_dir = tmp_path / ".pdd" / "meta"
        meta_dir.mkdir(parents=True, exist_ok=True)

        prompt_file = tmp_path / f"{basename}.prompt"
        prompt_file.write_text("Test")

        code_file = tmp_path / f"{basename}.py"
        code_file.write_text("def test(): pass")

        example_file = tmp_path / f"{basename}_example.py"
        example_file.write_text("print('test')")

        test_file = tmp_path / f"{basename}_test.py"
        test_file.write_text("# test")

        pdd_files = {
            'prompt': prompt_file,
            'code': code_file,
            'example': example_file,
            'test': test_file
        }

        _save_fingerprint_atomic(
            basename,
            language,
            'crash',
            pdd_files,
            0.0,
            'auto-fix',
            atomic_state=None
        )

        fingerprint_file = meta_dir / f"{basename}_{language}.json"
        assert fingerprint_file.exists()

        with open(fingerprint_file, 'r') as f:
            fingerprint = json.load(f)

        assert fingerprint['command'] == 'crash', (
            "Fingerprint command should be set to 'crash' after auto-fix success"
        )
