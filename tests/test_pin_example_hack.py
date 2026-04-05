"""Tests for pin_example_hack.py — Issue #1080 caller-side cwd fix."""
import datetime
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

from pdd.pin_example_hack import _execute_tests_and_create_run_report


class TestIssue1080MonorepoCwd:
    """Tests for issue #1080: pin_example_hack must use config dir as cwd for non-Python tests.

    Bug: _execute_tests_and_create_run_report() calls get_test_command_for_file() which now
    returns a TestCommand object, but the caller still passes it directly to subprocess.run()
    and uses cwd=str(test_file.parent) instead of TestCommand.cwd.
    """

    def test_execute_tests_uses_config_dir_not_test_file_parent(self, tmp_path, monkeypatch):
        """_execute_tests_and_create_run_report must use TestCommand.cwd, not test_file.parent.

        Before fix: subprocess.run(test_cmd, cwd=str(test_file.parent)) where test_cmd is a
            TestCommand object (not a string) and cwd is __test__/ instead of frontend/
        After fix: subprocess.run(test_cmd.command, cwd=str(test_cmd.cwd)) — extracts command
            string and uses the config directory from TestCommand
        """
        monkeypatch.chdir(tmp_path)

        # Set up monorepo: frontend/jest.config.js + frontend/src/__test__/api.test.ts
        config_dir = tmp_path / "frontend"
        config_dir.mkdir()
        (config_dir / "jest.config.js").write_text("module.exports = {};")

        test_dir = config_dir / "src" / "__test__"
        test_dir.mkdir(parents=True)
        test_file = test_dir / "api.test.ts"
        test_file.write_text("test('api', () => {});")

        subprocess_calls = []

        def capture_run(cmd, **kwargs):
            subprocess_calls.append({'cmd': cmd, 'kwargs': kwargs})
            result = MagicMock()
            result.returncode = 0
            result.stdout = "Tests: 5 passed"
            result.stderr = ""
            return result

        with patch('pdd.pin_example_hack.subprocess.run', side_effect=capture_run), \
             patch('pdd.pin_example_hack.calculate_sha256', return_value="abc123"), \
             patch('pdd.pin_example_hack.save_run_report'):
            try:
                _execute_tests_and_create_run_report(
                    test_file=test_file,
                    basename="api",
                    language="typescript",
                    target_coverage=0.0
                )
            except Exception:
                pass

        # Find the non-Python shell command (should be a string, not a TestCommand object)
        non_python_calls = [c for c in subprocess_calls if isinstance(c['cmd'], str)]
        assert len(non_python_calls) > 0, (
            "Expected at least one shell command (string) for non-Python test. "
            "If cmd is a TestCommand object, the caller isn't extracting .command. "
            f"All calls: {subprocess_calls}"
        )
        actual_cwd = non_python_calls[0]['kwargs'].get('cwd')
        assert actual_cwd == str(config_dir), (
            f"Bug #1080: Expected cwd={config_dir} (where jest.config.js lives), "
            f"got cwd={actual_cwd}. pin_example_hack uses test_file.parent "
            f"instead of TestCommand.cwd from get_test_command_for_file()."
        )

    def test_execute_tests_extracts_command_string_from_testcommand(self, tmp_path, monkeypatch):
        """Verify subprocess.run receives a command string, not a TestCommand object.

        Before fix: subprocess.run(TestCommand(...), shell=True) — passes object as cmd
        After fix: subprocess.run(test_cmd.command, shell=True) — extracts .command first
        """
        monkeypatch.chdir(tmp_path)

        config_dir = tmp_path / "frontend"
        config_dir.mkdir()
        (config_dir / "jest.config.js").write_text("module.exports = {};")

        test_dir = config_dir / "src" / "__test__"
        test_dir.mkdir(parents=True)
        test_file = test_dir / "api.test.ts"
        test_file.write_text("test('api', () => {});")

        subprocess_calls = []

        def capture_run(cmd, **kwargs):
            subprocess_calls.append({'cmd': cmd, 'kwargs': kwargs})
            result = MagicMock()
            result.returncode = 0
            result.stdout = "Tests: 1 passed"
            result.stderr = ""
            return result

        with patch('pdd.pin_example_hack.subprocess.run', side_effect=capture_run), \
             patch('pdd.pin_example_hack.calculate_sha256', return_value="abc123"), \
             patch('pdd.pin_example_hack.save_run_report'):
            try:
                _execute_tests_and_create_run_report(
                    test_file=test_file,
                    basename="api",
                    language="typescript",
                    target_coverage=0.0
                )
            except Exception:
                pass

        # At least one subprocess call should have been made
        assert len(subprocess_calls) > 0, "No subprocess calls captured"

        # The command passed to subprocess.run must be a string, not a TestCommand
        for call in subprocess_calls:
            cmd = call['cmd']
            assert isinstance(cmd, str), (
                f"Bug #1080: subprocess.run received {type(cmd).__name__} instead of str. "
                f"The caller must extract .command from the TestCommand before passing to "
                f"subprocess.run(). Got: {cmd}"
            )
