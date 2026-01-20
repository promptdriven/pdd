"""
TRUE end-to-end test for issue #340: report-core should have no default repo.

This E2E test verifies that when `pdd report-core` is invoked without the --repo flag
and without the PDD_GITHUB_REPO environment variable, it should raise a clear error
instead of silently defaulting to 'promptdriven/pdd'.

Unlike the unit test in test_report.py (which mocks internal functions), this E2E test
exercises the full CLI path with minimal mocking to verify the user-facing behavior.
"""
import json
import pytest
from pathlib import Path
from click.testing import CliRunner
from unittest import mock


@pytest.mark.e2e
class TestReportCoreNoDefaultRepoE2E:
    """
    TRUE E2E test for issue #340.
    Tests the actual CLI behavior when repo parameter is missing.
    """

    def test_report_core_requires_repo_parameter_e2e(self, tmp_path, monkeypatch):
        """
        CRITICAL TRUE E2E TEST for issue #340:

        This test verifies that `pdd report-core` correctly errors when:
        1. No --repo flag is provided
        2. No PDD_GITHUB_REPO environment variable is set

        Expected behavior: Command should exit with code 2 (UsageError) with a clear message.
        Buggy behavior: Command exits with code 0 and silently uses 'promptdriven/pdd'.

        This test will FAIL on the buggy code and PASS after the fix.
        """
        # Setup: Create a real core dump file
        core_dump_dir = tmp_path / ".pdd" / "core_dumps"
        core_dump_dir.mkdir(parents=True, exist_ok=True)

        core_dump_content = {
            "metadata": {
                "version": "0.0.122",
                "timestamp": "2026-01-20T00:00:00Z",
                "command": "pdd test example.prompt example.py"
            },
            "files": [
                {
                    "path": "example.py",
                    "content": "def foo():\n    pass\n"
                }
            ],
            "error": {
                "type": "TestError",
                "message": "Example error for E2E test"
            }
        }

        core_dump_path = core_dump_dir / "pdd-core-12345.json"
        core_dump_path.write_text(json.dumps(core_dump_content))

        # Change to temp directory so CLI can find the core dump
        monkeypatch.chdir(tmp_path)

        # Import CLI after changing directory to ensure proper initialization
        from pdd.cli import cli

        runner = CliRunner()

        # Mock webbrowser.open to prevent browser from actually opening during test
        with mock.patch("webbrowser.open") as mock_webbrowser:
            # Act: Run report-core WITHOUT --repo flag and WITHOUT PDD_GITHUB_REPO env var
            # Explicitly set environment to exclude PDD_GITHUB_REPO
            result = runner.invoke(
                cli,
                ["report-core"],
                env={
                    "PDD_AUTO_UPDATE": "false",
                    "HOME": str(tmp_path),
                    # Explicitly do NOT set PDD_GITHUB_REPO
                },
                catch_exceptions=False  # Let errors propagate for better debugging
            )

            # Assert: Should fail with UsageError (exit code 2)
            assert result.exit_code == 2, (
                f"Expected exit code 2 (UsageError) when repo is not provided, "
                f"but got {result.exit_code}.\n"
                f"Output: {result.output}\n"
                f"This indicates the bug still exists - the command is not raising an error "
                f"when repo parameter is missing."
            )

            # Assert: Error message should mention repo or required parameter
            output_lower = result.output.lower()
            assert "error" in output_lower or "required" in output_lower, (
                f"Expected error message to mention missing repo parameter.\n"
                f"Got: {result.output}"
            )

            # Assert: Browser should NOT be opened (command should fail before that)
            mock_webbrowser.assert_not_called()

    def test_report_core_works_with_explicit_repo_flag_e2e(self, tmp_path, monkeypatch):
        """
        E2E test verifying that report-core works correctly when --repo flag IS provided.

        This is a positive test case to ensure the fix doesn't break normal functionality.
        """
        # Setup: Create a real core dump file
        core_dump_dir = tmp_path / ".pdd" / "core_dumps"
        core_dump_dir.mkdir(parents=True, exist_ok=True)

        core_dump_content = {
            "metadata": {
                "version": "0.0.122",
                "timestamp": "2026-01-20T00:00:00Z"
            },
            "files": []
        }

        core_dump_path = core_dump_dir / "pdd-core-67890.json"
        core_dump_path.write_text(json.dumps(core_dump_content))

        monkeypatch.chdir(tmp_path)

        from pdd.cli import cli

        runner = CliRunner()

        # Mock both webbrowser and GitHub config to prevent actual API calls
        with mock.patch("webbrowser.open") as mock_webbrowser, \
             mock.patch("pdd.commands.report._github_config") as mock_github_config:

            # Simulate no GitHub auth (will use browser mode)
            mock_github_config.return_value = None

            # Act: Run report-core WITH explicit --repo flag
            result = runner.invoke(
                cli,
                ["report-core", "--repo", "test-owner/test-repo"],
                env={
                    "PDD_AUTO_UPDATE": "false",
                    "HOME": str(tmp_path)
                },
                catch_exceptions=False
            )

            # Assert: Should succeed (exit code 0)
            assert result.exit_code == 0, (
                f"Expected success when --repo flag is provided, "
                f"but got exit code {result.exit_code}.\n"
                f"Output: {result.output}"
            )

            # Assert: Browser should be opened with the correct repo
            mock_webbrowser.assert_called_once()
            call_args = mock_webbrowser.call_args[0]
            assert "test-owner/test-repo" in call_args[0], (
                f"Expected URL to contain 'test-owner/test-repo', "
                f"but got: {call_args[0]}"
            )

    def test_report_core_works_with_env_var_repo_e2e(self, tmp_path, monkeypatch):
        """
        E2E test verifying that report-core works correctly when PDD_GITHUB_REPO env var is set.

        This ensures the environment variable fallback continues to work after the fix.
        """
        # Setup: Create a real core dump file
        core_dump_dir = tmp_path / ".pdd" / "core_dumps"
        core_dump_dir.mkdir(parents=True, exist_ok=True)

        core_dump_content = {
            "metadata": {
                "version": "0.0.122",
                "timestamp": "2026-01-20T00:00:00Z"
            },
            "files": []
        }

        core_dump_path = core_dump_dir / "pdd-core-11111.json"
        core_dump_path.write_text(json.dumps(core_dump_content))

        monkeypatch.chdir(tmp_path)

        from pdd.cli import cli

        runner = CliRunner()

        # Mock both webbrowser and GitHub config
        with mock.patch("webbrowser.open") as mock_webbrowser, \
             mock.patch("pdd.commands.report._github_config") as mock_github_config:

            mock_github_config.return_value = None

            # Act: Run report-core WITH PDD_GITHUB_REPO environment variable
            result = runner.invoke(
                cli,
                ["report-core"],
                env={
                    "PDD_AUTO_UPDATE": "false",
                    "HOME": str(tmp_path),
                    "PDD_GITHUB_REPO": "env-owner/env-repo"  # Set via env var
                },
                catch_exceptions=False
            )

            # Assert: Should succeed (exit code 0)
            assert result.exit_code == 0, (
                f"Expected success when PDD_GITHUB_REPO env var is set, "
                f"but got exit code {result.exit_code}.\n"
                f"Output: {result.output}"
            )

            # Assert: Browser should be opened with the env var repo
            mock_webbrowser.assert_called_once()
            call_args = mock_webbrowser.call_args[0]
            assert "env-owner/env-repo" in call_args[0], (
                f"Expected URL to contain 'env-owner/env-repo', "
                f"but got: {call_args[0]}"
            )

    def test_report_core_cli_flag_overrides_env_var_e2e(self, tmp_path, monkeypatch):
        """
        E2E test verifying that --repo flag takes precedence over PDD_GITHUB_REPO env var.

        This ensures proper precedence order: CLI flag > env var > (no default).
        """
        # Setup: Create a real core dump file
        core_dump_dir = tmp_path / ".pdd" / "core_dumps"
        core_dump_dir.mkdir(parents=True, exist_ok=True)

        core_dump_content = {
            "metadata": {
                "version": "0.0.122",
                "timestamp": "2026-01-20T00:00:00Z"
            },
            "files": []
        }

        core_dump_path = core_dump_dir / "pdd-core-22222.json"
        core_dump_path.write_text(json.dumps(core_dump_content))

        monkeypatch.chdir(tmp_path)

        from pdd.cli import cli

        runner = CliRunner()

        # Mock both webbrowser and GitHub config
        with mock.patch("webbrowser.open") as mock_webbrowser, \
             mock.patch("pdd.commands.report._github_config") as mock_github_config:

            mock_github_config.return_value = None

            # Act: Run report-core WITH BOTH --repo flag AND PDD_GITHUB_REPO env var
            result = runner.invoke(
                cli,
                ["report-core", "--repo", "cli-owner/cli-repo"],
                env={
                    "PDD_AUTO_UPDATE": "false",
                    "HOME": str(tmp_path),
                    "PDD_GITHUB_REPO": "env-owner/env-repo"  # This should be overridden
                },
                catch_exceptions=False
            )

            # Assert: Should succeed (exit code 0)
            assert result.exit_code == 0, (
                f"Expected success, but got exit code {result.exit_code}.\n"
                f"Output: {result.output}"
            )

            # Assert: Browser should be opened with the CLI flag repo (not env var)
            mock_webbrowser.assert_called_once()
            call_args = mock_webbrowser.call_args[0]
            assert "cli-owner/cli-repo" in call_args[0], (
                f"Expected URL to contain 'cli-owner/cli-repo' (from CLI flag), "
                f"but got: {call_args[0]}"
            )
            assert "env-owner/env-repo" not in call_args[0], (
                f"URL should NOT contain env var repo when CLI flag is provided"
            )
