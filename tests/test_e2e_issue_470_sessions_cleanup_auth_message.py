"""
E2E test for Issue #470: pdd sessions cleanup error message references non-existent pdd login command.

This E2E test verifies that when `pdd sessions cleanup` is invoked without authentication,
the error message correctly references 'pdd auth login' (the actual command) instead of
'pdd login' (which doesn't exist).

Unlike the unit tests in test_sessions.py (which mock CloudConfig), this E2E test
exercises the full CLI path to verify the user-facing behavior.
"""
import pytest
from click.testing import CliRunner
from unittest import mock


@pytest.mark.e2e
class TestIssue470SessionsCleanupAuthMessageE2E:
    """
    E2E tests for Issue #470.
    Tests the actual CLI behavior when sessions cleanup is invoked without auth.
    """

    def test_sessions_cleanup_shows_correct_auth_command_e2e(self):
        """
        CRITICAL E2E TEST for issue #470:

        This test verifies that `pdd sessions cleanup` correctly references 'pdd auth login'
        in the error message when authentication is missing.

        Expected behavior: Error message should say "Please run 'pdd auth login'."
        Buggy behavior: Error message says "Please run 'pdd login'." (non-existent command)

        This test will FAIL on the buggy code and PASS after the fix.
        """
        from pdd.cli import cli

        runner = CliRunner()

        # Mock CloudConfig.get_jwt_token to return None (simulating no authentication)
        with mock.patch("pdd.commands.sessions.CloudConfig.get_jwt_token", return_value=None):
            # Act: Run sessions cleanup WITHOUT authentication
            result = runner.invoke(
                cli,
                ["sessions", "cleanup", "--all"],
                catch_exceptions=False
            )

            # Assert: The output should contain the error message
            assert "Error: Not authenticated" in result.output, (
                f"Expected error message about authentication, but got: {result.output}"
            )

            # Assert: The CRITICAL check - should reference the CORRECT command
            assert "pdd auth login" in result.output, (
                f"BUG DETECTED: Error message should reference 'pdd auth login', "
                f"but got: {result.output}\n\n"
                f"This is the exact bug reported in issue #470.\n"
                f"The error message incorrectly references 'pdd login' (which doesn't exist) "
                f"instead of 'pdd auth login' (the correct command)."
            )

            # Assert: Should NOT reference the non-existent command
            # We need to be careful here - "pdd auth login" contains "pdd login" as a substring
            # So we check that if "pdd login" appears, it's always part of "pdd auth login"
            import re
            # Find all instances of "pdd login" that are NOT part of "pdd auth login"
            wrong_command_pattern = r"(?<!auth )pdd login(?!')"
            wrong_command_matches = re.findall(wrong_command_pattern, result.output)

            assert len(wrong_command_matches) == 0, (
                f"BUG DETECTED: Error message contains 'pdd login' (non-existent command) "
                f"instead of 'pdd auth login'.\n"
                f"Found {len(wrong_command_matches)} instances of incorrect command reference.\n"
                f"Full output: {result.output}\n\n"
                f"Issue #470: https://github.com/promptdriven/pdd/issues/470"
            )

    def test_sessions_list_shows_correct_auth_command_e2e(self):
        """
        E2E test verifying that sessions list command shows correct auth message.

        This is a consistency check - the list command already has the correct message
        according to the issue report. This test ensures it stays correct.
        """
        from pdd.cli import cli

        runner = CliRunner()

        # Mock CloudConfig.get_jwt_token to return None
        with mock.patch("pdd.commands.sessions.CloudConfig.get_jwt_token", return_value=None):
            # Act: Run sessions list WITHOUT authentication
            result = runner.invoke(
                cli,
                ["sessions", "list"],
                catch_exceptions=False
            )

            # Assert: Should show correct auth command (this was already correct)
            assert "pdd auth login" in result.output, (
                f"Sessions list command should reference 'pdd auth login', "
                f"but got: {result.output}"
            )

    def test_sessions_info_shows_correct_auth_command_e2e(self):
        """
        E2E test verifying that sessions info command shows correct auth message.

        This is a consistency check - the info command already has the correct message
        according to the issue report. This test ensures it stays correct.
        """
        from pdd.cli import cli

        runner = CliRunner()

        # Mock CloudConfig.get_jwt_token to return None
        with mock.patch("pdd.commands.sessions.CloudConfig.get_jwt_token", return_value=None):
            # Act: Run sessions info WITHOUT authentication
            result = runner.invoke(
                cli,
                ["sessions", "info", "test-session-id"],
                catch_exceptions=False
            )

            # Assert: Should show correct auth command (this was already correct)
            assert "pdd auth login" in result.output, (
                f"Sessions info command should reference 'pdd auth login', "
                f"but got: {result.output}"
            )

    def test_all_sessions_subcommands_consistent_auth_message_e2e(self):
        """
        E2E test verifying ALL sessions subcommands have consistent auth error messages.

        This parametrized test ensures that list, info, and cleanup all reference
        'pdd auth login' consistently, and NONE reference the non-existent 'pdd login'.
        """
        from pdd.cli import cli

        runner = CliRunner()

        # Test cases: (subcommand_args, description)
        test_cases = [
            (["sessions", "list"], "sessions list"),
            (["sessions", "info", "dummy-id"], "sessions info"),
            (["sessions", "cleanup", "--all"], "sessions cleanup"),
        ]

        for subcommand_args, description in test_cases:
            # Mock CloudConfig.get_jwt_token to return None
            with mock.patch("pdd.commands.sessions.CloudConfig.get_jwt_token", return_value=None):
                # Act: Run the subcommand WITHOUT authentication
                result = runner.invoke(
                    cli,
                    subcommand_args,
                    catch_exceptions=False
                )

                # Assert: Should contain auth error
                assert "Error: Not authenticated" in result.output, (
                    f"{description}: Expected auth error, but got: {result.output}"
                )

                # Assert: Should reference correct command
                assert "pdd auth login" in result.output, (
                    f"{description}: Should reference 'pdd auth login', "
                    f"but got: {result.output}"
                )

                # Assert: Should NOT reference non-existent command
                import re
                wrong_command_pattern = r"(?<!auth )pdd login(?!')"
                wrong_command_matches = re.findall(wrong_command_pattern, result.output)

                assert len(wrong_command_matches) == 0, (
                    f"BUG in {description}: Contains 'pdd login' (non-existent command) "
                    f"instead of 'pdd auth login'.\n"
                    f"Full output: {result.output}"
                )

    def test_pdd_login_command_does_not_exist_e2e(self):
        """
        E2E test verifying that 'pdd login' is NOT a valid command.

        This confirms the core problem: users following the buggy error message
        will get a "No such command" error, causing confusion.
        """
        from pdd.cli import cli

        runner = CliRunner()

        # Act: Try to run 'pdd login' (the non-existent command)
        result = runner.invoke(
            cli,
            ["login"],
            catch_exceptions=False
        )

        # Assert: Should fail because 'login' is not a valid command
        assert result.exit_code != 0, (
            f"Expected 'pdd login' to fail (command doesn't exist), "
            f"but it succeeded with exit code {result.exit_code}"
        )

        # Assert: Error message should indicate unknown command
        output_lower = result.output.lower()
        assert "no such command" in output_lower or "error" in output_lower, (
            f"Expected error about unknown command, but got: {result.output}"
        )

    def test_pdd_auth_login_command_exists_e2e(self):
        """
        E2E test verifying that 'pdd auth login' IS a valid command.

        This confirms that the correct command (referenced in the fix) actually exists
        and is the right guidance to give users.
        """
        from pdd.cli import cli

        runner = CliRunner()

        # Mock webbrowser to prevent actual browser from opening during test
        with mock.patch("webbrowser.open"):
            # Act: Run 'pdd auth login' (the correct command)
            # We pass --help to avoid actually triggering auth flow
            result = runner.invoke(
                cli,
                ["auth", "login", "--help"],
                catch_exceptions=False
            )

            # Assert: Should not fail with "no such command" error
            # (It might fail for other reasons like missing config, but the command exists)
            output_lower = result.output.lower()
            assert "no such command" not in output_lower, (
                f"'pdd auth login' should be a valid command, "
                f"but got: {result.output}"
            )

            # Assert: Help text should show this is the login command
            assert "login" in output_lower and "auth" in output_lower, (
                f"Expected help text for 'auth login' command, but got: {result.output}"
            )
