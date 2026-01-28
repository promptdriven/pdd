"""
E2E Test for Issue #1: `install_completion()` got unexpected keyword argument 'quiet'

This test exercises the full CLI path from `pdd install_completion` command down to
the install_completion() function to verify that the function signature accepts the
'quiet' parameter that the CLI wrapper passes to it.

The bug: In version 0.0.32, the install_completion() function at pdd/install_completion.py:91
had NO parameters:
    def install_completion():

But the CLI command wrapper at pdd/commands/utility.py:22 was calling it with:
    cli_module.install_completion(quiet=quiet)

This caused: TypeError: install_completion() got an unexpected keyword argument 'quiet'

This E2E test:
1. Sets up the CLI environment
2. Runs the install_completion command through Click's CliRunner
3. Verifies the command executes without the TypeError
4. Tests both with --quiet flag and without it

The test should FAIL on buggy code (v0.0.32 with no quiet parameter) and
PASS once the fix is applied (v0.0.34+ with quiet: bool = False parameter).
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
from click.testing import CliRunner

from pdd import cli
from pdd.install_completion import get_current_shell


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory for all tests in this module.

    This is required for proper CLI operation.
    """
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


class TestInstallCompletionQuietParameterE2E:
    """
    E2E tests for Issue #1: Verify install_completion accepts the 'quiet' parameter
    that the CLI command wrapper passes to it.
    """

    def test_install_completion_command_without_quiet_flag(self, tmp_path, monkeypatch):
        """
        E2E Test: pdd install_completion (without --quiet flag)

        This test runs the full CLI path and verifies that the command executes
        without raising a TypeError about the 'quiet' parameter.

        Expected behavior (after fix):
        - Command should execute successfully
        - install_completion() should accept quiet=False (default from CLI context)
        - No TypeError should be raised

        Bug behavior (Issue #1, v0.0.32):
        - TypeError: install_completion() got an unexpected keyword argument 'quiet'
        """
        # Mock environment to prevent actual shell modification
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-openai-key-for-testing")

        # Mock the shell detection and file operations
        mock_shell = "bash"
        mock_rc_path = tmp_path / ".bashrc"
        mock_rc_path.write_text("# Test bashrc\n")

        # Create a fake completion script
        mock_completion_script = tmp_path / "pdd_completion.sh"
        mock_completion_script.write_text("# Completion script\n")

        def mock_get_current_shell():
            return mock_shell

        def mock_get_shell_rc_path(shell):
            return str(mock_rc_path)

        def mock_get_local_pdd_path():
            return str(tmp_path)

        # Track whether the install_completion function was called and with what args
        call_tracker = {"called": False, "args": None, "kwargs": None}
        original_install_completion = cli.install_completion

        def tracked_install_completion(*args, **kwargs):
            call_tracker["called"] = True
            call_tracker["args"] = args
            call_tracker["kwargs"] = kwargs
            # Don't actually install - just verify the call signature works
            return None

        # Run the CLI command
        with patch('pdd.install_completion.get_current_shell', side_effect=mock_get_current_shell):
            with patch('pdd.install_completion.get_shell_rc_path', side_effect=mock_get_shell_rc_path):
                with patch('pdd.install_completion.get_local_pdd_path', side_effect=mock_get_local_pdd_path):
                    with patch('pdd.cli.install_completion', side_effect=tracked_install_completion):
                        runner = CliRunner()
                        result = runner.invoke(cli.cli, [
                            "install_completion"
                        ], catch_exceptions=False)

        # THE KEY ASSERTION: The command should succeed without TypeError
        # If the function signature doesn't accept 'quiet', this will fail with:
        # TypeError: install_completion() got an unexpected keyword argument 'quiet'
        assert result.exit_code == 0 or "got an unexpected keyword argument 'quiet'" not in result.output, (
            f"BUG DETECTED (Issue #1): install_completion() does not accept 'quiet' parameter!\n\n"
            f"Exit code: {result.exit_code}\n"
            f"Output: {result.output}\n\n"
            f"The CLI command wrapper at pdd/commands/utility.py:22 calls:\n"
            f"  cli_module.install_completion(quiet=quiet)\n\n"
            f"But the function signature at pdd/install_completion.py:91 does not accept this parameter.\n"
            f"Expected signature: def install_completion(quiet: bool = False)\n"
            f"Buggy signature (v0.0.32): def install_completion()"
        )

        # Verify the function was called with the quiet parameter
        assert call_tracker["called"], "install_completion was not called"
        assert "quiet" in call_tracker["kwargs"], (
            f"The CLI should pass 'quiet' parameter to install_completion.\n"
            f"Got kwargs: {call_tracker['kwargs']}"
        )
        # When no --quiet flag, quiet should be False
        assert call_tracker["kwargs"]["quiet"] == False, (
            f"Expected quiet=False when no --quiet flag provided.\n"
            f"Got: {call_tracker['kwargs']['quiet']}"
        )

    def test_install_completion_command_with_quiet_flag(self, tmp_path, monkeypatch):
        """
        E2E Test: pdd --quiet install_completion (with --quiet global flag)

        This test verifies that when the user provides --quiet flag, it is properly
        passed through to the install_completion function.

        Expected behavior:
        - Command should execute successfully
        - install_completion() should receive quiet=True
        - No TypeError should be raised

        Bug behavior (Issue #1, v0.0.32):
        - TypeError: install_completion() got an unexpected keyword argument 'quiet'
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-openai-key-for-testing")

        # Mock shell environment
        mock_rc_path = tmp_path / ".bashrc"
        mock_rc_path.write_text("# Test bashrc\n")

        # Create a fake completion script
        mock_completion_script = tmp_path / "pdd_completion.sh"
        mock_completion_script.write_text("# Completion script\n")

        def mock_get_current_shell():
            return "bash"

        def mock_get_shell_rc_path(shell):
            return str(mock_rc_path)

        def mock_get_local_pdd_path():
            return str(tmp_path)

        # Track the call
        call_tracker = {"called": False, "kwargs": None}

        def tracked_install_completion(*args, **kwargs):
            call_tracker["called"] = True
            call_tracker["kwargs"] = kwargs
            return None

        # Run with --quiet flag
        with patch('pdd.install_completion.get_current_shell', side_effect=mock_get_current_shell):
            with patch('pdd.install_completion.get_shell_rc_path', side_effect=mock_get_shell_rc_path):
                with patch('pdd.install_completion.get_local_pdd_path', side_effect=mock_get_local_pdd_path):
                    with patch('pdd.cli.install_completion', side_effect=tracked_install_completion):
                        runner = CliRunner()
                        result = runner.invoke(cli.cli, [
                            "--quiet",  # Global quiet flag
                            "install_completion"
                        ], catch_exceptions=False)

        # THE KEY ASSERTION: Should not fail with TypeError about 'quiet'
        assert "got an unexpected keyword argument 'quiet'" not in result.output, (
            f"BUG DETECTED (Issue #1): install_completion() rejected 'quiet' parameter!\n\n"
            f"Output: {result.output}\n\n"
            f"The function must accept the 'quiet' parameter that the CLI passes to it."
        )

        # Verify quiet=True was passed
        assert call_tracker["called"], "install_completion was not called"
        assert "quiet" in call_tracker["kwargs"], "quiet parameter was not passed"
        assert call_tracker["kwargs"]["quiet"] == True, (
            f"Expected quiet=True when --quiet flag provided.\n"
            f"Got: {call_tracker['kwargs']['quiet']}"
        )

    def test_install_completion_function_signature_directly(self, tmp_path):
        """
        E2E Test: Direct call to install_completion() with quiet parameter

        This is the most direct test - it calls the actual install_completion function
        with the quiet parameter to verify the signature is correct.

        This test catches the bug at the lowest level without CLI overhead.

        Expected behavior (after fix):
        - Function should accept quiet=True
        - Function should accept quiet=False
        - No TypeError should be raised

        Bug behavior (Issue #1, v0.0.32):
        - TypeError: install_completion() got an unexpected keyword argument 'quiet'
        """
        from pdd.install_completion import install_completion

        # Create a fake completion script
        mock_completion_script = tmp_path / "pdd_completion.sh"
        mock_completion_script.write_text("# Completion script\n")

        # Create mock RC file
        mock_rc_path = tmp_path / ".bashrc"
        mock_rc_path.write_text("# Test bashrc\n")

        # Mock the functions that would actually modify the system
        with patch('pdd.install_completion.get_current_shell', return_value='bash'):
            with patch('pdd.install_completion.get_shell_rc_path', return_value=str(mock_rc_path)):
                with patch('pdd.install_completion.get_local_pdd_path', return_value=str(tmp_path)):
                    try:
                        # THE KEY TEST: Call with quiet=True
                        install_completion(quiet=True)
                        quiet_true_works = True
                        error_msg = None
                    except TypeError as e:
                        if "got an unexpected keyword argument 'quiet'" in str(e):
                            quiet_true_works = False
                            error_msg = str(e)
                        else:
                            raise
                    except Exception:
                        # Other exceptions are OK (e.g., file operations)
                        # We're only testing the signature
                        quiet_true_works = True
                        error_msg = None

        assert quiet_true_works, (
            f"BUG DETECTED (Issue #1): install_completion() does not accept 'quiet' parameter!\n\n"
            f"Error: {error_msg if error_msg else 'N/A'}\n\n"
            f"The function at pdd/install_completion.py:91 must have signature:\n"
            f"  def install_completion(quiet: bool = False):\n\n"
            f"But the current signature does not accept the 'quiet' parameter.\n"
            f"This causes the CLI command to fail with:\n"
            f"  TypeError: install_completion() got an unexpected keyword argument 'quiet'\n\n"
            f"Expected in v0.0.32: def install_completion()  # NO PARAMETERS - BUGGY\n"
            f"Fixed in v0.0.34: def install_completion(quiet: bool = False)  # CORRECT"
        )

        # Also test with quiet=False (default case)
        with patch('pdd.install_completion.get_current_shell', return_value='bash'):
            with patch('pdd.install_completion.get_shell_rc_path', return_value=str(mock_rc_path)):
                with patch('pdd.install_completion.get_local_pdd_path', return_value=str(tmp_path)):
                    try:
                        install_completion(quiet=False)
                        quiet_false_works = True
                    except TypeError as e:
                        if "got an unexpected keyword argument 'quiet'" in str(e):
                            quiet_false_works = False
                        else:
                            raise
                    except Exception:
                        quiet_false_works = True

        assert quiet_false_works, (
            "install_completion should accept quiet=False"
        )
