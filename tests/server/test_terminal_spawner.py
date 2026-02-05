"""
Tests for pdd.server.terminal_spawner module.

These tests verify the cross-platform terminal spawning functionality.
Most tests use mocking to avoid actually spawning terminal windows.
"""

import os
import sys
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock

from pdd.server.terminal_spawner import TerminalSpawner


# ============================================================================
# Tests for TerminalSpawner.spawn
# ============================================================================

class TestTerminalSpawner:
    """Test suite for TerminalSpawner class."""

    def test_spawn_prepends_cd_when_working_dir_provided(self):
        """Test that spawn prepends cd command when working_dir is given."""
        with patch.object(TerminalSpawner, '_darwin', return_value=True) as mock_darwin:
            with patch('sys.platform', 'darwin'):
                TerminalSpawner.spawn("pdd sync foo", working_dir="/home/user/project")

                # Verify the command includes cd (may be quoted)
                call_args = mock_darwin.call_args[0][0]
                assert "/home/user/project" in call_args
                assert "cd" in call_args
                assert "pdd sync foo" in call_args

    def test_spawn_dispatches_to_darwin_on_macos(self):
        """Test that spawn calls _darwin on macOS."""
        with patch.object(TerminalSpawner, '_darwin', return_value=True) as mock_darwin:
            with patch('sys.platform', 'darwin'):
                result = TerminalSpawner.spawn("pdd sync foo")

                mock_darwin.assert_called_once()
                assert result is True

    def test_spawn_dispatches_to_linux_on_linux(self):
        """Test that spawn calls _linux on Linux."""
        with patch.object(TerminalSpawner, '_linux', return_value=True) as mock_linux:
            with patch('sys.platform', 'linux'):
                result = TerminalSpawner.spawn("pdd sync foo")

                mock_linux.assert_called_once()
                assert result is True

    def test_spawn_dispatches_to_windows_on_win32(self):
        """Test that spawn calls _windows on Windows."""
        with patch.object(TerminalSpawner, '_windows', return_value=True) as mock_windows:
            with patch('sys.platform', 'win32'):
                result = TerminalSpawner.spawn("pdd sync foo")

                mock_windows.assert_called_once()
                assert result is True

    def test_spawn_returns_false_on_unknown_platform(self):
        """Test that spawn returns False on unsupported platforms."""
        with patch('sys.platform', 'unknown_os'):
            result = TerminalSpawner.spawn("pdd sync foo")
            assert result is False


# ============================================================================
# Tests for macOS (_darwin)
# ============================================================================

class TestDarwinSpawner:
    """Test suite for macOS terminal spawning."""

    def test_darwin_creates_script_and_opens_terminal(self):
        """Test that _darwin creates a script and opens Terminal.app."""
        mock_popen = MagicMock()

        with patch('subprocess.Popen', mock_popen):
            with patch.object(Path, 'write_text') as mock_write:
                with patch.object(Path, 'chmod') as mock_chmod:
                    result = TerminalSpawner._darwin("pdd sync foo")

                    # Verify script was created
                    mock_write.assert_called_once()
                    script_content = mock_write.call_args[0][0]
                    assert "pdd sync foo" in script_content
                    assert "exec bash" in script_content

                    # Verify chmod was called with executable permission
                    mock_chmod.assert_called_once_with(0o755)

                    # Verify open was called with Terminal.app
                    mock_popen.assert_called_once()
                    call_args = mock_popen.call_args[0][0]
                    assert "open" in call_args
                    assert "-a" in call_args
                    assert "Terminal" in call_args

                    assert result is True

    def test_darwin_returns_false_on_exception(self):
        """Test that _darwin returns False when an error occurs."""
        with patch('subprocess.Popen', side_effect=Exception("Test error")):
            result = TerminalSpawner._darwin("pdd sync foo")
            assert result is False


# ============================================================================
# Tests for Linux (_linux)
# ============================================================================

class TestLinuxSpawner:
    """Test suite for Linux terminal spawning."""

    def test_linux_tries_terminals_in_order(self):
        """Test that _linux tries terminals in order."""
        mock_popen = MagicMock()

        # Simulate gnome-terminal not found, xfce4-terminal found
        def mock_which(name):
            return "/usr/bin/xfce4-terminal" if name == "xfce4-terminal" else None

        with patch('shutil.which', side_effect=mock_which):
            with patch('subprocess.Popen', mock_popen):
                result = TerminalSpawner._linux("pdd sync foo")

                mock_popen.assert_called_once()
                call_args = mock_popen.call_args[0][0]
                assert "xfce4-terminal" in call_args
                assert result is True

    def test_linux_uses_gnome_terminal_when_available(self):
        """Test that _linux prefers gnome-terminal when available."""
        mock_popen = MagicMock()

        with patch('shutil.which', return_value="/usr/bin/gnome-terminal"):
            with patch('subprocess.Popen', mock_popen):
                result = TerminalSpawner._linux("pdd sync foo")

                call_args = mock_popen.call_args[0][0]
                assert "gnome-terminal" in call_args
                assert result is True

    def test_linux_returns_false_when_no_terminal_found(self):
        """Test that _linux returns False when no terminal emulator is found."""
        with patch('shutil.which', return_value=None):
            result = TerminalSpawner._linux("pdd sync foo")
            assert result is False

    def test_linux_returns_false_on_exception(self):
        """Test that _linux returns False when an error occurs."""
        with patch('shutil.which', return_value="/usr/bin/gnome-terminal"):
            with patch('subprocess.Popen', side_effect=Exception("Test error")):
                result = TerminalSpawner._linux("pdd sync foo")
                assert result is False


# ============================================================================
# Tests for Windows (_windows)
# ============================================================================

class TestWindowsSpawner:
    """Test suite for Windows terminal spawning."""

    def test_windows_tries_wt_first(self):
        """Test that _windows tries Windows Terminal first."""
        mock_popen = MagicMock()

        with patch('subprocess.Popen', mock_popen):
            result = TerminalSpawner._windows("pdd sync foo")

            # First call should be to wt.exe
            first_call = mock_popen.call_args_list[0][0][0]
            assert "wt.exe" in first_call
            assert result is True

    def test_windows_falls_back_to_powershell(self):
        """Test that _windows falls back to PowerShell when wt.exe not found."""
        call_count = [0]

        def mock_popen(args):
            call_count[0] += 1
            if call_count[0] == 1 and "wt.exe" in args:
                raise FileNotFoundError("wt.exe not found")
            return MagicMock()

        with patch('subprocess.Popen', side_effect=mock_popen):
            result = TerminalSpawner._windows("pdd sync foo")

            assert call_count[0] == 2  # wt.exe failed, powershell succeeded
            assert result is True

    def test_windows_returns_false_on_complete_failure(self):
        """Test that _windows returns False when both methods fail."""
        with patch('subprocess.Popen', side_effect=Exception("All failed")):
            result = TerminalSpawner._windows("pdd sync foo")
            assert result is False


# ============================================================================
# Tests for Callback URL Port Handling
# ============================================================================


class TestTerminalSpawnerCallbackPort:
    """Tests for callback URL port handling in terminal spawner."""

    def test_darwin_callback_uses_provided_port(self):
        """Test macOS callback URL uses the server_port parameter."""
        mock_popen = MagicMock()

        with patch('subprocess.Popen', mock_popen):
            with patch.object(Path, 'write_text') as mock_write:
                with patch.object(Path, 'chmod'):
                    TerminalSpawner._darwin(
                        "pdd generate test.prompt",
                        job_id="test-job-123",
                        server_port=8000  # Non-default port
                    )

                    script_content = mock_write.call_args[0][0]
                    # Verify the callback URL uses port 8000
                    assert "localhost:8000" in script_content
                    # Verify default port is NOT used
                    assert "localhost:9876" not in script_content

    def test_darwin_callback_uses_default_port_when_not_specified(self):
        """Test default port 9876 is used when server_port not specified."""
        mock_popen = MagicMock()

        with patch('subprocess.Popen', mock_popen):
            with patch.object(Path, 'write_text') as mock_write:
                with patch.object(Path, 'chmod'):
                    TerminalSpawner._darwin(
                        "pdd generate test.prompt",
                        job_id="test-job-123"
                        # server_port not specified - should use default 9876
                    )

                    script_content = mock_write.call_args[0][0]
                    assert "localhost:9876" in script_content

    def test_linux_callback_uses_provided_port(self):
        """Test Linux callback URL uses the server_port parameter."""
        with patch('shutil.which', return_value="/usr/bin/gnome-terminal"):
            with patch('subprocess.Popen') as mock_popen:
                TerminalSpawner._linux(
                    "pdd generate test.prompt",
                    job_id="test-job-123",
                    server_port=8000
                )

                call_args = mock_popen.call_args[0][0]
                full_command = " ".join(str(arg) for arg in call_args)
                assert "localhost:8000" in full_command
                assert "localhost:9876" not in full_command

    def test_windows_callback_uses_provided_port(self):
        """Test Windows callback URL uses the server_port parameter."""
        with patch('subprocess.Popen') as mock_popen:
            TerminalSpawner._windows(
                "pdd generate test.prompt",
                job_id="test-job-123",
                server_port=8000
            )

            call_args = mock_popen.call_args[0][0]
            full_command = " ".join(str(arg) for arg in call_args)
            assert "localhost:8000" in full_command
            assert "localhost:9876" not in full_command

    def test_spawn_passes_server_port_to_darwin(self):
        """Test that spawn method passes server_port to _darwin."""
        with patch.object(TerminalSpawner, '_darwin', return_value=True) as mock_darwin:
            with patch('sys.platform', 'darwin'):
                TerminalSpawner.spawn(
                    "pdd generate test.prompt",
                    job_id="test-job-123",
                    server_port=8000
                )

                mock_darwin.assert_called_once()
                call_args = mock_darwin.call_args
                assert call_args[0][1] == "test-job-123"  # job_id
                assert call_args[0][2] == 8000  # server_port

    def test_spawn_passes_server_port_to_linux(self):
        """Test that spawn method passes server_port to _linux."""
        with patch.object(TerminalSpawner, '_linux', return_value=True) as mock_linux:
            with patch('sys.platform', 'linux'):
                TerminalSpawner.spawn(
                    "pdd generate test.prompt",
                    job_id="test-job-123",
                    server_port=8000
                )

                mock_linux.assert_called_once()
                call_args = mock_linux.call_args
                assert call_args[0][1] == "test-job-123"  # job_id
                assert call_args[0][2] == 8000  # server_port


# ============================================================================
# Tests for Callback Execution Order (Race Condition Bug)
# ============================================================================


class TestCallbackExecutionOrder:
    """
    Tests to verify that callback curl completes BEFORE exec bash runs.

    BUG: The curl callback was running in background (&) and then exec bash
    immediately replaces the shell process, potentially killing curl before
    it can send the HTTP request.

    FIX: Curl must run synchronously (without &) before exec bash.
    """

    def test_darwin_callback_not_backgrounded(self):
        """
        FAILING TEST: macOS callback should NOT be backgrounded.

        The curl command must complete before exec bash runs, otherwise
        the HTTP request may never be sent.
        """
        mock_popen = MagicMock()

        with patch('subprocess.Popen', mock_popen):
            with patch.object(Path, 'write_text') as mock_write:
                with patch.object(Path, 'chmod'):
                    TerminalSpawner._darwin(
                        "pdd generate test.prompt",
                        job_id="test-job-123",
                        server_port=9876
                    )

                    script_content = mock_write.call_args[0][0]

                    # Find the curl command line
                    lines = script_content.split('\n')
                    curl_lines = [l for l in lines if 'curl' in l and 'POST' in l]

                    assert len(curl_lines) >= 1, "Should have a curl command"

                    # The curl line should NOT end with '&' (background)
                    # This is the bug - curl runs in background and exec bash kills it
                    for curl_line in curl_lines:
                        # Check if line ends with & (backgrounded)
                        # Note: &>/dev/null is ok, but &>/dev/null & is not
                        assert not curl_line.rstrip().endswith('&'), \
                            f"Curl should NOT be backgrounded! Found: {curl_line}"

    def test_darwin_callback_completes_before_exec(self):
        """
        Test that the callback script ensures curl completes before exec bash.

        Either:
        1. curl runs synchronously (no &), OR
        2. There's a 'wait' command before exec bash
        """
        mock_popen = MagicMock()

        with patch('subprocess.Popen', mock_popen):
            with patch.object(Path, 'write_text') as mock_write:
                with patch.object(Path, 'chmod'):
                    TerminalSpawner._darwin(
                        "pdd generate test.prompt",
                        job_id="test-job-123",
                        server_port=9876
                    )

                    script_content = mock_write.call_args[0][0]

                    # Check that curl is NOT backgrounded OR there's a wait
                    has_backgrounded_curl = '&>/dev/null &' in script_content or \
                                           "& #" in script_content or \
                                           script_content.count('curl') > 0 and \
                                           any(l.rstrip().endswith('&') for l in script_content.split('\n') if 'curl' in l)

                    has_wait_before_exec = 'wait' in script_content and \
                                          script_content.index('wait') < script_content.index('exec bash')

                    # Either curl is synchronous OR there's a wait
                    assert not has_backgrounded_curl or has_wait_before_exec, \
                        "Curl must complete before exec bash - either run synchronously or add 'wait'"

    def test_linux_callback_not_backgrounded(self):
        """
        FAILING TEST: Linux callback should NOT be backgrounded.
        """
        with patch('shutil.which', return_value="/usr/bin/gnome-terminal"):
            with patch('subprocess.Popen') as mock_popen:
                TerminalSpawner._linux(
                    "pdd generate test.prompt",
                    job_id="test-job-123",
                    server_port=9876
                )

                call_args = mock_popen.call_args[0][0]
                full_command = " ".join(str(arg) for arg in call_args)

                # Find if curl is backgrounded (ends with &)
                # The pattern is: curl ... &>/dev/null &
                # This is wrong - should be: curl ... &>/dev/null (no trailing &)

                # Check for the problematic pattern
                assert "&>/dev/null &" not in full_command and \
                       ">/dev/null &" not in full_command, \
                    f"Curl should NOT be backgrounded! Found backgrounded curl in: {full_command}"

    def test_linux_callback_completes_before_exec(self):
        """
        Test that Linux callback ensures curl completes before exec bash.
        """
        with patch('shutil.which', return_value="/usr/bin/gnome-terminal"):
            with patch('subprocess.Popen') as mock_popen:
                TerminalSpawner._linux(
                    "pdd generate test.prompt",
                    job_id="test-job-123",
                    server_port=9876
                )

                call_args = mock_popen.call_args[0][0]
                full_command = " ".join(str(arg) for arg in call_args)

                # Check for backgrounded curl pattern
                has_backgrounded_curl = "&>/dev/null &" in full_command or \
                                       ">/dev/null &" in full_command

                # Check for wait before exec
                has_wait_before_exec = "wait" in full_command and \
                                      full_command.index("wait") < full_command.index("exec bash")

                assert not has_backgrounded_curl or has_wait_before_exec, \
                    "Curl must complete before exec bash - either run synchronously or add 'wait'"

    def test_windows_callback_is_synchronous(self):
        """
        Test that Windows callback is synchronous (Invoke-RestMethod is sync by default).
        This test should PASS - Windows implementation is correct.
        """
        with patch('subprocess.Popen') as mock_popen:
            TerminalSpawner._windows(
                "pdd generate test.prompt",
                job_id="test-job-123",
                server_port=9876
            )

            call_args = mock_popen.call_args[0][0]
            full_command = " ".join(str(arg) for arg in call_args)

            # Invoke-RestMethod is synchronous by default
            # Just verify it's present and not backgrounded with Start-Job
            assert "Invoke-RestMethod" in full_command
            assert "Start-Job" not in full_command, \
                "Windows callback should be synchronous, not using Start-Job"


# ============================================================================
# Tests for Callback JSON Format (Issue #277)
# ============================================================================


class TestCallbackJsonFormat:
    """
    Tests for callback JSON payload format.

    BUG: The JSON payload uses shell quoting that produces invalid JSON:
    - {"success": 1, "exit_code": } when EXIT_CODE is empty
    - Should be: {"success": true, "exit_code": 0}
    """

    def test_darwin_callback_json_uses_boolean_for_success(self):
        """
        Test that callback JSON uses proper boolean true/false for success field.

        Current bug: Uses 1/0 which may work but is not proper JSON boolean.
        """
        mock_popen = MagicMock()

        with patch('subprocess.Popen', mock_popen):
            with patch.object(Path, 'write_text') as mock_write:
                with patch.object(Path, 'chmod'):
                    TerminalSpawner._darwin(
                        "pdd generate test.prompt",
                        job_id="test-job-123",
                        server_port=9876
                    )

                    script_content = mock_write.call_args[0][0]

                    # The JSON should use boolean true/false, not 1/0
                    # Look for the -d parameter content (quotes are escaped in bash)
                    assert '\\"success\\": true' in script_content or \
                           '\\"success\\": false' in script_content or \
                           '\\"success\\": $SUCCESS_JSON' in script_content or \
                           'SUCCESS_JSON="true"' in script_content, \
                        f"JSON should use boolean true/false for success field. Script:\n{script_content}"

    def test_darwin_callback_handles_empty_exit_code(self):
        """
        Test that callback JSON handles empty EXIT_CODE gracefully.

        BUG: When EXIT_CODE is empty, the JSON becomes invalid:
        {"success": 1, "exit_code": } <- missing value!

        FIX: Should use ${EXIT_CODE:-0} to default to 0.
        """
        mock_popen = MagicMock()

        with patch('subprocess.Popen', mock_popen):
            with patch.object(Path, 'write_text') as mock_write:
                with patch.object(Path, 'chmod'):
                    TerminalSpawner._darwin(
                        "pdd generate test.prompt",
                        job_id="test-job-123",
                        server_port=9876
                    )

                    script_content = mock_write.call_args[0][0]

                    # Should use default value syntax to handle empty EXIT_CODE
                    assert '${EXIT_CODE:-' in script_content or \
                           '${EXIT_CODE:=' in script_content, \
                        f"Should use bash default value for EXIT_CODE. Script:\n{script_content}"

    def test_darwin_callback_exit_code_comparison_handles_empty(self):
        """
        Test that EXIT_CODE comparison is quoted to handle empty values.

        BUG: [ $EXIT_CODE -eq 0 ] fails with "unary operator expected" when empty.
        FIX: Use [ "$EXIT_CODE" -eq 0 ] or [ "${EXIT_CODE:-1}" -eq 0 ]
        """
        mock_popen = MagicMock()

        with patch('subprocess.Popen', mock_popen):
            with patch.object(Path, 'write_text') as mock_write:
                with patch.object(Path, 'chmod'):
                    TerminalSpawner._darwin(
                        "pdd generate test.prompt",
                        job_id="test-job-123",
                        server_port=9876
                    )

                    script_content = mock_write.call_args[0][0]

                    # Find lines with EXIT_CODE comparison
                    lines = script_content.split('\n')
                    comparison_lines = [l for l in lines if 'EXIT_CODE' in l and '-eq' in l]

                    for line in comparison_lines:
                        # Should use quoted variable or default value
                        assert '"$EXIT_CODE"' in line or \
                               '"${EXIT_CODE' in line or \
                               '${EXIT_CODE:-' in line, \
                            f"EXIT_CODE comparison should be quoted. Line: {line}"

    def test_linux_callback_handles_empty_exit_code(self):
        """Test Linux callback also handles empty EXIT_CODE."""
        with patch('shutil.which', return_value="/usr/bin/gnome-terminal"):
            with patch('subprocess.Popen') as mock_popen:
                TerminalSpawner._linux(
                    "pdd generate test.prompt",
                    job_id="test-job-123",
                    server_port=9876
                )

                call_args = mock_popen.call_args[0][0]
                full_command = " ".join(str(arg) for arg in call_args)

                assert '${EXIT_CODE:-' in full_command or \
                       '${EXIT_CODE:=' in full_command, \
                    f"Should use bash default value for EXIT_CODE. Command:\n{full_command}"

    def test_linux_callback_json_uses_boolean_for_success(self):
        """Test Linux callback uses proper boolean true/false for success field."""
        with patch('shutil.which', return_value="/usr/bin/gnome-terminal"):
            with patch('subprocess.Popen') as mock_popen:
                TerminalSpawner._linux(
                    "pdd generate test.prompt",
                    job_id="test-job-123",
                    server_port=9876
                )

                call_args = mock_popen.call_args[0][0]
                full_command = " ".join(str(arg) for arg in call_args)

                # Check for proper boolean handling (quotes are escaped in bash)
                assert '\\"success\\": true' in full_command or \
                       '\\"success\\": false' in full_command or \
                       '\\"success\\": $SUCCESS_JSON' in full_command or \
                       'SUCCESS_JSON="true"' in full_command, \
                    f"JSON should use boolean true/false for success field. Command:\n{full_command}"


# ============================================================================
# Tests for Python Environment Preservation (Issue #347)
# ============================================================================


class TestPythonEnvironmentPreservation:
    """
    Tests for Python environment (conda/virtualenv) preservation in spawned terminals.

    Issue #347: When pdd connect spawns local terminals, they don't inherit
    the conda/virtualenv environment from the parent process. This causes
    commands like 'pdd' to fail if they're only available in the virtual env.

    These tests verify that the TerminalSpawner detects and activates the
    parent process's Python environment in the spawned terminal.
    """

    # --------------------------------------------------------------------------
    # Conda Environment Detection Tests
    # --------------------------------------------------------------------------

    def test_darwin_detects_conda_environment(self):
        """
        FAILING TEST: macOS spawner should detect CONDA_PREFIX and activate the env.

        When CONDA_PREFIX is set, the generated script should include
        'conda activate <env>' or 'source <conda_prefix>/bin/activate' before
        the user's command.
        """
        mock_popen = MagicMock()

        with patch('subprocess.Popen', mock_popen):
            with patch.object(Path, 'write_text') as mock_write:
                with patch.object(Path, 'chmod'):
                    with patch.dict(os.environ, {
                        'CONDA_PREFIX': '/opt/anaconda3/envs/myenv',
                        'CONDA_DEFAULT_ENV': 'myenv'
                    }):
                        TerminalSpawner._darwin("pdd sync foo")

                        script_content = mock_write.call_args[0][0]

                        # The script should activate the conda environment
                        # Either using 'conda activate' or 'source .../activate'
                        has_conda_activation = (
                            'conda activate' in script_content or
                            'source' in script_content and 'activate' in script_content
                        )

                        assert has_conda_activation, (
                            f"Script should activate conda environment.\n"
                            f"Expected 'conda activate myenv' or "
                            f"'source /opt/anaconda3/envs/myenv/bin/activate'\n"
                            f"Got script:\n{script_content}"
                        )

    def test_darwin_conda_activation_precedes_command(self):
        """
        Test that conda activation happens BEFORE the user's command.

        The activation must come first so the command runs in the correct env.
        """
        mock_popen = MagicMock()

        with patch('subprocess.Popen', mock_popen):
            with patch.object(Path, 'write_text') as mock_write:
                with patch.object(Path, 'chmod'):
                    with patch.dict(os.environ, {
                        'CONDA_PREFIX': '/opt/anaconda3/envs/testenv',
                        'CONDA_DEFAULT_ENV': 'testenv'
                    }):
                        TerminalSpawner._darwin("pdd generate module.prompt")

                        script_content = mock_write.call_args[0][0]

                        # Find the position of activation and command
                        activation_patterns = [
                            'conda activate',
                            'source',  # source .../activate
                        ]
                        command_marker = 'pdd generate module.prompt'

                        activation_pos = -1
                        for pattern in activation_patterns:
                            pos = script_content.find(pattern)
                            if pos != -1:
                                activation_pos = pos
                                break

                        command_pos = script_content.find(command_marker)

                        assert activation_pos != -1, (
                            f"No conda activation found in script:\n{script_content}"
                        )
                        assert activation_pos < command_pos, (
                            f"Conda activation must come BEFORE user command.\n"
                            f"Activation at position {activation_pos}, "
                            f"command at position {command_pos}\n"
                            f"Script:\n{script_content}"
                        )

    def test_linux_detects_conda_environment(self):
        """
        FAILING TEST: Linux spawner should detect CONDA_PREFIX and activate the env.
        """
        with patch('shutil.which', return_value="/usr/bin/gnome-terminal"):
            with patch('subprocess.Popen') as mock_popen:
                with patch.dict(os.environ, {
                    'CONDA_PREFIX': '/home/user/miniconda3/envs/devenv',
                    'CONDA_DEFAULT_ENV': 'devenv'
                }):
                    TerminalSpawner._linux("pdd sync foo")

                    call_args = mock_popen.call_args[0][0]
                    full_command = " ".join(str(arg) for arg in call_args)

                    has_conda_activation = (
                        'conda activate' in full_command or
                        'source' in full_command and 'activate' in full_command
                    )

                    assert has_conda_activation, (
                        f"Command should activate conda environment.\n"
                        f"Got command:\n{full_command}"
                    )

    def test_windows_detects_conda_environment(self):
        """
        FAILING TEST: Windows spawner should detect CONDA_PREFIX and activate the env.
        """
        with patch('subprocess.Popen') as mock_popen:
            with patch.dict(os.environ, {
                'CONDA_PREFIX': r'C:\Users\test\anaconda3\envs\myenv',
                'CONDA_DEFAULT_ENV': 'myenv'
            }):
                TerminalSpawner._windows("pdd sync foo")

                call_args = mock_popen.call_args[0][0]
                full_command = " ".join(str(arg) for arg in call_args)

                # Windows conda activation uses 'conda activate' or
                # 'Scripts\activate.bat'
                has_conda_activation = (
                    'conda activate' in full_command or
                    'activate' in full_command.lower()
                )

                assert has_conda_activation, (
                    f"Command should activate conda environment.\n"
                    f"Got command:\n{full_command}"
                )

    # --------------------------------------------------------------------------
    # Virtualenv Detection Tests
    # --------------------------------------------------------------------------

    def test_darwin_detects_virtualenv(self):
        """
        FAILING TEST: macOS spawner should detect VIRTUAL_ENV and activate it.

        When VIRTUAL_ENV is set, the generated script should include
        'source <venv>/bin/activate' before the user's command.
        """
        mock_popen = MagicMock()

        with patch('subprocess.Popen', mock_popen):
            with patch.object(Path, 'write_text') as mock_write:
                with patch.object(Path, 'chmod'):
                    # Clear conda env vars to test pure virtualenv
                    env_vars = {
                        'VIRTUAL_ENV': '/Users/test/myproject/.venv',
                    }
                    # Also need to clear CONDA vars if they exist
                    with patch.dict(os.environ, env_vars, clear=False):
                        # Temporarily remove conda vars for this test
                        conda_prefix = os.environ.pop('CONDA_PREFIX', None)
                        conda_env = os.environ.pop('CONDA_DEFAULT_ENV', None)
                        try:
                            TerminalSpawner._darwin("python script.py")

                            script_content = mock_write.call_args[0][0]

                            # Should source the virtualenv activate script
                            assert 'source' in script_content and 'activate' in script_content, (
                                f"Script should activate virtualenv.\n"
                                f"Expected 'source /Users/test/myproject/.venv/bin/activate'\n"
                                f"Got script:\n{script_content}"
                            )
                        finally:
                            # Restore conda vars
                            if conda_prefix:
                                os.environ['CONDA_PREFIX'] = conda_prefix
                            if conda_env:
                                os.environ['CONDA_DEFAULT_ENV'] = conda_env

    def test_linux_detects_virtualenv(self):
        """
        FAILING TEST: Linux spawner should detect VIRTUAL_ENV and activate it.
        """
        with patch('shutil.which', return_value="/usr/bin/gnome-terminal"):
            with patch('subprocess.Popen') as mock_popen:
                env_vars = {
                    'VIRTUAL_ENV': '/home/user/project/venv',
                }
                with patch.dict(os.environ, env_vars, clear=False):
                    conda_prefix = os.environ.pop('CONDA_PREFIX', None)
                    conda_env = os.environ.pop('CONDA_DEFAULT_ENV', None)
                    try:
                        TerminalSpawner._linux("python script.py")

                        call_args = mock_popen.call_args[0][0]
                        full_command = " ".join(str(arg) for arg in call_args)

                        assert 'source' in full_command and 'activate' in full_command, (
                            f"Command should activate virtualenv.\n"
                            f"Got command:\n{full_command}"
                        )
                    finally:
                        if conda_prefix:
                            os.environ['CONDA_PREFIX'] = conda_prefix
                        if conda_env:
                            os.environ['CONDA_DEFAULT_ENV'] = conda_env

    def test_windows_detects_virtualenv(self):
        """
        FAILING TEST: Windows spawner should detect VIRTUAL_ENV and activate it.
        """
        with patch('subprocess.Popen') as mock_popen:
            env_vars = {
                'VIRTUAL_ENV': r'C:\Users\test\project\.venv',
            }
            with patch.dict(os.environ, env_vars, clear=False):
                conda_prefix = os.environ.pop('CONDA_PREFIX', None)
                conda_env = os.environ.pop('CONDA_DEFAULT_ENV', None)
                try:
                    TerminalSpawner._windows("python script.py")

                    call_args = mock_popen.call_args[0][0]
                    full_command = " ".join(str(arg) for arg in call_args)

                    # Windows virtualenv uses Scripts\Activate.ps1
                    assert 'activate' in full_command.lower(), (
                        f"Command should activate virtualenv.\n"
                        f"Got command:\n{full_command}"
                    )
                finally:
                    if conda_prefix:
                        os.environ['CONDA_PREFIX'] = conda_prefix
                    if conda_env:
                        os.environ['CONDA_DEFAULT_ENV'] = conda_env

    # --------------------------------------------------------------------------
    # No Environment Tests (Regression)
    # --------------------------------------------------------------------------

    def test_darwin_no_env_still_works(self):
        """
        Regression test: When no conda/venv is active, spawner should still work.

        This ensures adding environment detection doesn't break the base case.
        """
        mock_popen = MagicMock()

        with patch('subprocess.Popen', mock_popen):
            with patch.object(Path, 'write_text') as mock_write:
                with patch.object(Path, 'chmod'):
                    # Remove all environment variables
                    env_without_python_env = os.environ.copy()
                    env_without_python_env.pop('CONDA_PREFIX', None)
                    env_without_python_env.pop('CONDA_DEFAULT_ENV', None)
                    env_without_python_env.pop('VIRTUAL_ENV', None)

                    with patch.dict(os.environ, env_without_python_env, clear=True):
                        result = TerminalSpawner._darwin("echo hello")

                        assert result is True
                        script_content = mock_write.call_args[0][0]
                        assert "echo hello" in script_content

    def test_linux_no_env_still_works(self):
        """
        Regression test: Linux spawner works without conda/venv.
        """
        with patch('shutil.which', return_value="/usr/bin/gnome-terminal"):
            with patch('subprocess.Popen') as mock_popen:
                env_without_python_env = os.environ.copy()
                env_without_python_env.pop('CONDA_PREFIX', None)
                env_without_python_env.pop('CONDA_DEFAULT_ENV', None)
                env_without_python_env.pop('VIRTUAL_ENV', None)

                with patch.dict(os.environ, env_without_python_env, clear=True):
                    result = TerminalSpawner._linux("echo hello")

                    assert result is True

    def test_windows_no_env_still_works(self):
        """
        Regression test: Windows spawner works without conda/venv.
        """
        with patch('subprocess.Popen') as mock_popen:
            env_without_python_env = os.environ.copy()
            env_without_python_env.pop('CONDA_PREFIX', None)
            env_without_python_env.pop('CONDA_DEFAULT_ENV', None)
            env_without_python_env.pop('VIRTUAL_ENV', None)

            with patch.dict(os.environ, env_without_python_env, clear=True):
                result = TerminalSpawner._windows("echo hello")

                assert result is True
