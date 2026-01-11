"""
Tests for pdd.server.terminal_spawner module.

These tests verify the cross-platform terminal spawning functionality.
Most tests use mocking to avoid actually spawning terminal windows.
"""

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
