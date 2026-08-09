"""Tests for remote session detection utility."""
import os
import sys
from unittest import mock

import pytest

from pdd.core.remote_session import is_remote_session, should_skip_browser


class TestIsRemoteSession:
    """Tests for is_remote_session function."""

    def test_ssh_connection_detected(self):
        """Test that SSH_CONNECTION environment variable is detected."""
        with mock.patch.dict(os.environ, {"SSH_CONNECTION": "192.168.1.1"}, clear=True):
            is_remote, reason = is_remote_session()
            assert is_remote is True
            assert "SSH_CONNECTION" in reason

    def test_ssh_client_detected(self):
        """Test that SSH_CLIENT environment variable is detected."""
        with mock.patch.dict(os.environ, {"SSH_CLIENT": "192.168.1.1"}, clear=True):
            is_remote, reason = is_remote_session()
            assert is_remote is True
            assert "SSH_CLIENT" in reason

    def test_ssh_tty_detected(self):
        """Test that SSH_TTY environment variable is detected."""
        with mock.patch.dict(os.environ, {"SSH_TTY": "/dev/pts/0"}, clear=True):
            is_remote, reason = is_remote_session()
            assert is_remote is True
            assert "SSH_TTY" in reason

    def test_no_display_on_linux(self):
        """Test that missing DISPLAY on Linux is detected as headless."""
        with mock.patch.dict(os.environ, {}, clear=True):
            with mock.patch.object(sys, "platform", "linux"):
                is_remote, reason = is_remote_session()
                assert is_remote is True
                assert "DISPLAY" in reason

    def test_no_display_on_darwin(self):
        """Test that missing DISPLAY on macOS is detected as headless."""
        with mock.patch.dict(os.environ, {}, clear=True):
            with mock.patch.object(sys, "platform", "darwin"):
                is_remote, reason = is_remote_session()
                assert is_remote is True
                assert "DISPLAY" in reason

    def test_wsl_without_wslg(self):
        """Test that WSL without WSLg is detected as remote."""
        with mock.patch.dict(
            os.environ, {"WSL_DISTRO_NAME": "Ubuntu", "DISPLAY": ":0"}, clear=True
        ):
            is_remote, reason = is_remote_session()
            assert is_remote is True
            assert "WSL" in reason

    def test_wsl_with_wslg(self):
        """Test that WSL with WSLg is NOT detected as remote."""
        with mock.patch.dict(
            os.environ,
            {"WSL_DISTRO_NAME": "Ubuntu", "WAYLAND_DISPLAY": "wayland-0", "DISPLAY": ":0"},
            clear=True,
        ):
            is_remote, reason = is_remote_session()
            assert is_remote is False
            assert "Local session" in reason

    def test_local_session_with_display(self):
        """Test that local session with DISPLAY is NOT detected as remote."""
        with mock.patch.dict(os.environ, {"DISPLAY": ":0"}, clear=True):
            with mock.patch.object(sys, "platform", "linux"):
                is_remote, reason = is_remote_session()
                assert is_remote is False
                assert "Local session" in reason

    def test_windows_local_session(self):
        """Test that Windows local session is NOT detected as remote."""
        with mock.patch.dict(os.environ, {}, clear=True):
            with mock.patch.object(sys, "platform", "win32"):
                is_remote, reason = is_remote_session()
                assert is_remote is False
                assert "Local session" in reason

    def test_ssh_takes_precedence_over_display(self):
        """Test that SSH detection takes precedence even when DISPLAY is set."""
        with mock.patch.dict(
            os.environ, {"SSH_CONNECTION": "192.168.1.1", "DISPLAY": ":0"}, clear=True
        ):
            is_remote, reason = is_remote_session()
            assert is_remote is True
            assert "SSH_CONNECTION" in reason


class TestShouldSkipBrowser:
    """Tests for should_skip_browser function."""

    def test_explicit_flag_true_forces_browser(self):
        """Test that explicit_flag=True forces browser opening."""
        with mock.patch.dict(os.environ, {"SSH_CONNECTION": "192.168.1.1"}, clear=True):
            skip, reason = should_skip_browser(explicit_flag=True)
            assert skip is False
            assert "--browser flag" in reason

    def test_explicit_flag_false_forces_no_browser(self):
        """Test that explicit_flag=False forces no browser."""
        with mock.patch.dict(os.environ, {"DISPLAY": ":0"}, clear=True):
            with mock.patch.object(sys, "platform", "linux"):
                skip, reason = should_skip_browser(explicit_flag=False)
                assert skip is True
                assert "--no-browser flag" in reason

    def test_auto_detect_remote_session(self):
        """Test that auto-detect skips browser for remote sessions."""
        with mock.patch.dict(os.environ, {"SSH_CONNECTION": "192.168.1.1"}, clear=True):
            skip, reason = should_skip_browser(explicit_flag=None)
            assert skip is True
            assert "Auto-detected" in reason
            assert "SSH_CONNECTION" in reason

    def test_auto_detect_local_session(self):
        """Test that auto-detect opens browser for local sessions."""
        with mock.patch.dict(os.environ, {"DISPLAY": ":0"}, clear=True):
            with mock.patch.object(sys, "platform", "linux"):
                skip, reason = should_skip_browser(explicit_flag=None)
                assert skip is False
                assert "Local session" in reason

    def test_default_parameter_auto_detects(self):
        """Test that default parameter (None) auto-detects."""
        with mock.patch.dict(os.environ, {"SSH_TTY": "/dev/pts/0"}, clear=True):
            skip, reason = should_skip_browser()
            assert skip is True
            assert "Auto-detected" in reason

    def test_override_in_ssh_session(self):
        """Test that user can override auto-detection in SSH session."""
        with mock.patch.dict(os.environ, {"SSH_CONNECTION": "192.168.1.1"}, clear=True):
            # Without override: should skip browser
            skip_auto, _ = should_skip_browser(explicit_flag=None)
            assert skip_auto is True

            # With override: should open browser
            skip_override, reason = should_skip_browser(explicit_flag=True)
            assert skip_override is False
            assert "explicitly requested" in reason
