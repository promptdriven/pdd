"""
Utility to detect if running in a remote/SSH session or headless environment.
"""
import os
import sys
from typing import Optional, Tuple


def is_remote_session() -> Tuple[bool, str]:
    """
    Detect if the current session is remote (SSH) or headless.

    Returns:
        Tuple[bool, str]: (is_remote, reason) where reason explains why

    Detection criteria:
    1. SSH environment variables (SSH_CONNECTION, SSH_CLIENT, SSH_TTY)
    2. DISPLAY not set (headless Linux/Unix)
    3. WSL without WSLg (Windows Subsystem for Linux)
    """
    # Check SSH environment variables
    if os.environ.get("SSH_CONNECTION"):
        return True, "SSH_CONNECTION environment variable detected"
    if os.environ.get("SSH_CLIENT"):
        return True, "SSH_CLIENT environment variable detected"
    if os.environ.get("SSH_TTY"):
        return True, "SSH_TTY environment variable detected"

    # Check for headless environment (no DISPLAY on Unix/Linux)
    if sys.platform in ("linux", "linux2") or sys.platform == "darwin":
        if not os.environ.get("DISPLAY"):
            return True, "No DISPLAY environment variable (headless)"

    # Check for WSL without WSLg (older WSL versions)
    if os.environ.get("WSL_DISTRO_NAME") and not os.environ.get("WAYLAND_DISPLAY"):
        return True, "WSL environment without display server"

    return False, "Local session with display capability"


def should_skip_browser(explicit_flag: Optional[bool] = None) -> Tuple[bool, str]:
    """
    Determine if browser opening should be skipped.

    Args:
        explicit_flag: True to force browser, False to force no-browser, None to auto-detect

    Returns:
        Tuple[bool, str]: (skip_browser, reason)
    """
    if explicit_flag is True:
        return False, "User explicitly requested browser opening (--browser flag)"
    if explicit_flag is False:
        return True, "User explicitly requested no browser (--no-browser flag)"

    # Auto-detect
    is_remote, reason = is_remote_session()
    if is_remote:
        return True, f"Auto-detected remote session: {reason}"

    return False, "Local session detected, will attempt browser opening"
