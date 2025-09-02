import pytest
import os
from unittest.mock import patch
from pdd.install_completion import get_shell_rc_path

def test_get_shell_rc_path():
    """Verify that get_shell_rc_path returns expected defaults for known shells."""
    home = os.path.expanduser("~")

    assert get_shell_rc_path("bash") == os.path.join(home, ".bashrc")
    assert get_shell_rc_path("zsh") == os.path.join(home, ".zshrc")
    assert get_shell_rc_path("fish") == os.path.join(home, ".config", "fish", "config.fish")
    assert get_shell_rc_path("csh") is None
