# tests/test_core_utils.py
"""Tests for core/utils."""
import os
import sys
import subprocess
from pathlib import Path
from unittest.mock import patch, ANY, MagicMock

import pytest
from click.testing import CliRunner
import click

from pdd import cli, __version__, DEFAULT_STRENGTH, DEFAULT_TIME
# Import core.utils to patch functions there
from pdd.core import utils as core_utils

RUN_ALL_TESTS_ENABLED = os.getenv("PDD_RUN_ALL_TESTS") == "1"


def test_cli_onboarding_reminder_shown(monkeypatch, runner, tmp_path):
    """Warn users when no global or project setup artifacts exist."""
    home_dir = tmp_path / "home"
    home_dir.mkdir()
    rc_path = home_dir / ".bashrc"

    monkeypatch.setattr(cli, "auto_update", lambda: None)
    # Patch get_current_shell in pdd.core.utils where it is used
    monkeypatch.setattr(core_utils, "get_current_shell", lambda: "bash")
    # Patch get_shell_rc_path in pdd.core.utils or pdd.cli?
    # The original test used pdd.cli.get_shell_rc_path.
    # Let's see if it's in core.utils.
    # Yes, _should_show_onboarding_reminder calls get_shell_rc_path.
    # It is imported into core.utils from install_completion.
    # So we should patch it in core.utils.
    monkeypatch.setattr(core_utils, "get_shell_rc_path", lambda _shell: str(rc_path))
    monkeypatch.delenv("PDD_SUPPRESS_SETUP_REMINDER", raising=False)

    with patch('pdd.core.utils.Path.home', return_value=home_dir): # Patch Path.home in utils
        with runner.isolated_filesystem():
            result = runner.invoke(cli.cli, [])

    assert result.exit_code == 0
    assert "Complete onboarding with `pdd setup`" in result.output

def test_cli_onboarding_reminder_suppressed_by_project_env(monkeypatch, runner, tmp_path):
    """A project-level .env with API keys suppresses the reminder."""
    home_dir = tmp_path / "home"
    home_dir.mkdir()
    rc_path = home_dir / ".bashrc"

    monkeypatch.setattr(cli, "auto_update", lambda: None)
    monkeypatch.setattr(core_utils, "get_current_shell", lambda: "bash")
    monkeypatch.setattr(core_utils, "get_shell_rc_path", lambda _shell: str(rc_path))
    monkeypatch.delenv("PDD_SUPPRESS_SETUP_REMINDER", raising=False)

    with patch('pdd.core.utils.Path.home', return_value=home_dir):
        with runner.isolated_filesystem():
            Path(".env").write_text("OPENAI_API_KEY=abc123\n", encoding="utf-8")
            result = runner.invoke(cli.cli, [])

    assert result.exit_code == 0
    assert "Complete onboarding with `pdd setup`" not in result.output

def test_cli_onboarding_reminder_suppressed_by_api_env(monkeypatch, runner, tmp_path):
    """Presence of ~/.pdd/api-env suppresses the reminder."""
    home_dir = tmp_path / "home"
    pdd_dir = home_dir / ".pdd"
    pdd_dir.mkdir(parents=True)
    (pdd_dir / "api-env").write_text("export OPENAI_API_KEY=abc123\n", encoding="utf-8")

    rc_path = home_dir / ".zshrc"

    monkeypatch.setattr(cli, "auto_update", lambda: None)
    monkeypatch.setattr(core_utils, "get_current_shell", lambda: "zsh")
    monkeypatch.setattr(core_utils, "get_shell_rc_path", lambda _shell: str(rc_path))
    monkeypatch.delenv("PDD_SUPPRESS_SETUP_REMINDER", raising=False)

    with patch('pdd.core.utils.Path.home', return_value=home_dir):
        with runner.isolated_filesystem():
            result = runner.invoke(cli.cli, [])

    assert result.exit_code == 0
    assert "Complete onboarding with `pdd setup`" not in result.output

# --- Real Command Tests (No Mocking) ---
# These tests remain largely unchanged as they call the *_main functions directly
# or expect exceptions to be raised by those main functions.