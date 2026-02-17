"""Tests for pdd/cli_detector.py"""

import subprocess
import os
import sys
from unittest import mock
from pathlib import Path

import pytest

from pdd.cli_detector import (
    _CLI_COMMANDS,
    _API_KEY_ENV_VARS,
    _INSTALL_COMMANDS,
    _CLI_DISPLAY_NAMES,
    _which,
    _has_api_key,
    _npm_available,
    _prompt_yes_no,
    _run_install,
    detect_cli_tools,
    detect_and_bootstrap_cli,
    CliBootstrapResult,
    _save_api_key,
    _find_cli_binary,
    _prompt_input,
    console
)


# ---------------------------------------------------------------------------
# Tests for constants
# ---------------------------------------------------------------------------


class TestConstants:
    """Tests for static mappings."""

    def test_cli_commands_has_expected_providers(self):
        """Should have CLI commands for known providers."""
        assert "anthropic" in _CLI_COMMANDS
        assert "google" in _CLI_COMMANDS
        assert "openai" in _CLI_COMMANDS

    def test_cli_commands_values(self):
        """CLI command values should be correct."""
        assert _CLI_COMMANDS["anthropic"] == "claude"
        assert _CLI_COMMANDS["google"] == "gemini"
        assert _CLI_COMMANDS["openai"] == "codex"

    def test_api_key_env_vars_has_expected_providers(self):
        """Should have API key env vars for known providers."""
        assert "anthropic" in _API_KEY_ENV_VARS
        assert "google" in _API_KEY_ENV_VARS
        assert "openai" in _API_KEY_ENV_VARS

    def test_api_key_env_vars_values(self):
        """API key env var values should be correct."""
        assert _API_KEY_ENV_VARS["anthropic"] == "ANTHROPIC_API_KEY"
        assert _API_KEY_ENV_VARS["google"] == "GOOGLE_API_KEY"
        assert _API_KEY_ENV_VARS["openai"] == "OPENAI_API_KEY"

    def test_install_commands_has_expected_providers(self):
        """Should have install commands for known providers."""
        assert "anthropic" in _INSTALL_COMMANDS
        assert "google" in _INSTALL_COMMANDS
        assert "openai" in _INSTALL_COMMANDS

    def test_install_commands_are_npm_commands(self):
        """Install commands should be npm install commands."""
        for provider, cmd in _INSTALL_COMMANDS.items():
            assert cmd.startswith("npm install -g ")

    def test_cli_display_names_has_expected_providers(self):
        """Should have display names for known providers."""
        assert "anthropic" in _CLI_DISPLAY_NAMES
        assert "google" in _CLI_DISPLAY_NAMES
        assert "openai" in _CLI_DISPLAY_NAMES

    def test_cli_display_names_are_human_readable(self):
        """Display names should be human-readable."""
        assert _CLI_DISPLAY_NAMES["anthropic"] == "Claude CLI"
        assert _CLI_DISPLAY_NAMES["google"] == "Gemini CLI"
        assert _CLI_DISPLAY_NAMES["openai"] == "Codex CLI"

    def test_all_providers_have_consistent_mappings(self):
        """All providers should have entries in all mappings."""
        providers = set(_CLI_COMMANDS.keys())

        assert providers == set(_API_KEY_ENV_VARS.keys())
        assert providers == set(_INSTALL_COMMANDS.keys())
        assert providers == set(_CLI_DISPLAY_NAMES.keys())


# ---------------------------------------------------------------------------
# Tests for _which
# ---------------------------------------------------------------------------


class TestWhich:
    """Tests for _which function."""

    def test_returns_path_for_existing_command(self):
        """Should return path for commands that exist."""
        # 'ls' should exist on all Unix-like systems
        result = _which("ls")
        assert result is not None
        assert "ls" in result

    def test_returns_none_for_nonexistent_command(self):
        """Should return None for commands that don't exist."""
        result = _which("nonexistent_command_xyz_12345")
        assert result is None

    def test_returns_none_for_empty_string(self):
        """Should return None for empty command string."""
        result = _which("")
        assert result is None


# ---------------------------------------------------------------------------
# Tests for _has_api_key
# ---------------------------------------------------------------------------


class TestHasApiKey:
    """Tests for _has_api_key function."""

    def test_returns_true_when_key_set(self, monkeypatch):
        """Should return True when API key is set."""
        monkeypatch.setenv("ANTHROPIC_API_KEY", "test-key-value")
        assert _has_api_key("anthropic") is True

    def test_returns_false_when_key_not_set(self, monkeypatch):
        """Should return False when API key is not set."""
        monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
        assert _has_api_key("anthropic") is False

    def test_returns_false_when_key_empty(self, monkeypatch):
        """Should return False when API key is empty string."""
        monkeypatch.setenv("ANTHROPIC_API_KEY", "")
        assert _has_api_key("anthropic") is False

    def test_returns_false_when_key_whitespace(self, monkeypatch):
        """Should return False when API key is only whitespace."""
        monkeypatch.setenv("ANTHROPIC_API_KEY", "   ")
        assert _has_api_key("anthropic") is False

    def test_returns_false_for_unknown_provider(self, monkeypatch):
        """Should return False for unknown providers."""
        # Unknown provider won't be in _API_KEY_ENV_VARS
        assert _has_api_key("unknown_provider") is False


# ---------------------------------------------------------------------------
# Tests for _npm_available
# ---------------------------------------------------------------------------


class TestNpmAvailable:
    """Tests for _npm_available function."""

    def test_returns_bool(self):
        """Should return a boolean."""
        result = _npm_available()
        assert isinstance(result, bool)

    def test_uses_which_internally(self):
        """Should use _which to find npm."""
        with mock.patch("pdd.cli_detector._which") as mock_which:
            mock_which.return_value = "/usr/bin/npm"
            result = _npm_available()
            mock_which.assert_called_once_with("npm")
            assert result is True

    def test_returns_false_when_npm_not_found(self):
        """Should return False when npm is not installed."""
        with mock.patch("pdd.cli_detector._which", return_value=None):
            assert _npm_available() is False


# ---------------------------------------------------------------------------
# Tests for _prompt_yes_no
# ---------------------------------------------------------------------------


class TestPromptYesNo:
    """Tests for _prompt_yes_no function."""

    def test_returns_true_for_y(self):
        """Should return True for 'y' input."""
        with mock.patch("pdd.cli_detector._prompt_input", return_value="y"):
            assert _prompt_yes_no("Test? ") is True

    def test_returns_true_for_yes(self):
        """Should return True for 'yes' input."""
        with mock.patch("pdd.cli_detector._prompt_input", return_value="yes"):
            assert _prompt_yes_no("Test? ") is True

    def test_returns_true_for_Y_uppercase(self):
        """Should return True for uppercase 'Y' input."""
        with mock.patch("pdd.cli_detector._prompt_input", return_value="Y"):
            assert _prompt_yes_no("Test? ") is True

    def test_returns_true_for_YES_uppercase(self):
        """Should return True for uppercase 'YES' input."""
        with mock.patch("pdd.cli_detector._prompt_input", return_value="YES"):
            assert _prompt_yes_no("Test? ") is True

    def test_returns_false_for_n(self):
        """Should return False for 'n' input."""
        with mock.patch("pdd.cli_detector._prompt_input", return_value="n"):
            assert _prompt_yes_no("Test? ") is False

    def test_returns_false_for_no(self):
        """Should return False for 'no' input."""
        with mock.patch("pdd.cli_detector._prompt_input", return_value="no"):
            assert _prompt_yes_no("Test? ") is False

    def test_returns_false_for_empty(self):
        """Should return False for empty input (default is No)."""
        with mock.patch("pdd.cli_detector._prompt_input", return_value=""):
            assert _prompt_yes_no("Test? ") is False

    def test_returns_false_for_random_input(self):
        """Should return False for unrecognized input."""
        with mock.patch("pdd.cli_detector._prompt_input", return_value="maybe"):
            assert _prompt_yes_no("Test? ") is False

    def test_handles_eof_error(self):
        """Should return False on EOFError."""
        with mock.patch("pdd.cli_detector._prompt_input", side_effect=EOFError()):
            assert _prompt_yes_no("Test? ") is False

    def test_handles_keyboard_interrupt(self):
        """Should return False on KeyboardInterrupt."""
        with mock.patch("pdd.cli_detector._prompt_input", side_effect=KeyboardInterrupt()):
            assert _prompt_yes_no("Test? ") is False

    def test_strips_whitespace(self):
        """Should strip whitespace from input."""
        with mock.patch("pdd.cli_detector._prompt_input", return_value="  y  "):
            assert _prompt_yes_no("Test? ") is True


# ---------------------------------------------------------------------------
# Tests for _run_install
# ---------------------------------------------------------------------------


class TestRunInstall:
    """Tests for _run_install function."""

    def test_returns_true_on_success(self):
        """Should return True when command succeeds."""
        with mock.patch("subprocess.run") as mock_run:
            mock_run.return_value = mock.MagicMock(returncode=0)
            result = _run_install("echo test")
            assert result is True

    def test_returns_false_on_failure(self):
        """Should return False when command fails."""
        with mock.patch("subprocess.run") as mock_run:
            mock_run.return_value = mock.MagicMock(returncode=1)
            result = _run_install("exit 1")
            assert result is False

    def test_returns_false_on_exception(self):
        """Should return False on subprocess exception."""
        with mock.patch("subprocess.run", side_effect=Exception("Test error")):
            result = _run_install("failing command")
            assert result is False

    def test_runs_command_with_shell(self):
        """Should run command with shell=True."""
        with mock.patch("subprocess.run") as mock_run:
            mock_run.return_value = mock.MagicMock(returncode=0)
            _run_install("npm install -g test")
            mock_run.assert_called_once()
            call_kwargs = mock_run.call_args[1]
            assert call_kwargs["shell"] is True


# ---------------------------------------------------------------------------
# Tests for detect_cli_tools
# ---------------------------------------------------------------------------


class TestDetectCliTools:
    """Tests for detect_cli_tools function."""

    def test_prints_header(self, capsys):
        """Should print the detection header."""
        with mock.patch("pdd.cli_detector._which", return_value=None):
            with mock.patch("pdd.cli_detector._has_api_key", return_value=False):
                detect_cli_tools()

        captured = capsys.readouterr()
        assert "Agentic CLI Tool Detection" in captured.out
        assert "pdd fix, pdd change, pdd bug" in captured.out

    def test_shows_found_cli(self, capsys):
        """Should show checkmark for found CLI tools."""
        with mock.patch("pdd.cli_detector._which") as mock_which:
            mock_which.side_effect = lambda cmd: "/usr/bin/claude" if cmd == "claude" else None
            with mock.patch("pdd.cli_detector._has_api_key", return_value=False):
                detect_cli_tools()

        captured = capsys.readouterr()
        assert "✓" in captured.out
        assert "Claude CLI" in captured.out

    def test_shows_not_found_cli(self, capsys):
        """Should show X for missing CLI tools."""
        with mock.patch("pdd.cli_detector._which", return_value=None):
            with mock.patch("pdd.cli_detector._has_api_key", return_value=False):
                detect_cli_tools()

        captured = capsys.readouterr()
        assert "✗" in captured.out
        assert "Not found" in captured.out

    def test_shows_api_key_status_when_cli_found(self, capsys):
        """Should show API key status when CLI is found."""
        with mock.patch("pdd.cli_detector._which", return_value="/usr/bin/claude"):
            with mock.patch("pdd.cli_detector._has_api_key") as mock_has_key:
                mock_has_key.return_value = True
                detect_cli_tools()

        captured = capsys.readouterr()
        assert "set" in captured.out

    def test_warns_when_cli_found_but_no_key(self, capsys):
        """Should warn when CLI found but API key not set."""
        with mock.patch("pdd.cli_detector._which", return_value="/usr/bin/claude"):
            with mock.patch("pdd.cli_detector._has_api_key", return_value=False):
                detect_cli_tools()

        captured = capsys.readouterr()
        assert "not set" in captured.out
        assert "won't be usable" in captured.out

    def test_suggests_install_when_key_but_no_cli(self, capsys):
        """Should suggest installation when API key is set but CLI is missing."""
        with mock.patch("pdd.cli_detector._which", return_value=None):
            with mock.patch("pdd.cli_detector._has_api_key") as mock_has_key:
                # Only anthropic has key set
                mock_has_key.side_effect = lambda p: p == "anthropic"
                with mock.patch("pdd.cli_detector._npm_available", return_value=False):
                    detect_cli_tools()

        captured = capsys.readouterr()
        assert "install the cli" in captured.out.lower()

    def test_offers_installation_when_npm_available(self, capsys):
        """Should offer installation when npm is available."""
        with mock.patch("pdd.cli_detector._which", return_value=None):
            with mock.patch("pdd.cli_detector._has_api_key") as mock_has_key:
                mock_has_key.side_effect = lambda p: p == "anthropic"
                with mock.patch("pdd.cli_detector._npm_available", return_value=True):
                    with mock.patch("pdd.cli_detector._prompt_yes_no", return_value=False):
                        detect_cli_tools()

        captured = capsys.readouterr()
        assert "Install now?" in captured.out or "Install:" in captured.out

    def test_shows_npm_not_installed_message(self, capsys):
        """Should show message when npm is not installed."""
        with mock.patch("pdd.cli_detector._which", return_value=None):
            with mock.patch("pdd.cli_detector._has_api_key") as mock_has_key:
                mock_has_key.side_effect = lambda p: p == "anthropic"
                with mock.patch("pdd.cli_detector._npm_available", return_value=False):
                    detect_cli_tools()

        captured = capsys.readouterr()
        assert "npm is not installed" in captured.out

    def test_runs_installation_on_yes(self, capsys):
        """Should run installation when user says yes."""
        with mock.patch("pdd.cli_detector._which") as mock_which:
            mock_which.side_effect = [None, None, None, "/usr/bin/claude"]  # Found after install
            with mock.patch("pdd.cli_detector._has_api_key") as mock_has_key:
                mock_has_key.side_effect = lambda p: p == "anthropic"
                with mock.patch("pdd.cli_detector._npm_available", return_value=True):
                    with mock.patch("pdd.cli_detector._prompt_yes_no", return_value=True):
                        with mock.patch("pdd.cli_detector._run_install", return_value=True):
                            detect_cli_tools()

        captured = capsys.readouterr()
        assert "successfully" in captured.out or "completed" in captured.out

    def test_shows_failure_message_on_install_fail(self, capsys):
        """Should show failure message when installation fails."""
        with mock.patch("pdd.cli_detector._which", return_value=None):
            with mock.patch("pdd.cli_detector._has_api_key") as mock_has_key:
                mock_has_key.side_effect = lambda p: p == "anthropic"
                with mock.patch("pdd.cli_detector._npm_available", return_value=True):
                    with mock.patch("pdd.cli_detector._prompt_yes_no", return_value=True):
                        with mock.patch("pdd.cli_detector._run_install", return_value=False):
                            detect_cli_tools()

        captured = capsys.readouterr()
        assert "failed" in captured.out.lower() or "manually" in captured.out.lower()

    def test_shows_skip_message_on_no(self, capsys):
        """Should show skip message when user declines installation."""
        with mock.patch("pdd.cli_detector._which", return_value=None):
            with mock.patch("pdd.cli_detector._has_api_key") as mock_has_key:
                mock_has_key.side_effect = lambda p: p == "anthropic"
                with mock.patch("pdd.cli_detector._npm_available", return_value=True):
                    with mock.patch("pdd.cli_detector._prompt_yes_no", return_value=False):
                        detect_cli_tools()

        captured = capsys.readouterr()
        assert "Skipped" in captured.out or "later" in captured.out

    def test_shows_quick_start_when_nothing_installed(self, capsys):
        """Should show quick start guide when no CLIs are installed."""
        with mock.patch("pdd.cli_detector._which", return_value=None):
            with mock.patch("pdd.cli_detector._has_api_key", return_value=False):
                detect_cli_tools()

        captured = capsys.readouterr()
        assert "Quick start" in captured.out or "No CLI tools found" in captured.out

    def test_shows_all_installed_message(self, capsys):
        """Should show success message when all CLIs with keys are installed."""
        with mock.patch("pdd.cli_detector._which", return_value="/usr/bin/cli"):
            with mock.patch("pdd.cli_detector._has_api_key", return_value=True):
                detect_cli_tools()

        captured = capsys.readouterr()
        assert "All CLI tools with matching API keys are installed" in captured.out


# ---------------------------------------------------------------------------
# Integration tests
# ---------------------------------------------------------------------------


class TestIntegration:
    """Integration tests for CLI detector."""

    def test_detect_cli_tools_handles_import_error(self, capsys):
        """Should handle missing agentic_common gracefully."""
        with mock.patch("pdd.cli_detector._which", return_value=None):
            with mock.patch("pdd.cli_detector._has_api_key", return_value=False):
                # The function imports get_available_agents but handles import errors
                detect_cli_tools()

        # Should complete without error
        captured = capsys.readouterr()
        assert "Agentic CLI Tool Detection" in captured.out

    def test_detect_cli_tools_complete_flow(self, capsys):
        """Test complete detection flow with mixed results."""
        def mock_which(cmd):
            return "/usr/bin/claude" if cmd == "claude" else None

        def mock_has_key(provider):
            return provider in ["anthropic", "openai"]

        with mock.patch("pdd.cli_detector._which", side_effect=mock_which):
            with mock.patch("pdd.cli_detector._has_api_key", side_effect=mock_has_key):
                with mock.patch("pdd.cli_detector._npm_available", return_value=False):
                    detect_cli_tools()

        captured = capsys.readouterr()
        # Claude should show as found
        assert "Claude CLI" in captured.out
        assert "✓" in captured.out
        # Others should show as not found
        assert "✗" in captured.out


# ---------------------------------------------------------------------------
# Edge case tests
# ---------------------------------------------------------------------------


class TestEdgeCases:
    """Test edge cases and error handling."""

    def test_handles_subprocess_timeout(self):
        """Should handle subprocess timeout gracefully."""
        with mock.patch("subprocess.run", side_effect=subprocess.TimeoutExpired("cmd", 30)):
            result = _run_install("slow command")
            assert result is False

    def test_empty_env_var_treated_as_not_set(self, monkeypatch):
        """Empty string env vars should be treated as not set."""
        monkeypatch.setenv("ANTHROPIC_API_KEY", "")
        assert _has_api_key("anthropic") is False

    def test_whitespace_only_env_var_treated_as_not_set(self, monkeypatch):
        """Whitespace-only env vars should be treated as not set."""
        monkeypatch.setenv("ANTHROPIC_API_KEY", "   \t\n  ")
        assert _has_api_key("anthropic") is False



# ---------------------------------------------------------------------------
# Fixtures for bootstrap tests
# ---------------------------------------------------------------------------

@pytest.fixture
def mock_console():
    with mock.patch("pdd.cli_detector.console") as m:
        yield m

@pytest.fixture
def mock_env():
    with mock.patch.dict(os.environ, {}, clear=True):
        yield os.environ

@pytest.fixture
def mock_which():
    with mock.patch("shutil.which") as m:
        yield m

@pytest.fixture
def mock_input():
    with mock.patch("pdd.cli_detector._prompt_input") as m:
        yield m

@pytest.fixture
def mock_subprocess():
    with mock.patch("subprocess.run") as m:
        yield m

@pytest.fixture
def mock_home(tmp_path):
    """Mock Path.home() to return a temporary directory."""
    with mock.patch("pathlib.Path.home", return_value=tmp_path):
        yield tmp_path

# ---------------------------------------------------------------------------
# Helper Function Tests
# ---------------------------------------------------------------------------

def test_save_api_key_bash(mock_home, mock_console):
    """Test saving API key for bash shell."""
    shell = "bash"
    key_name = "TEST_KEY"
    key_value = "sk-test-123"
    
    # Create a dummy .bashrc
    rc_file = mock_home / ".bashrc"
    rc_file.write_text("# existing content\n")
    
    success = _save_api_key(key_name, key_value, shell)
    
    assert success is True
    
    # Check api-env file
    api_env = mock_home / ".pdd" / "api-env.bash"
    assert api_env.exists()
    content = api_env.read_text()
    assert f"export {key_name}={key_value}" in content
    
    # Check RC file update
    rc_content = rc_file.read_text()
    assert f"source {api_env}" in rc_content
    assert os.environ[key_name] == key_value

def test_save_api_key_fish(mock_home, mock_console):
    """Test saving API key for fish shell."""
    shell = "fish"
    key_name = "TEST_KEY"
    key_value = "sk-test-123"
    
    # Create dummy config.fish
    fish_config = mock_home / ".config" / "fish" / "config.fish"
    fish_config.parent.mkdir(parents=True)
    fish_config.write_text("")
    
    success = _save_api_key(key_name, key_value, shell)
    
    assert success is True
    
    api_env = mock_home / ".pdd" / "api-env.fish"
    content = api_env.read_text()
    assert f"set -gx {key_name} {key_value}" in content
    
    rc_content = fish_config.read_text()
    assert f"test -f {api_env} ; and source {api_env}" in rc_content

def test_find_cli_binary_fallback(mock_which):
    """Test finding binary in fallback paths when shutil.which fails."""
    mock_which.return_value = None
    
    # Mock os.path.exists and is_file/access
    with mock.patch("pathlib.Path.exists", return_value=True), \
         mock.patch("pathlib.Path.is_file", return_value=True), \
         mock.patch("os.access", return_value=True):
        
        # Should find it in the first fallback path checked
        result = _find_cli_binary("claude")
        assert result is not None
        assert "claude" in result

# ---------------------------------------------------------------------------
# detect_and_bootstrap_cli Tests
# ---------------------------------------------------------------------------

def test_bootstrap_happy_path(mock_env, mock_input, mock_console):
    """
    Scenario: Claude is installed and ANTHROPIC_API_KEY is set.
    All 3 CLIs are shown in table. User selects Claude (1).
    Expect: Return with success, no install or API key prompt needed.
    """
    mock_env["ANTHROPIC_API_KEY"] = "sk-existing"
    mock_input.return_value = "1"  # User selects Claude

    with mock.patch("pdd.cli_detector._find_cli_binary") as mock_find:
        mock_find.side_effect = lambda x: "/usr/bin/claude" if x == "claude" else None
        result = detect_and_bootstrap_cli()

    assert result.cli_name == "claude"
    assert result.provider == "anthropic"
    assert result.api_key_configured is True
    assert result.cli_path == "/usr/bin/claude"

    # Table should be shown with all 3 CLIs before the user picks
    all_printed = " ".join(str(c) for c in mock_console.print.call_args_list)
    assert "Claude CLI" in all_printed
    assert "Codex CLI" in all_printed
    assert "Gemini CLI" in all_printed

def test_bootstrap_key_needed_user_provides(mock_which, mock_env, mock_input, mock_home, mock_console):
    """
    Scenario: Claude installed, no key. User enters key.
    Expect: Key saved, success returned.
    """
    mock_which.side_effect = lambda x: f"/usr/bin/{x}" if x == "claude" else None
    # No API key in env
    
    mock_input.return_value = "sk-new-key"
    
    result = detect_and_bootstrap_cli()
    
    assert result.cli_name == "claude"
    assert result.provider == "anthropic"
    assert result.api_key_configured is True
    
    # Verify key was saved to env
    assert os.environ["ANTHROPIC_API_KEY"] == "sk-new-key"
    # Verify file write happened (via _save_api_key logic)
    api_env = mock_home / ".pdd" / "api-env.bash" # Default shell is bash
    assert api_env.exists()

def test_bootstrap_key_needed_user_skips(mock_which, mock_env, mock_input, mock_console):
    """
    Scenario: Claude installed, no key. User presses Enter (skips).
    Expect: Success returned but api_key_configured=False.
    """
    mock_which.side_effect = lambda x: f"/usr/bin/{x}" if x == "claude" else None
    mock_input.return_value = "" # Empty input
    
    result = detect_and_bootstrap_cli()
    
    assert result.cli_name == "claude"
    assert result.api_key_configured is False
    mock_console.print.assert_any_call("  [dim]Note: Claude CLI may still work with subscription auth.[/dim]")

def test_bootstrap_no_cli_user_declines(mock_which, mock_input, mock_console):
    """
    Scenario: No CLIs found. User says 'n' to install.
    Expect: Empty result.
    """
    mock_which.return_value = None # No CLIs found
    mock_input.return_value = "n"
    
    result = detect_and_bootstrap_cli()
    
    assert result.cli_name == ""
    assert result.provider == ""
    mock_console.print.assert_any_call("  [dim]Skipped CLI setup. You can run `pdd setup` again later.[/dim]")

def test_bootstrap_install_npm_missing(mock_input, mock_console):
    """
    Scenario: No CLIs found. All 3 shown in table. User selects Claude (1),
    says yes to install. npm not found.
    Expect: Error message, empty result.
    """
    mock_input.side_effect = ["1", "y"]  # Select Claude, then yes to install

    with mock.patch("pdd.cli_detector._find_cli_binary", return_value=None), \
         mock.patch("pdd.cli_detector._npm_available", return_value=False):
        result = detect_and_bootstrap_cli()

    assert result.cli_name == ""
    all_printed = " ".join(str(c) for c in mock_console.print.call_args_list)
    assert "npm is not installed" in all_printed

def test_bootstrap_install_success(mock_input, mock_subprocess, mock_home, mock_console):
    """
    Scenario: No CLIs found. All 3 shown in table. User selects Claude (1),
    says yes to install. Install succeeds. User provides API key.
    Expect: Full success.
    """
    # Inputs: select Claude, yes to install, provide API key
    mock_input.side_effect = ["1", "y", "sk-key"]

    # _find_cli_binary returns None on initial scan; returns the path after install
    claude_calls = [0]
    def find_binary(name):
        if name == "claude":
            claude_calls[0] += 1
            return "/usr/bin/claude" if claude_calls[0] > 1 else None
        return None

    mock_subprocess.return_value.returncode = 0

    with mock.patch("pdd.cli_detector._find_cli_binary", side_effect=find_binary), \
         mock.patch("pdd.cli_detector._npm_available", return_value=True):
        result = detect_and_bootstrap_cli()

    assert result.cli_name == "claude"
    assert result.cli_path == "/usr/bin/claude"
    assert result.api_key_configured is True

    # Verify the correct install command was run
    mock_subprocess.assert_called_with(
        "npm install -g @anthropic-ai/claude-code",
        shell=True, capture_output=True, text=True, timeout=120
    )

def test_bootstrap_install_failure(mock_input, mock_subprocess, mock_console):
    """
    Scenario: No CLIs found. All 3 shown in table. User selects Claude (1),
    says yes to install. Install fails.
    Expect: Empty result with failure message.
    """
    mock_input.side_effect = ["1", "y"]  # Select Claude, then yes to install

    mock_subprocess.return_value.returncode = 1
    mock_subprocess.return_value.stderr = "Permission denied"

    with mock.patch("pdd.cli_detector._find_cli_binary", return_value=None), \
         mock.patch("pdd.cli_detector._npm_available", return_value=True):
        result = detect_and_bootstrap_cli()

    assert result.cli_name == ""
    all_printed = " ".join(str(c) for c in mock_console.print.call_args_list)
    assert "Installation failed" in all_printed

# ---------------------------------------------------------------------------
# detect_cli_tools Tests (Bootstrap Perspective)
# ---------------------------------------------------------------------------

def test_detect_cli_tools_reporting(mock_which, mock_env, mock_console):
    """Test legacy detection reporting."""
    # Claude found, others missing
    mock_which.side_effect = lambda x: "/bin/claude" if x == "claude" else None
    mock_env["ANTHROPIC_API_KEY"] = "sk-test"
    
    detect_cli_tools()
    
    # The code now uses display_name, so we adjust expectations
    mock_console.print.assert_any_call("  [green]✓[/green] Claude CLI — Found at /bin/claude")
    mock_console.print.assert_any_call("    [green]✓[/green] ANTHROPIC_API_KEY is set")
    mock_console.print.assert_any_call("  [red]✗[/red] Codex CLI — Not found")

def test_detect_cli_tools_offer_install(mock_which, mock_env, mock_input, mock_subprocess, mock_console):
    """Test legacy install offer when key exists but CLI missing."""
    # Codex missing, but key present
    mock_which.side_effect = lambda x: "/bin/npm" if x == "npm" else None
    mock_env["OPENAI_API_KEY"] = "sk-openai"
    
    # User says yes to install
    mock_input.return_value = "y"
    mock_subprocess.return_value.returncode = 0
    
    detect_cli_tools()
    
    # The code now uses display_name, so we adjust expectations
    mock_console.print.assert_any_call("    [yellow]You have OPENAI_API_KEY set but Codex CLI is not installed.[/yellow]")
    mock_subprocess.assert_called_with(
        "npm install -g @openai/codex",
        shell=True, capture_output=True, text=True, timeout=120
    )
