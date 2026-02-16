"""Tests for pdd/setup/cli_detector.py"""

import subprocess
from unittest import mock

import pytest

from pdd.setup.cli_detector import (
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
        with mock.patch("pdd.setup.cli_detector._which") as mock_which:
            mock_which.return_value = "/usr/bin/npm"
            result = _npm_available()
            mock_which.assert_called_once_with("npm")
            assert result is True

    def test_returns_false_when_npm_not_found(self):
        """Should return False when npm is not installed."""
        with mock.patch("pdd.setup.cli_detector._which", return_value=None):
            assert _npm_available() is False


# ---------------------------------------------------------------------------
# Tests for _prompt_yes_no
# ---------------------------------------------------------------------------


class TestPromptYesNo:
    """Tests for _prompt_yes_no function."""

    def test_returns_true_for_y(self):
        """Should return True for 'y' input."""
        with mock.patch("builtins.input", return_value="y"):
            assert _prompt_yes_no("Test? ") is True

    def test_returns_true_for_yes(self):
        """Should return True for 'yes' input."""
        with mock.patch("builtins.input", return_value="yes"):
            assert _prompt_yes_no("Test? ") is True

    def test_returns_true_for_Y_uppercase(self):
        """Should return True for uppercase 'Y' input."""
        with mock.patch("builtins.input", return_value="Y"):
            assert _prompt_yes_no("Test? ") is True

    def test_returns_true_for_YES_uppercase(self):
        """Should return True for uppercase 'YES' input."""
        with mock.patch("builtins.input", return_value="YES"):
            assert _prompt_yes_no("Test? ") is True

    def test_returns_false_for_n(self):
        """Should return False for 'n' input."""
        with mock.patch("builtins.input", return_value="n"):
            assert _prompt_yes_no("Test? ") is False

    def test_returns_false_for_no(self):
        """Should return False for 'no' input."""
        with mock.patch("builtins.input", return_value="no"):
            assert _prompt_yes_no("Test? ") is False

    def test_returns_false_for_empty(self):
        """Should return False for empty input (default is No)."""
        with mock.patch("builtins.input", return_value=""):
            assert _prompt_yes_no("Test? ") is False

    def test_returns_false_for_random_input(self):
        """Should return False for unrecognized input."""
        with mock.patch("builtins.input", return_value="maybe"):
            assert _prompt_yes_no("Test? ") is False

    def test_handles_eof_error(self):
        """Should return False on EOFError."""
        with mock.patch("builtins.input", side_effect=EOFError()):
            assert _prompt_yes_no("Test? ") is False

    def test_handles_keyboard_interrupt(self):
        """Should return False on KeyboardInterrupt."""
        with mock.patch("builtins.input", side_effect=KeyboardInterrupt()):
            assert _prompt_yes_no("Test? ") is False

    def test_strips_whitespace(self):
        """Should strip whitespace from input."""
        with mock.patch("builtins.input", return_value="  y  "):
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
        with mock.patch("pdd.setup.cli_detector._which", return_value=None):
            with mock.patch("pdd.setup.cli_detector._has_api_key", return_value=False):
                detect_cli_tools()

        captured = capsys.readouterr()
        assert "Agentic CLI Tool Detection" in captured.out
        assert "pdd fix, pdd change, pdd bug" in captured.out

    def test_shows_found_cli(self, capsys):
        """Should show checkmark for found CLI tools."""
        with mock.patch("pdd.setup.cli_detector._which") as mock_which:
            mock_which.side_effect = lambda cmd: "/usr/bin/claude" if cmd == "claude" else None
            with mock.patch("pdd.setup.cli_detector._has_api_key", return_value=False):
                detect_cli_tools()

        captured = capsys.readouterr()
        assert "✓" in captured.out
        assert "Claude CLI" in captured.out

    def test_shows_not_found_cli(self, capsys):
        """Should show X for missing CLI tools."""
        with mock.patch("pdd.setup.cli_detector._which", return_value=None):
            with mock.patch("pdd.setup.cli_detector._has_api_key", return_value=False):
                detect_cli_tools()

        captured = capsys.readouterr()
        assert "✗" in captured.out
        assert "Not found" in captured.out

    def test_shows_api_key_status_when_cli_found(self, capsys):
        """Should show API key status when CLI is found."""
        with mock.patch("pdd.setup.cli_detector._which", return_value="/usr/bin/claude"):
            with mock.patch("pdd.setup.cli_detector._has_api_key") as mock_has_key:
                mock_has_key.return_value = True
                detect_cli_tools()

        captured = capsys.readouterr()
        assert "set" in captured.out

    def test_warns_when_cli_found_but_no_key(self, capsys):
        """Should warn when CLI found but API key not set."""
        with mock.patch("pdd.setup.cli_detector._which", return_value="/usr/bin/claude"):
            with mock.patch("pdd.setup.cli_detector._has_api_key", return_value=False):
                detect_cli_tools()

        captured = capsys.readouterr()
        assert "not set" in captured.out
        assert "won't be usable" in captured.out

    def test_suggests_install_when_key_but_no_cli(self, capsys):
        """Should suggest installation when API key is set but CLI is missing."""
        with mock.patch("pdd.setup.cli_detector._which", return_value=None):
            with mock.patch("pdd.setup.cli_detector._has_api_key") as mock_has_key:
                # Only anthropic has key set
                mock_has_key.side_effect = lambda p: p == "anthropic"
                with mock.patch("pdd.setup.cli_detector._npm_available", return_value=False):
                    detect_cli_tools()

        captured = capsys.readouterr()
        assert "install the CLI" in captured.out

    def test_offers_installation_when_npm_available(self, capsys):
        """Should offer installation when npm is available."""
        with mock.patch("pdd.setup.cli_detector._which", return_value=None):
            with mock.patch("pdd.setup.cli_detector._has_api_key") as mock_has_key:
                mock_has_key.side_effect = lambda p: p == "anthropic"
                with mock.patch("pdd.setup.cli_detector._npm_available", return_value=True):
                    with mock.patch("pdd.setup.cli_detector._prompt_yes_no", return_value=False):
                        detect_cli_tools()

        captured = capsys.readouterr()
        assert "Install now?" in captured.out or "Install command" in captured.out

    def test_shows_npm_not_installed_message(self, capsys):
        """Should show message when npm is not installed."""
        with mock.patch("pdd.setup.cli_detector._which", return_value=None):
            with mock.patch("pdd.setup.cli_detector._has_api_key") as mock_has_key:
                mock_has_key.side_effect = lambda p: p == "anthropic"
                with mock.patch("pdd.setup.cli_detector._npm_available", return_value=False):
                    detect_cli_tools()

        captured = capsys.readouterr()
        assert "npm is not installed" in captured.out

    def test_runs_installation_on_yes(self, capsys):
        """Should run installation when user says yes."""
        with mock.patch("pdd.setup.cli_detector._which") as mock_which:
            mock_which.side_effect = [None, None, None, "/usr/bin/claude"]  # Found after install
            with mock.patch("pdd.setup.cli_detector._has_api_key") as mock_has_key:
                mock_has_key.side_effect = lambda p: p == "anthropic"
                with mock.patch("pdd.setup.cli_detector._npm_available", return_value=True):
                    with mock.patch("pdd.setup.cli_detector._prompt_yes_no", return_value=True):
                        with mock.patch("pdd.setup.cli_detector._run_install", return_value=True):
                            detect_cli_tools()

        captured = capsys.readouterr()
        assert "installed successfully" in captured.out or "completed" in captured.out

    def test_shows_failure_message_on_install_fail(self, capsys):
        """Should show failure message when installation fails."""
        with mock.patch("pdd.setup.cli_detector._which", return_value=None):
            with mock.patch("pdd.setup.cli_detector._has_api_key") as mock_has_key:
                mock_has_key.side_effect = lambda p: p == "anthropic"
                with mock.patch("pdd.setup.cli_detector._npm_available", return_value=True):
                    with mock.patch("pdd.setup.cli_detector._prompt_yes_no", return_value=True):
                        with mock.patch("pdd.setup.cli_detector._run_install", return_value=False):
                            detect_cli_tools()

        captured = capsys.readouterr()
        assert "failed" in captured.out.lower() or "manually" in captured.out.lower()

    def test_shows_skip_message_on_no(self, capsys):
        """Should show skip message when user declines installation."""
        with mock.patch("pdd.setup.cli_detector._which", return_value=None):
            with mock.patch("pdd.setup.cli_detector._has_api_key") as mock_has_key:
                mock_has_key.side_effect = lambda p: p == "anthropic"
                with mock.patch("pdd.setup.cli_detector._npm_available", return_value=True):
                    with mock.patch("pdd.setup.cli_detector._prompt_yes_no", return_value=False):
                        detect_cli_tools()

        captured = capsys.readouterr()
        assert "Skipped" in captured.out or "later" in captured.out

    def test_shows_quick_start_when_nothing_installed(self, capsys):
        """Should show quick start guide when no CLIs are installed."""
        with mock.patch("pdd.setup.cli_detector._which", return_value=None):
            with mock.patch("pdd.setup.cli_detector._has_api_key", return_value=False):
                detect_cli_tools()

        captured = capsys.readouterr()
        assert "Quick start" in captured.out or "No CLI tools found" in captured.out

    def test_shows_all_installed_message(self, capsys):
        """Should show success message when all CLIs with keys are installed."""
        with mock.patch("pdd.setup.cli_detector._which", return_value="/usr/bin/cli"):
            with mock.patch("pdd.setup.cli_detector._has_api_key", return_value=True):
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
        with mock.patch("pdd.setup.cli_detector._which", return_value=None):
            with mock.patch("pdd.setup.cli_detector._has_api_key", return_value=False):
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

        with mock.patch("pdd.setup.cli_detector._which", side_effect=mock_which):
            with mock.patch("pdd.setup.cli_detector._has_api_key", side_effect=mock_has_key):
                with mock.patch("pdd.setup.cli_detector._npm_available", return_value=False):
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
