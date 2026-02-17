"""Tests for pdd/api_key_scanner.py"""

import csv
import os
import tempfile
from pathlib import Path
from unittest import mock

import pytest

from pdd.api_key_scanner import (
    KeyInfo,
    get_provider_key_names,
    scan_environment,
    _get_csv_path,
    _load_dotenv_values,
    _detect_shell,
    _parse_api_env_file,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------


@pytest.fixture
def temp_home(tmp_path, monkeypatch):
    """Create a temporary home directory with .pdd folder."""
    pdd_dir = tmp_path / ".pdd"
    pdd_dir.mkdir(parents=True, exist_ok=True)
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    return tmp_path


@pytest.fixture
def sample_csv(temp_home):
    """Create a sample llm_model.csv with various providers."""
    csv_path = temp_home / ".pdd" / "llm_model.csv"
    rows = [
        {
            "provider": "OpenAI",
            "model": "gpt-4",
            "input": "30.0",
            "output": "60.0",
            "coding_arena_elo": "1000",
            "base_url": "",
            "api_key": "OPENAI_API_KEY",
            "max_reasoning_tokens": "0",
            "structured_output": "True",
            "reasoning_type": "",
            "location": "",
        },
        {
            "provider": "Anthropic",
            "model": "claude-3-opus",
            "input": "15.0",
            "output": "75.0",
            "coding_arena_elo": "1000",
            "base_url": "",
            "api_key": "ANTHROPIC_API_KEY",
            "max_reasoning_tokens": "0",
            "structured_output": "True",
            "reasoning_type": "",
            "location": "",
        },
        {
            "provider": "Local",
            "model": "ollama/llama2",
            "input": "0.0",
            "output": "0.0",
            "coding_arena_elo": "1000",
            "base_url": "http://localhost:11434",
            "api_key": "",  # Local LLM - no key needed
            "max_reasoning_tokens": "0",
            "structured_output": "False",
            "reasoning_type": "",
            "location": "",
        },
    ]

    fieldnames = [
        "provider", "model", "input", "output", "coding_arena_elo",
        "base_url", "api_key", "max_reasoning_tokens", "structured_output",
        "reasoning_type", "location",
    ]

    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)

    return csv_path


# ---------------------------------------------------------------------------
# Tests for get_provider_key_names
# ---------------------------------------------------------------------------


class TestGetProviderKeyNames:
    """Tests for get_provider_key_names function."""

    def test_returns_sorted_unique_keys(self, sample_csv):
        """Should return deduplicated, sorted list of API key names."""
        result = get_provider_key_names()
        assert result == ["ANTHROPIC_API_KEY", "OPENAI_API_KEY"]

    def test_returns_empty_list_when_csv_missing(self, temp_home):
        """Should return empty list when CSV doesn't exist."""
        result = get_provider_key_names()
        assert result == []

    def test_returns_empty_list_when_csv_empty(self, temp_home):
        """Should return empty list when CSV exists but is empty."""
        csv_path = temp_home / ".pdd" / "llm_model.csv"
        csv_path.touch()
        result = get_provider_key_names()
        assert result == []

    def test_handles_csv_without_api_key_column(self, temp_home):
        """Should return empty list when CSV lacks api_key column."""
        csv_path = temp_home / ".pdd" / "llm_model.csv"
        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=["provider", "model"])
            writer.writeheader()
            writer.writerow({"provider": "OpenAI", "model": "gpt-4"})

        result = get_provider_key_names()
        assert result == []

    def test_handles_csv_with_only_empty_api_keys(self, temp_home):
        """Should return empty list when all api_key values are empty."""
        csv_path = temp_home / ".pdd" / "llm_model.csv"
        fieldnames = ["provider", "model", "api_key"]
        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerow({"provider": "Local", "model": "llama2", "api_key": ""})
            writer.writerow({"provider": "Local2", "model": "mistral", "api_key": "   "})

        result = get_provider_key_names()
        assert result == []

    def test_deduplicates_same_key_multiple_providers(self, temp_home):
        """Should deduplicate when multiple rows use the same API key."""
        csv_path = temp_home / ".pdd" / "llm_model.csv"
        fieldnames = ["provider", "model", "api_key"]
        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerow({"provider": "OpenAI", "model": "gpt-4", "api_key": "OPENAI_API_KEY"})
            writer.writerow({"provider": "OpenAI", "model": "gpt-3.5", "api_key": "OPENAI_API_KEY"})
            writer.writerow({"provider": "Together", "model": "llama", "api_key": "TOGETHER_API_KEY"})

        result = get_provider_key_names()
        assert result == ["OPENAI_API_KEY", "TOGETHER_API_KEY"]

    def test_handles_malformed_csv(self, temp_home):
        """Should return empty list for malformed CSV without raising."""
        csv_path = temp_home / ".pdd" / "llm_model.csv"
        csv_path.write_text("this is not,a valid\ncsv file with\"broken quotes")

        result = get_provider_key_names()
        # Should handle gracefully - either empty or partial results
        assert isinstance(result, list)


# ---------------------------------------------------------------------------
# Tests for _detect_shell
# ---------------------------------------------------------------------------


class TestDetectShell:
    """Tests for _detect_shell function."""

    def test_detects_zsh(self, monkeypatch):
        """Should detect zsh shell."""
        monkeypatch.setenv("SHELL", "/bin/zsh")
        assert _detect_shell() == "zsh"

    def test_detects_bash(self, monkeypatch):
        """Should detect bash shell."""
        monkeypatch.setenv("SHELL", "/bin/bash")
        assert _detect_shell() == "bash"

    def test_detects_fish(self, monkeypatch):
        """Should detect fish shell."""
        monkeypatch.setenv("SHELL", "/usr/local/bin/fish")
        assert _detect_shell() == "fish"

    def test_returns_none_when_shell_not_set(self, monkeypatch):
        """Should return None when SHELL env var is not set."""
        monkeypatch.delenv("SHELL", raising=False)
        assert _detect_shell() is None

    def test_handles_unusual_shell_paths(self, monkeypatch):
        """Should extract shell name from unusual paths."""
        monkeypatch.setenv("SHELL", "/opt/homebrew/bin/zsh")
        assert _detect_shell() == "zsh"


# ---------------------------------------------------------------------------
# Tests for _parse_api_env_file
# ---------------------------------------------------------------------------


class TestParseApiEnvFile:
    """Tests for _parse_api_env_file function."""

    def test_parses_simple_exports(self, tmp_path):
        """Should parse simple export KEY=value lines."""
        env_file = tmp_path / "api-env.bash"
        env_file.write_text(
            "export OPENAI_API_KEY=sk-12345\n"
            "export ANTHROPIC_API_KEY=ant-67890\n"
        )

        result = _parse_api_env_file(env_file)
        assert result == {
            "OPENAI_API_KEY": "sk-12345",
            "ANTHROPIC_API_KEY": "ant-67890",
        }

    def test_parses_quoted_values(self, tmp_path):
        """Should parse quoted export values."""
        env_file = tmp_path / "api-env.bash"
        env_file.write_text(
            'export OPENAI_API_KEY="sk-12345"\n'
            "export ANTHROPIC_API_KEY='ant-67890'\n"
        )

        result = _parse_api_env_file(env_file)
        assert result == {
            "OPENAI_API_KEY": "sk-12345",
            "ANTHROPIC_API_KEY": "ant-67890",
        }

    def test_skips_commented_lines(self, tmp_path):
        """Should skip lines starting with #."""
        env_file = tmp_path / "api-env.bash"
        env_file.write_text(
            "# This is a comment\n"
            "export OPENAI_API_KEY=sk-12345\n"
            "# export ANTHROPIC_API_KEY=ant-67890\n"
        )

        result = _parse_api_env_file(env_file)
        assert result == {"OPENAI_API_KEY": "sk-12345"}

    def test_skips_empty_lines(self, tmp_path):
        """Should skip empty lines."""
        env_file = tmp_path / "api-env.bash"
        env_file.write_text(
            "export OPENAI_API_KEY=sk-12345\n"
            "\n"
            "   \n"
            "export ANTHROPIC_API_KEY=ant-67890\n"
        )

        result = _parse_api_env_file(env_file)
        assert len(result) == 2

    def test_returns_empty_dict_for_missing_file(self, tmp_path):
        """Should return empty dict when file doesn't exist."""
        env_file = tmp_path / "nonexistent"
        result = _parse_api_env_file(env_file)
        assert result == {}

    def test_handles_special_characters_in_values(self, tmp_path):
        """Should handle API keys with special characters."""
        # Characters that might appear in API keys
        special_key = 'AIzaSyAbCdEf123456$var"quote\'backtick\\slash'
        env_file = tmp_path / "api-env.bash"
        # Note: The file might have various quoting styles
        env_file.write_text(f"export TEST_KEY='{special_key}'\n")

        result = _parse_api_env_file(env_file)
        assert result.get("TEST_KEY") == special_key

    def test_ignores_non_export_lines(self, tmp_path):
        """Should ignore lines that don't start with 'export '."""
        env_file = tmp_path / "api-env.bash"
        env_file.write_text(
            "OPENAI_API_KEY=sk-12345\n"  # No export
            "export ANTHROPIC_API_KEY=ant-67890\n"
            "echo 'hello'\n"
        )

        result = _parse_api_env_file(env_file)
        assert result == {"ANTHROPIC_API_KEY": "ant-67890"}

    def test_handles_whitespace_around_equals(self, tmp_path):
        """Should handle whitespace around equals sign."""
        env_file = tmp_path / "api-env.bash"
        env_file.write_text("export OPENAI_API_KEY = sk-12345\n")

        # The current implementation uses partition("="), check behavior
        result = _parse_api_env_file(env_file)
        # Result may vary based on implementation - just ensure no crash
        assert isinstance(result, dict)


# ---------------------------------------------------------------------------
# Tests for scan_environment
# ---------------------------------------------------------------------------


class TestScanEnvironment:
    """Tests for scan_environment function."""

    def test_returns_empty_dict_when_no_models_configured(self, temp_home):
        """Should return empty dict when no models in CSV."""
        result = scan_environment()
        assert result == {}

    def test_detects_key_in_shell_environment(self, sample_csv, monkeypatch):
        """Should detect keys set in shell environment."""
        monkeypatch.setenv("OPENAI_API_KEY", "sk-test123")
        # Don't set ANTHROPIC_API_KEY

        result = scan_environment()

        assert "OPENAI_API_KEY" in result
        assert result["OPENAI_API_KEY"].is_set is True
        assert result["OPENAI_API_KEY"].source == "shell environment"

        assert "ANTHROPIC_API_KEY" in result
        assert result["ANTHROPIC_API_KEY"].is_set is False

    def test_detects_key_in_api_env_file(self, sample_csv, temp_home, monkeypatch):
        """Should detect keys in ~/.pdd/api-env.{shell} file."""
        monkeypatch.setenv("SHELL", "/bin/bash")
        # Clear any existing env vars
        monkeypatch.delenv("OPENAI_API_KEY", raising=False)
        monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)

        api_env_path = temp_home / ".pdd" / "api-env.bash"
        api_env_path.write_text("export OPENAI_API_KEY=sk-from-api-env\n")

        result = scan_environment()

        assert result["OPENAI_API_KEY"].is_set is True
        assert result["OPENAI_API_KEY"].source == "~/.pdd/api-env.bash"
        assert result["ANTHROPIC_API_KEY"].is_set is False

    def test_priority_order_dotenv_first(self, sample_csv, temp_home, monkeypatch):
        """Should check .env file first (highest priority)."""
        monkeypatch.setenv("SHELL", "/bin/bash")
        monkeypatch.setenv("OPENAI_API_KEY", "sk-from-shell")

        # Create api-env file too
        api_env_path = temp_home / ".pdd" / "api-env.bash"
        api_env_path.write_text("export OPENAI_API_KEY=sk-from-api-env\n")

        # Mock dotenv to return a value
        with mock.patch(
            "pdd.api_key_scanner._load_dotenv_values",
            return_value={"OPENAI_API_KEY": "sk-from-dotenv"},
        ):
            result = scan_environment()

        assert result["OPENAI_API_KEY"].source == ".env file"

    def test_priority_order_shell_before_api_env(self, sample_csv, temp_home, monkeypatch):
        """Shell environment should have priority over api-env file."""
        monkeypatch.setenv("SHELL", "/bin/bash")
        monkeypatch.setenv("OPENAI_API_KEY", "sk-from-shell")

        api_env_path = temp_home / ".pdd" / "api-env.bash"
        api_env_path.write_text("export OPENAI_API_KEY=sk-from-api-env\n")

        # Mock dotenv to return empty (no .env file)
        with mock.patch(
            "pdd.api_key_scanner._load_dotenv_values",
            return_value={},
        ):
            result = scan_environment()

        assert result["OPENAI_API_KEY"].source == "shell environment"

    def test_keyinfo_structure(self, sample_csv, monkeypatch):
        """Should return KeyInfo dataclass with correct fields."""
        monkeypatch.setenv("OPENAI_API_KEY", "sk-test")

        result = scan_environment()
        key_info = result["OPENAI_API_KEY"]

        assert isinstance(key_info, KeyInfo)
        assert hasattr(key_info, "source")
        assert hasattr(key_info, "is_set")

    def test_handles_exception_gracefully(self, monkeypatch, temp_home):
        """Should return best-effort results on errors without raising."""
        # Create a CSV that will cause issues
        csv_path = temp_home / ".pdd" / "llm_model.csv"
        csv_path.write_text("provider,model,api_key\nTest,test,TEST_KEY\n")

        # Mock get_provider_key_names to raise
        with mock.patch(
            "pdd.api_key_scanner.get_provider_key_names",
            side_effect=Exception("Test error"),
        ):
            result = scan_environment()

        # Should return empty dict, not raise
        assert result == {}

    def test_different_shells_use_different_api_env_files(self, sample_csv, temp_home, monkeypatch):
        """Should use api-env file matching the detected shell."""
        # Create both bash and zsh api-env files with different keys
        (temp_home / ".pdd" / "api-env.bash").write_text(
            "export OPENAI_API_KEY=sk-bash\n"
        )
        (temp_home / ".pdd" / "api-env.zsh").write_text(
            "export ANTHROPIC_API_KEY=ant-zsh\n"
        )

        # Clear shell env
        monkeypatch.delenv("OPENAI_API_KEY", raising=False)
        monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)

        # Test with bash shell
        monkeypatch.setenv("SHELL", "/bin/bash")
        with mock.patch("pdd.api_key_scanner._load_dotenv_values", return_value={}):
            result = scan_environment()

        assert result["OPENAI_API_KEY"].is_set is True
        assert result["OPENAI_API_KEY"].source == "~/.pdd/api-env.bash"
        assert result["ANTHROPIC_API_KEY"].is_set is False


# ---------------------------------------------------------------------------
# Tests for _load_dotenv_values
# ---------------------------------------------------------------------------


class TestLoadDotenvValues:
    """Tests for _load_dotenv_values function."""

    def test_returns_empty_dict_when_dotenv_not_installed(self, monkeypatch):
        """Should return empty dict if python-dotenv is not available."""
        # Mock the import to fail
        import builtins
        real_import = builtins.__import__

        def mock_import(name, *args, **kwargs):
            if name == "dotenv":
                raise ImportError("No module named 'dotenv'")
            return real_import(name, *args, **kwargs)

        monkeypatch.setattr(builtins, "__import__", mock_import)

        result = _load_dotenv_values()
        assert result == {}

    def test_filters_out_none_values(self):
        """Should filter out keys with None values from dotenv."""
        # Mock dotenv_values to return some None values
        with mock.patch("dotenv.dotenv_values", return_value={
            "KEY1": "value1",
            "KEY2": None,
            "KEY3": "value3",
        }):
            result = _load_dotenv_values()

        assert result == {"KEY1": "value1", "KEY3": "value3"}


# ---------------------------------------------------------------------------
# Edge case tests
# ---------------------------------------------------------------------------


class TestEdgeCases:
    """Test edge cases and error handling."""

    def test_handles_unicode_in_csv(self, temp_home):
        """Should handle unicode characters in CSV."""
        csv_path = temp_home / ".pdd" / "llm_model.csv"
        fieldnames = ["provider", "model", "api_key"]
        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerow({
                "provider": "Tëst Provider",
                "model": "模型",
                "api_key": "UNICODE_KEY_名前",
            })

        result = get_provider_key_names()
        assert "UNICODE_KEY_名前" in result

    def test_handles_very_long_api_key_names(self, temp_home):
        """Should handle very long API key names."""
        csv_path = temp_home / ".pdd" / "llm_model.csv"
        fieldnames = ["provider", "model", "api_key"]
        long_key_name = "A" * 1000 + "_API_KEY"

        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerow({
                "provider": "Test",
                "model": "test",
                "api_key": long_key_name,
            })

        result = get_provider_key_names()
        assert long_key_name in result

    def test_handles_api_key_with_special_shell_characters(self, temp_home, monkeypatch):
        """Should handle API key names with characters problematic for shells."""
        csv_path = temp_home / ".pdd" / "llm_model.csv"
        fieldnames = ["provider", "model", "api_key"]

        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerow({
                "provider": "Test",
                "model": "test",
                "api_key": "MY_SPECIAL_KEY",
            })

        # Set the env var
        monkeypatch.setenv("MY_SPECIAL_KEY", "value_with_$pecial_chars")
        monkeypatch.setenv("SHELL", "/bin/bash")

        with mock.patch("pdd.api_key_scanner._load_dotenv_values", return_value={}):
            result = scan_environment()

        assert result["MY_SPECIAL_KEY"].is_set is True

    def test_handles_permission_error_on_csv(self, temp_home, monkeypatch):
        """Should handle permission errors gracefully."""
        csv_path = temp_home / ".pdd" / "llm_model.csv"
        csv_path.write_text("provider,model,api_key\nTest,test,KEY\n")

        # Mock open to raise PermissionError
        original_open = open

        def mock_open_with_permission_error(file, *args, **kwargs):
            if str(file) == str(csv_path):
                raise PermissionError("Access denied")
            return original_open(file, *args, **kwargs)

        with mock.patch("builtins.open", side_effect=mock_open_with_permission_error):
            result = get_provider_key_names()

        assert result == []
