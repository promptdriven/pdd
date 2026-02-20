"""Tests for pdd/provider_manager.py

Organized by public API function. Tests verify user-observable behavior
through the public interface; private helpers are exercised indirectly.
Shell execution integration tests verify generated scripts actually work.
"""

import csv
import os
import subprocess
import shutil
from pathlib import Path
from unittest import mock

import pytest

from pdd.provider_manager import (
    CSV_FIELDNAMES,
    COMPLEX_AUTH_PROVIDERS,
    _save_key_to_api_env,
    _setup_complex_provider,
    add_custom_provider,
    add_provider_from_registry,
    is_multi_credential,
    parse_api_key_vars,
    remove_models_by_provider,
    remove_individual_models,
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
    monkeypatch.setenv("SHELL", "/bin/bash")
    return tmp_path


@pytest.fixture
def sample_csv(temp_home):
    """Create a sample llm_model.csv with test data."""
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
            "provider": "OpenAI",
            "model": "gpt-3.5-turbo",
            "input": "0.5",
            "output": "1.5",
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
    ]

    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=CSV_FIELDNAMES)
        writer.writeheader()
        writer.writerows(rows)

    return csv_path


@pytest.fixture
def sample_api_env(temp_home):
    """Create a sample api-env.bash file."""
    api_env_path = temp_home / ".pdd" / "api-env.bash"
    api_env_path.write_text(
        "export OPENAI_API_KEY=sk-test123\n"
        "export ANTHROPIC_API_KEY=ant-test456\n"
    )
    return api_env_path


def _read_user_csv(temp_home):
    """Read the user CSV and return list of row dicts."""
    csv_path = temp_home / ".pdd" / "llm_model.csv"
    if not csv_path.exists():
        return []
    with open(csv_path, "r", encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f))


# ---------------------------------------------------------------------------
# I. parse_api_key_vars / is_multi_credential
# ---------------------------------------------------------------------------


class TestApiKeyParsing:
    """Tests for the public utility functions parse_api_key_vars and is_multi_credential."""

    def test_parse_single_var(self):
        assert parse_api_key_vars("OPENAI_API_KEY") == ["OPENAI_API_KEY"]

    def test_parse_multiple_vars(self):
        result = parse_api_key_vars("AWS_ACCESS_KEY_ID|AWS_SECRET_ACCESS_KEY|AWS_REGION_NAME")
        assert result == ["AWS_ACCESS_KEY_ID", "AWS_SECRET_ACCESS_KEY", "AWS_REGION_NAME"]

    def test_parse_empty_and_none(self):
        assert parse_api_key_vars("") == []
        assert parse_api_key_vars(None) == []
        assert parse_api_key_vars("   ") == []

    def test_parse_strips_whitespace_and_filters_empty(self):
        assert parse_api_key_vars(" KEY_A | KEY_B ") == ["KEY_A", "KEY_B"]
        assert parse_api_key_vars("KEY_A||KEY_B") == ["KEY_A", "KEY_B"]

    def test_is_multi_credential(self):
        assert is_multi_credential("A|B") is True
        assert is_multi_credential("OPENAI_API_KEY") is False
        assert is_multi_credential("") is False
        assert is_multi_credential(None) is False


# ---------------------------------------------------------------------------
# II. add_provider_from_registry
# ---------------------------------------------------------------------------


class TestAddProviderFromRegistry:
    """Tests for add_provider_from_registry — the main provider browsing flow."""

    def test_returns_false_on_empty_ref_csv(self, temp_home):
        """Should return False when reference CSV has no models."""
        with mock.patch("pdd.provider_manager._read_csv", return_value=[]):
            with mock.patch("pdd.provider_manager.console"):
                assert add_provider_from_registry() is False

    def test_returns_false_on_cancel(self, temp_home):
        """Empty input should cancel the flow."""
        ref_rows = [
            {"provider": "Anthropic", "model": "claude", "api_key": "ANTHROPIC_API_KEY"},
        ]
        with mock.patch("pdd.provider_manager._read_csv", return_value=ref_rows):
            with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
                mock_prompt.ask.return_value = ""
                with mock.patch("pdd.provider_manager.console"):
                    assert add_provider_from_registry() is False

    @pytest.mark.parametrize("bad_input", ["99", "0", "abc", "-1"])
    def test_returns_false_on_invalid_selection(self, temp_home, bad_input):
        """Out-of-range or non-numeric input should return False."""
        ref_rows = [
            {"provider": "Anthropic", "model": "claude", "api_key": "ANTHROPIC_API_KEY"},
        ]
        with mock.patch("pdd.provider_manager._read_csv", return_value=ref_rows):
            with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
                mock_prompt.ask.return_value = bad_input
                with mock.patch("pdd.provider_manager.console"):
                    assert add_provider_from_registry() is False

    def test_adds_models_to_csv(self, temp_home, monkeypatch):
        """Should add all models for the selected provider to user CSV."""
        monkeypatch.setenv("SHELL", "/bin/bash")

        ref_rows = [
            {"provider": "Anthropic", "model": "claude-sonnet", "api_key": "ANTHROPIC_API_KEY",
             "input": "3.0", "output": "15.0", "coding_arena_elo": "1400", "base_url": "",
             "max_reasoning_tokens": "0", "structured_output": "True", "reasoning_type": "", "location": ""},
            {"provider": "Anthropic", "model": "claude-opus", "api_key": "ANTHROPIC_API_KEY",
             "input": "5.0", "output": "25.0", "coding_arena_elo": "1500", "base_url": "",
             "max_reasoning_tokens": "0", "structured_output": "True", "reasoning_type": "", "location": ""},
            {"provider": "OpenAI", "model": "gpt-4", "api_key": "OPENAI_API_KEY",
             "input": "30.0", "output": "60.0", "coding_arena_elo": "1300", "base_url": "",
             "max_reasoning_tokens": "0", "structured_output": "True", "reasoning_type": "", "location": ""},
        ]

        with mock.patch("pdd.provider_manager._read_csv", side_effect=[ref_rows, []]):
            with mock.patch("pdd.provider_manager._write_csv_atomic") as mock_write:
                with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
                    mock_prompt.ask.side_effect = ["1", "test-api-key"]
                    with mock.patch("pdd.provider_manager.Confirm") as mock_confirm:
                        mock_confirm.ask.return_value = False
                        with mock.patch("pdd.provider_manager.console"):
                            with mock.patch("pdd.provider_manager._is_key_set", return_value=None):
                                result = add_provider_from_registry()

        assert result is True
        mock_write.assert_called_once()
        written_rows = mock_write.call_args[0][1]
        assert len(written_rows) == 2
        assert all(r["provider"] == "Anthropic" for r in written_rows)

    def test_skips_duplicate_models(self, temp_home, monkeypatch):
        """Should not add models that already exist in user CSV."""
        monkeypatch.setenv("SHELL", "/bin/bash")

        ref_rows = [
            {"provider": "Anthropic", "model": "claude-sonnet", "api_key": "ANTHROPIC_API_KEY",
             "input": "3.0", "output": "15.0", "coding_arena_elo": "1400", "base_url": "",
             "max_reasoning_tokens": "0", "structured_output": "True", "reasoning_type": "", "location": ""},
        ]
        existing_rows = [
            {"provider": "Anthropic", "model": "claude-sonnet", "api_key": "ANTHROPIC_API_KEY"},
        ]

        with mock.patch("pdd.provider_manager._read_csv", side_effect=[ref_rows, existing_rows]):
            with mock.patch("pdd.provider_manager._write_csv_atomic") as mock_write:
                with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
                    mock_prompt.ask.return_value = "1"
                    with mock.patch("pdd.provider_manager.console"):
                        with mock.patch("pdd.provider_manager._is_key_set", return_value="shell environment"):
                            with mock.patch("pdd.provider_manager.Confirm") as mock_confirm:
                                mock_confirm.ask.return_value = False
                                result = add_provider_from_registry()

        assert result is False
        mock_write.assert_not_called()

    def test_dispatches_to_complex_auth_for_vertex(self, temp_home):
        """Selecting a complex provider should delegate to _setup_complex_provider."""
        with mock.patch("pdd.provider_manager._setup_complex_provider", return_value=True) as mock_setup:
            with mock.patch("pdd.provider_manager._write_csv_atomic"):
                with mock.patch("pdd.provider_manager._read_csv") as mock_read:
                    mock_read.side_effect = [
                        [{"provider": "Google Vertex AI", "model": "vertex_ai/gemini-2.5-pro",
                          "api_key": "GOOGLE_APPLICATION_CREDENTIALS", "base_url": ""}],
                        [],
                    ]
                    with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
                        mock_prompt.ask.return_value = "1"
                        with mock.patch("pdd.provider_manager.console"):
                            add_provider_from_registry()

        mock_setup.assert_called_once_with("Google Vertex AI")


# ---------------------------------------------------------------------------
# III. add_custom_provider
# ---------------------------------------------------------------------------


class TestAddCustomProvider:
    """Tests for add_custom_provider — the manual provider entry flow."""

    @mock.patch("pdd.provider_manager._ensure_api_env_sourced_in_rc")
    @mock.patch("pdd.provider_manager._save_key_to_api_env")
    @mock.patch("pdd.provider_manager._write_csv_atomic")
    @mock.patch("pdd.provider_manager._read_csv", return_value=[])
    @mock.patch("pdd.provider_manager.Confirm")
    @mock.patch("pdd.provider_manager.Prompt")
    @mock.patch("pdd.provider_manager.console")
    def test_adds_custom_model_with_correct_format(
        self, mock_console, mock_prompt, mock_confirm, mock_read, mock_write, mock_save, mock_rc
    ):
        """Should create provider/model formatted model name and sensible defaults."""
        mock_prompt.ask.side_effect = [
            "ollama", "llama3", "OLLAMA_API_KEY", "", "0.0", "0.0",
        ]
        mock_confirm.ask.return_value = False

        assert add_custom_provider() is True

        written_rows = mock_write.call_args[0][1]
        assert len(written_rows) == 1
        assert written_rows[0]["model"] == "ollama/llama3"
        assert written_rows[0]["provider"] == "ollama"
        assert written_rows[0]["api_key"] == "OLLAMA_API_KEY"
        assert written_rows[0]["coding_arena_elo"] == "1000"
        assert written_rows[0]["structured_output"] == "True"

    @pytest.mark.parametrize("abort_at_step,inputs", [
        ("provider", [""]),
        ("model", ["ollama", ""]),
        ("api_key_var", ["ollama", "llama3", ""]),
    ])
    @mock.patch("pdd.provider_manager.Prompt")
    @mock.patch("pdd.provider_manager.console")
    def test_returns_false_on_empty_input_at_each_step(
        self, mock_console, mock_prompt, abort_at_step, inputs
    ):
        """Empty input at any required step should cancel."""
        mock_prompt.ask.side_effect = inputs
        assert add_custom_provider() is False

    @mock.patch("pdd.provider_manager._ensure_api_env_sourced_in_rc")
    @mock.patch("pdd.provider_manager._save_key_to_api_env")
    @mock.patch("pdd.provider_manager._write_csv_atomic")
    @mock.patch("pdd.provider_manager._read_csv", return_value=[])
    @mock.patch("pdd.provider_manager.Confirm")
    @mock.patch("pdd.provider_manager.Prompt")
    @mock.patch("pdd.provider_manager.console")
    def test_saves_api_key_when_user_provides_value(
        self, mock_console, mock_prompt, mock_confirm, mock_read, mock_write, mock_save, mock_rc
    ):
        """When user opts to provide key value, it should be saved to api-env."""
        mock_prompt.ask.side_effect = [
            "openai", "gpt-5", "MY_KEY", "", "0.0", "0.0", "sk-secret123",
        ]
        mock_confirm.ask.return_value = True

        assert add_custom_provider() is True
        mock_save.assert_called_once_with("MY_KEY", "sk-secret123")

    @mock.patch("pdd.provider_manager._ensure_api_env_sourced_in_rc")
    @mock.patch("pdd.provider_manager._save_key_to_api_env")
    @mock.patch("pdd.provider_manager._write_csv_atomic")
    @mock.patch("pdd.provider_manager._read_csv", return_value=[])
    @mock.patch("pdd.provider_manager.Confirm")
    @mock.patch("pdd.provider_manager.Prompt")
    @mock.patch("pdd.provider_manager.console")
    def test_invalid_costs_default_to_zero(
        self, mock_console, mock_prompt, mock_confirm, mock_read, mock_write, mock_save, mock_rc
    ):
        """Non-numeric cost values should default to 0.0."""
        mock_prompt.ask.side_effect = [
            "test", "model", "TEST_KEY", "", "not-a-number", "also-bad",
        ]
        mock_confirm.ask.return_value = False

        assert add_custom_provider() is True
        written_rows = mock_write.call_args[0][1]
        assert written_rows[0]["input"] == "0.0"
        assert written_rows[0]["output"] == "0.0"


# ---------------------------------------------------------------------------
# IV. remove_models_by_provider
# ---------------------------------------------------------------------------


class TestRemoveModelsByProvider:
    """Tests for remove_models_by_provider — bulk removal by api_key group."""

    def test_returns_false_when_no_models(self, temp_home):
        with mock.patch("pdd.provider_manager.console"):
            assert remove_models_by_provider() is False

    def test_returns_false_on_cancel(self, sample_csv, temp_home):
        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.return_value = ""
            with mock.patch("pdd.provider_manager.console"):
                assert remove_models_by_provider() is False

    @pytest.mark.parametrize("bad_input", ["99", "abc"])
    def test_returns_false_on_invalid_selection(self, sample_csv, temp_home, bad_input):
        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.return_value = bad_input
            with mock.patch("pdd.provider_manager.console"):
                assert remove_models_by_provider() is False

    def test_returns_false_when_user_declines_confirm(self, sample_csv, temp_home):
        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.return_value = "1"
            with mock.patch("pdd.provider_manager.Confirm") as mock_confirm:
                mock_confirm.ask.return_value = False
                with mock.patch("pdd.provider_manager.console"):
                    assert remove_models_by_provider() is False

    def test_removes_all_models_for_selected_provider(self, sample_csv, temp_home, monkeypatch):
        """Should remove all models sharing the selected api_key and comment it out."""
        monkeypatch.setenv("SHELL", "/bin/bash")

        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.return_value = "1"
            with mock.patch("pdd.provider_manager.Confirm") as mock_confirm:
                mock_confirm.ask.return_value = True
                with mock.patch("pdd.provider_manager.console"):
                    result = remove_models_by_provider()

        assert result is True
        remaining = _read_user_csv(temp_home)
        assert len(remaining) < 3


# ---------------------------------------------------------------------------
# V. remove_individual_models
# ---------------------------------------------------------------------------


class TestRemoveIndividualModels:
    """Tests for remove_individual_models — selective model removal."""

    def test_returns_false_when_no_models(self, temp_home):
        with mock.patch("pdd.provider_manager.console"):
            assert remove_individual_models() is False

    def test_returns_false_on_cancel(self, sample_csv, temp_home):
        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.return_value = ""
            with mock.patch("pdd.provider_manager.console"):
                assert remove_individual_models() is False

    def test_returns_false_on_all_invalid_numbers(self, sample_csv, temp_home):
        """All-invalid comma-separated input should result in no selections."""
        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.return_value = "99, abc, -1"
            with mock.patch("pdd.provider_manager.console"):
                assert remove_individual_models() is False

    def test_returns_false_when_user_declines_confirm(self, sample_csv, temp_home):
        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.return_value = "1"
            with mock.patch("pdd.provider_manager.Confirm") as mock_confirm:
                mock_confirm.ask.return_value = False
                with mock.patch("pdd.provider_manager.console"):
                    assert remove_individual_models() is False

    def test_removes_single_model(self, sample_csv, temp_home):
        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.return_value = "1"
            with mock.patch("pdd.provider_manager.Confirm") as mock_confirm:
                mock_confirm.ask.return_value = True
                with mock.patch("pdd.provider_manager.console"):
                    assert remove_individual_models() is True

        assert len(_read_user_csv(temp_home)) == 2

    def test_removes_multiple_comma_separated(self, sample_csv, temp_home):
        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.return_value = "1, 2"
            with mock.patch("pdd.provider_manager.Confirm") as mock_confirm:
                mock_confirm.ask.return_value = True
                with mock.patch("pdd.provider_manager.console"):
                    assert remove_individual_models() is True

        assert len(_read_user_csv(temp_home)) == 1


# ---------------------------------------------------------------------------
# VI. Complex provider auth (_setup_complex_provider)
# ---------------------------------------------------------------------------


class TestComplexProviderAuth:
    """Tests for complex (multi-variable) provider authentication flows.

    _setup_complex_provider is tested directly because it's the entry point
    for a significant user-facing flow that add_provider_from_registry delegates to.
    """

    def test_registry_contains_expected_providers(self):
        """Registry should contain the 5 known complex providers."""
        expected = {"Google Vertex AI", "AWS Bedrock", "Azure OpenAI", "Azure AI", "Github Copilot"}
        assert expected == set(COMPLEX_AUTH_PROVIDERS.keys())

    def test_simple_providers_not_in_registry(self):
        for name in ["Anthropic", "OpenAI", "DeepSeek"]:
            assert name not in COMPLEX_AUTH_PROVIDERS

    def test_registry_entries_have_required_fields(self):
        required_keys = {"env_var", "label", "required", "default", "hint"}
        for provider, configs in COMPLEX_AUTH_PROVIDERS.items():
            assert len(configs) > 0, f"{provider} has no configs"
            for cfg in configs:
                assert required_keys <= set(cfg.keys()), f"{provider} config missing keys"

    def test_unknown_provider_returns_false(self):
        assert _setup_complex_provider("Unknown Provider") is False

    @mock.patch("pdd.provider_manager._ensure_api_env_sourced_in_rc")
    @mock.patch("pdd.provider_manager._save_key_to_api_env")
    @mock.patch("pdd.provider_manager._is_key_set", return_value=None)
    @mock.patch("pdd.provider_manager.Confirm")
    @mock.patch("pdd.provider_manager.Prompt")
    @mock.patch("pdd.provider_manager.console")
    def test_bedrock_saves_all_three_vars(
        self, mock_console, mock_prompt, mock_confirm, mock_is_key, mock_save, mock_rc
    ):
        mock_prompt.ask.side_effect = ["AKIAEXAMPLE", "wJalrXSecret", "us-east-1"]

        assert _setup_complex_provider("AWS Bedrock") is True
        assert mock_save.call_count == 3
        mock_save.assert_any_call("AWS_ACCESS_KEY_ID", "AKIAEXAMPLE")
        mock_save.assert_any_call("AWS_SECRET_ACCESS_KEY", "wJalrXSecret")
        mock_save.assert_any_call("AWS_REGION_NAME", "us-east-1")
        mock_rc.assert_called_once()

    @mock.patch("pdd.provider_manager._ensure_api_env_sourced_in_rc")
    @mock.patch("pdd.provider_manager._save_key_to_api_env")
    @mock.patch("pdd.provider_manager._is_key_set", return_value=None)
    @mock.patch("pdd.provider_manager.Confirm")
    @mock.patch("pdd.provider_manager.Prompt")
    @mock.patch("pdd.provider_manager.console")
    def test_vertex_adc_skips_credentials_save(
        self, mock_console, mock_prompt, mock_confirm, mock_is_key, mock_save, mock_rc
    ):
        """When user enters 'adc' for Vertex credentials, that var should not be saved."""
        mock_prompt.ask.side_effect = ["adc", "my-project-123", "us-central1"]

        assert _setup_complex_provider("Google Vertex AI") is True
        assert mock_save.call_count == 2
        mock_save.assert_any_call("VERTEXAI_PROJECT", "my-project-123")
        mock_save.assert_any_call("VERTEXAI_LOCATION", "us-central1")

    @mock.patch("pdd.provider_manager._ensure_api_env_sourced_in_rc")
    @mock.patch("pdd.provider_manager._save_key_to_api_env")
    @mock.patch("pdd.provider_manager._is_key_set", return_value=None)
    @mock.patch("pdd.provider_manager.Confirm")
    @mock.patch("pdd.provider_manager.Prompt")
    @mock.patch("pdd.provider_manager.console")
    def test_azure_openai_saves_three_vars(
        self, mock_console, mock_prompt, mock_confirm, mock_is_key, mock_save, mock_rc
    ):
        mock_prompt.ask.side_effect = [
            "abc123key", "https://myresource.openai.azure.com/", "2024-10-21",
        ]

        assert _setup_complex_provider("Azure OpenAI") is True
        assert mock_save.call_count == 3
        mock_save.assert_any_call("AZURE_API_KEY", "abc123key")
        mock_save.assert_any_call("AZURE_API_BASE", "https://myresource.openai.azure.com/")
        mock_save.assert_any_call("AZURE_API_VERSION", "2024-10-21")

    @mock.patch("pdd.provider_manager._ensure_api_env_sourced_in_rc")
    @mock.patch("pdd.provider_manager._save_key_to_api_env")
    @mock.patch("pdd.provider_manager._is_key_set", return_value=None)
    @mock.patch("pdd.provider_manager.Confirm")
    @mock.patch("pdd.provider_manager.Prompt")
    @mock.patch("pdd.provider_manager.console")
    def test_skip_all_required_vars_returns_false(
        self, mock_console, mock_prompt, mock_confirm, mock_is_key, mock_save, mock_rc
    ):
        """Skipping all vars should return False and save nothing."""
        mock_prompt.ask.side_effect = ["", "", ""]

        assert _setup_complex_provider("AWS Bedrock") is False
        mock_save.assert_not_called()
        mock_rc.assert_not_called()

    @mock.patch("pdd.provider_manager._ensure_api_env_sourced_in_rc")
    @mock.patch("pdd.provider_manager._save_key_to_api_env")
    @mock.patch("pdd.provider_manager._is_key_set", return_value="shell environment")
    @mock.patch("pdd.provider_manager.Confirm")
    @mock.patch("pdd.provider_manager.Prompt")
    @mock.patch("pdd.provider_manager.console")
    def test_existing_key_skipped_when_update_declined(
        self, mock_console, mock_prompt, mock_confirm, mock_is_key, mock_save, mock_rc
    ):
        mock_confirm.ask.return_value = False

        assert _setup_complex_provider("Github Copilot") is False
        mock_save.assert_not_called()


# ---------------------------------------------------------------------------
# VII. Shell execution integration tests
#
# These are the most valuable tests in this file. They verify that
# _save_key_to_api_env produces scripts that real shells can source,
# and that API key values survive the shell escaping roundtrip.
# ---------------------------------------------------------------------------


def _shell_available(shell: str) -> bool:
    return shutil.which(shell) is not None


class TestShellExecution:
    """
    Integration tests that actually execute generated api-env scripts
    in real shells and verify key values are preserved exactly.
    """

    def test_bash_syntax_valid_with_special_chars(self, temp_home, monkeypatch):
        """Generated api-env script should have valid bash syntax."""
        monkeypatch.setenv("SHELL", "/bin/bash")
        _save_key_to_api_env("TEST_KEY", 'AIzaSyAbCdEf123456$var"quote\'backtick\\slash')
        env_path = temp_home / ".pdd" / "api-env.bash"

        result = subprocess.run(
            ["bash", "-n", str(env_path)],
            capture_output=True, text=True, timeout=5,
        )
        assert result.returncode == 0, (
            f"Bash syntax error: {result.stderr}\nScript:\n{env_path.read_text()}"
        )

    def test_zsh_syntax_valid_with_special_chars(self, temp_home, monkeypatch):
        if not _shell_available("zsh"):
            pytest.skip("zsh not available")
        monkeypatch.setenv("SHELL", "/bin/zsh")
        _save_key_to_api_env("TEST_KEY", 'AIzaSyAbCdEf123456$var"quote\'backtick\\slash')
        env_path = temp_home / ".pdd" / "api-env.zsh"

        result = subprocess.run(
            ["zsh", "-n", str(env_path)],
            capture_output=True, text=True, timeout=5,
        )
        assert result.returncode == 0, (
            f"Zsh syntax error: {result.stderr}\nScript:\n{env_path.read_text()}"
        )

    def test_key_value_preserved_bash(self, temp_home, monkeypatch):
        """API key should survive bash source→read roundtrip exactly."""
        monkeypatch.setenv("SHELL", "/bin/bash")
        original = 'AIzaSyAbCdEf123456$var"quote\'backtick\\slash'
        _save_key_to_api_env("TEST_KEY", original)
        env_path = temp_home / ".pdd" / "api-env.bash"

        result = subprocess.run(
            ["bash", "-c",
             f"source {env_path} && python3 -c \"import os; print(os.environ.get('TEST_KEY', ''))\""],
            capture_output=True, text=True, timeout=5,
        )
        assert result.returncode == 0, f"Source failed: {result.stderr}"
        assert result.stdout.strip() == original

    def test_key_value_preserved_zsh(self, temp_home, monkeypatch):
        if not _shell_available("zsh"):
            pytest.skip("zsh not available")
        monkeypatch.setenv("SHELL", "/bin/zsh")
        original = 'AIzaSyAbCdEf123456$var"quote\'backtick\\slash'
        _save_key_to_api_env("TEST_KEY", original)
        env_path = temp_home / ".pdd" / "api-env.zsh"

        result = subprocess.run(
            ["zsh", "-c",
             f"source {env_path} && python3 -c \"import os; print(os.environ.get('TEST_KEY', ''))\""],
            capture_output=True, text=True, timeout=5,
        )
        assert result.returncode == 0, f"Source failed: {result.stderr}"
        assert result.stdout.strip() == original

    @pytest.mark.parametrize("name,value", [
        ("dollar", "key$value"),
        ("double_quote", 'key"value'),
        ("single_quote", "key'value"),
        ("backtick", "key`value"),
        ("backslash", "key\\value"),
        ("space", "key value"),
        ("semicolon", "key;value"),
        ("ampersand", "key&value"),
        ("pipe", "key|value"),
        ("newline", "key\nvalue"),
        ("tab", "key\tvalue"),
    ])
    def test_problematic_char_preserved_bash(self, temp_home, monkeypatch, name, value):
        """Each problematic shell character should be preserved through bash roundtrip."""
        monkeypatch.setenv("SHELL", "/bin/bash")
        key_name = f"TEST_{name.upper()}"
        _save_key_to_api_env(key_name, value)
        env_path = temp_home / ".pdd" / "api-env.bash"

        syntax = subprocess.run(
            ["bash", "-n", str(env_path)],
            capture_output=True, text=True, timeout=5,
        )
        assert syntax.returncode == 0, f"Syntax error for '{name}': {syntax.stderr}"

        extract = subprocess.run(
            ["bash", "-c",
             f"source {env_path} && python3 -c \"import os; print(repr(os.environ.get('{key_name}', '')))\""],
            capture_output=True, text=True, timeout=5,
        )
        if extract.returncode == 0:
            extracted = eval(extract.stdout.strip())
            assert extracted == value, (
                f"Value corrupted for '{name}': expected {repr(value)}, got {repr(extracted)}"
            )

    def test_multiple_keys_all_preserved(self, temp_home, monkeypatch):
        """Multiple keys saved sequentially should all be preserved."""
        monkeypatch.setenv("SHELL", "/bin/bash")
        keys = {
            "OPENAI_API_KEY": "sk-test123",
            "ANTHROPIC_API_KEY": "ant-key$special",
            "GEMINI_API_KEY": 'gem"quoted\'key',
        }
        for k, v in keys.items():
            _save_key_to_api_env(k, v)

        env_path = temp_home / ".pdd" / "api-env.bash"
        for key_name, expected in keys.items():
            result = subprocess.run(
                ["bash", "-c",
                 f"source {env_path} && python3 -c \"import os; print(os.environ.get('{key_name}', ''))\""],
                capture_output=True, text=True, timeout=5,
            )
            assert result.returncode == 0
            assert result.stdout.strip() == expected

    def test_key_update_replaces_in_place(self, temp_home, monkeypatch):
        """Updating an existing key should replace it, not duplicate it."""
        monkeypatch.setenv("SHELL", "/bin/bash")
        _save_key_to_api_env("MY_KEY", "old-value")
        _save_key_to_api_env("MY_KEY", "new-value")

        env_path = temp_home / ".pdd" / "api-env.bash"
        content = env_path.read_text()
        assert content.count("MY_KEY") == 1

        result = subprocess.run(
            ["bash", "-c",
             f"source {env_path} && python3 -c \"import os; print(os.environ.get('MY_KEY', ''))\""],
            capture_output=True, text=True, timeout=5,
        )
        assert result.returncode == 0
        assert result.stdout.strip() == "new-value"

    def test_save_key_sets_os_environ_immediately(self, temp_home, monkeypatch):
        """_save_key_to_api_env should set os.environ for immediate availability."""
        monkeypatch.setenv("SHELL", "/bin/bash")
        monkeypatch.delenv("MY_IMMEDIATE_KEY", raising=False)

        _save_key_to_api_env("MY_IMMEDIATE_KEY", "test-value-abc")

        assert os.environ.get("MY_IMMEDIATE_KEY") == "test-value-abc"

    def test_commented_key_replaced_on_save(self, temp_home, monkeypatch):
        """Saving a key that was previously commented out should uncomment/replace it."""
        monkeypatch.setenv("SHELL", "/bin/bash")
        env_path = temp_home / ".pdd" / "api-env.bash"
        env_path.write_text("# export OLD_KEY=old-value\n")

        _save_key_to_api_env("OLD_KEY", "new-value")

        content = env_path.read_text()
        assert "# export OLD_KEY" not in content
        assert "new-value" in content

        result = subprocess.run(
            ["bash", "-c",
             f"source {env_path} && python3 -c \"import os; print(os.environ.get('OLD_KEY', ''))\""],
            capture_output=True, text=True, timeout=5,
        )
        assert result.returncode == 0
        assert result.stdout.strip() == "new-value"
