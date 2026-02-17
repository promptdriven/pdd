"""Tests for pdd/provider_manager.py"""

import csv
import os
import tempfile
from pathlib import Path
from unittest import mock

import pytest

from pdd.provider_manager import (
    CSV_FIELDNAMES,
    _get_shell_name,
    _get_pdd_dir,
    _get_api_env_path,
    _get_user_csv_path,
    _read_csv,
    _write_csv_atomic,
    _read_api_env_lines,
    _write_api_env_atomic,
    _save_key_to_api_env,
    _comment_out_key_in_api_env,
    _is_key_set,
    add_provider_from_registry,
    add_custom_provider,
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


# ---------------------------------------------------------------------------
# Tests for path helpers
# ---------------------------------------------------------------------------


class TestPathHelpers:
    """Tests for path helper functions."""

    def test_get_shell_name_bash(self, monkeypatch):
        """Should detect bash shell."""
        monkeypatch.setenv("SHELL", "/bin/bash")
        assert _get_shell_name() == "bash"

    def test_get_shell_name_zsh(self, monkeypatch):
        """Should detect zsh shell."""
        monkeypatch.setenv("SHELL", "/usr/local/bin/zsh")
        assert _get_shell_name() == "zsh"

    def test_get_shell_name_fish(self, monkeypatch):
        """Should detect fish shell."""
        monkeypatch.setenv("SHELL", "/opt/homebrew/bin/fish")
        assert _get_shell_name() == "fish"

    def test_get_shell_name_defaults_to_bash(self, monkeypatch):
        """Should default to bash for unknown shells."""
        monkeypatch.setenv("SHELL", "/bin/unknown_shell")
        assert _get_shell_name() == "bash"

    def test_get_shell_name_no_shell_var(self, monkeypatch):
        """Should default to bash when SHELL not set."""
        monkeypatch.delenv("SHELL", raising=False)
        # Implementation defaults to /bin/bash when SHELL is not set
        result = _get_shell_name()
        assert result == "bash"

    def test_get_pdd_dir_creates_directory(self, tmp_path, monkeypatch):
        """Should create ~/.pdd if it doesn't exist."""
        monkeypatch.setattr(Path, "home", lambda: tmp_path)
        pdd_dir = tmp_path / ".pdd"

        # Directory shouldn't exist yet
        assert not pdd_dir.exists()

        result = _get_pdd_dir()

        assert result == pdd_dir
        assert pdd_dir.exists()

    def test_get_api_env_path(self, temp_home, monkeypatch):
        """Should return correct api-env path for shell."""
        monkeypatch.setenv("SHELL", "/bin/zsh")
        result = _get_api_env_path()
        assert result == temp_home / ".pdd" / "api-env.zsh"

    def test_get_user_csv_path(self, temp_home):
        """Should return correct user CSV path."""
        result = _get_user_csv_path()
        assert result == temp_home / ".pdd" / "llm_model.csv"


# ---------------------------------------------------------------------------
# Tests for CSV I/O helpers
# ---------------------------------------------------------------------------


class TestCsvHelpers:
    """Tests for CSV read/write functions."""

    def test_read_csv_returns_list_of_dicts(self, sample_csv):
        """Should read CSV and return list of row dictionaries."""
        result = _read_csv(sample_csv)

        assert isinstance(result, list)
        assert len(result) == 3
        assert result[0]["provider"] == "OpenAI"
        assert result[0]["model"] == "gpt-4"

    def test_read_csv_missing_file(self, temp_home):
        """Should return empty list for missing file."""
        result = _read_csv(temp_home / ".pdd" / "nonexistent.csv")
        assert result == []

    def test_write_csv_atomic_creates_file(self, temp_home):
        """Should create CSV file with correct content."""
        csv_path = temp_home / ".pdd" / "test.csv"
        rows = [
            {"provider": "Test", "model": "test-model", "input": "1.0", "output": "2.0"},
        ]

        _write_csv_atomic(csv_path, rows)

        assert csv_path.exists()
        result = _read_csv(csv_path)
        assert len(result) == 1
        assert result[0]["provider"] == "Test"

    def test_write_csv_atomic_is_atomic(self, temp_home):
        """Write should be atomic - no partial writes on failure."""
        csv_path = temp_home / ".pdd" / "test.csv"

        # Write initial content
        _write_csv_atomic(csv_path, [{"provider": "Original"}])

        # Verify temp files are cleaned up
        pdd_dir = temp_home / ".pdd"
        temp_files = list(pdd_dir.glob(".llm_model_*.tmp"))
        assert len(temp_files) == 0

    def test_write_csv_atomic_fills_missing_fields(self, temp_home):
        """Should fill missing fields with empty strings."""
        csv_path = temp_home / ".pdd" / "test.csv"
        rows = [{"provider": "Test", "model": "test-model"}]  # Missing many fields

        _write_csv_atomic(csv_path, rows)

        result = _read_csv(csv_path)
        # All CSV_FIELDNAMES should be present
        for field in CSV_FIELDNAMES:
            assert field in result[0]


# ---------------------------------------------------------------------------
# Tests for api-env file helpers
# ---------------------------------------------------------------------------


class TestApiEnvHelpers:
    """Tests for api-env file read/write functions."""

    def test_read_api_env_lines(self, sample_api_env):
        """Should read api-env file lines."""
        result = _read_api_env_lines(sample_api_env)

        assert len(result) == 2
        assert "OPENAI_API_KEY" in result[0]

    def test_read_api_env_lines_missing_file(self, temp_home):
        """Should return empty list for missing file."""
        result = _read_api_env_lines(temp_home / ".pdd" / "nonexistent")
        assert result == []

    def test_write_api_env_atomic(self, temp_home):
        """Should write api-env file atomically."""
        env_path = temp_home / ".pdd" / "api-env.bash"
        lines = ["export TEST_KEY=value\n"]

        _write_api_env_atomic(env_path, lines)

        assert env_path.exists()
        content = env_path.read_text()
        assert "TEST_KEY" in content

    def test_save_key_to_api_env_new_key(self, temp_home, monkeypatch):
        """Should add new key to api-env file."""
        monkeypatch.setenv("SHELL", "/bin/bash")
        env_path = temp_home / ".pdd" / "api-env.bash"

        _save_key_to_api_env("NEW_KEY", "new-value")

        content = env_path.read_text()
        # shlex.quote() doesn't quote simple values without special chars
        assert 'export NEW_KEY=' in content
        assert 'new-value' in content

    def test_save_key_to_api_env_updates_existing(self, sample_api_env, monkeypatch):
        """Should update existing key in api-env file."""
        monkeypatch.setenv("SHELL", "/bin/bash")

        _save_key_to_api_env("OPENAI_API_KEY", "sk-updated")

        content = sample_api_env.read_text()
        # shlex.quote() doesn't quote simple values without special chars
        assert 'export OPENAI_API_KEY=' in content
        assert 'sk-updated' in content
        # Should not have duplicate entries
        assert content.count("OPENAI_API_KEY") == 1

    def test_save_key_to_api_env_uncomments_commented_key(self, temp_home, monkeypatch):
        """Should replace commented key with new value."""
        monkeypatch.setenv("SHELL", "/bin/bash")
        env_path = temp_home / ".pdd" / "api-env.bash"
        env_path.write_text("# export OLD_KEY=old-value\n")

        _save_key_to_api_env("OLD_KEY", "new-value")

        content = env_path.read_text()
        # shlex.quote() doesn't quote simple values without special chars
        assert 'export OLD_KEY=' in content
        assert 'new-value' in content
        assert "# export OLD_KEY" not in content

    def test_save_key_with_special_characters(self, temp_home, monkeypatch):
        """Should handle API keys with special characters."""
        monkeypatch.setenv("SHELL", "/bin/bash")

        # Key with special shell characters
        special_value = 'key$with"special\'chars'
        _save_key_to_api_env("SPECIAL_KEY", special_value)

        env_path = temp_home / ".pdd" / "api-env.bash"
        content = env_path.read_text()
        assert "SPECIAL_KEY" in content

    def test_comment_out_key_in_api_env(self, sample_api_env, monkeypatch):
        """Should comment out key with date annotation."""
        monkeypatch.setenv("SHELL", "/bin/bash")

        _comment_out_key_in_api_env("OPENAI_API_KEY")

        content = sample_api_env.read_text()
        assert "# Commented out by pdd setup on" in content
        assert "# export OPENAI_API_KEY" in content

    def test_comment_out_preserves_other_keys(self, sample_api_env, monkeypatch):
        """Should preserve other keys when commenting out one."""
        monkeypatch.setenv("SHELL", "/bin/bash")

        _comment_out_key_in_api_env("OPENAI_API_KEY")

        content = sample_api_env.read_text()
        # ANTHROPIC_API_KEY should still be active
        assert "export ANTHROPIC_API_KEY=ant-test456" in content


# ---------------------------------------------------------------------------
# Tests for _is_key_set
# ---------------------------------------------------------------------------


class TestIsKeySet:
    """Tests for _is_key_set function."""

    def test_detects_key_in_shell_env(self, temp_home, monkeypatch):
        """Should detect key set in shell environment."""
        monkeypatch.setenv("TEST_KEY", "test-value")

        result = _is_key_set("TEST_KEY")

        assert result == "shell environment"

    def test_detects_key_in_api_env_file(self, sample_api_env, monkeypatch):
        """Should detect key in api-env file."""
        monkeypatch.setenv("SHELL", "/bin/bash")
        monkeypatch.delenv("OPENAI_API_KEY", raising=False)

        result = _is_key_set("OPENAI_API_KEY")

        assert "api-env.bash" in result

    def test_returns_none_when_key_not_set(self, temp_home, monkeypatch):
        """Should return None when key is not set anywhere."""
        monkeypatch.delenv("NONEXISTENT_KEY", raising=False)

        result = _is_key_set("NONEXISTENT_KEY")

        assert result is None

    def test_dotenv_priority_over_shell(self, temp_home, monkeypatch):
        """Should check .env file first."""
        monkeypatch.setenv("TEST_KEY", "shell-value")

        with mock.patch("dotenv.dotenv_values", return_value={"TEST_KEY": "dotenv-value"}):
            result = _is_key_set("TEST_KEY")

        assert result == ".env file"


# ---------------------------------------------------------------------------
# Tests for add_provider_from_registry (mocked)
# ---------------------------------------------------------------------------


class TestAddProviderFromRegistry:
    """Tests for add_provider_from_registry function."""

    def test_returns_false_when_litellm_unavailable(self, temp_home):
        """Should return False when litellm is not available."""
        with mock.patch(
            "pdd.provider_manager.is_litellm_available", return_value=False
        ):
            with mock.patch("pdd.provider_manager.console"):
                result = add_provider_from_registry()

        assert result is False

    def test_returns_false_on_empty_selection(self, temp_home):
        """Should return False when user enters empty selection."""
        with mock.patch(
            "pdd.provider_manager.is_litellm_available", return_value=True
        ):
            with mock.patch(
                "pdd.provider_manager.get_top_providers",
                return_value=[],
            ):
                with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
                    mock_prompt.ask.return_value = ""
                    with mock.patch("pdd.provider_manager.console"):
                        result = add_provider_from_registry()

        assert result is False

    def test_adds_models_to_csv(self, temp_home):
        """Should add selected models to user CSV."""
        from pdd.litellm_registry import ProviderInfo, ModelInfo

        mock_provider = ProviderInfo(
            name="test_provider",
            display_name="Test Provider",
            api_key_env_var="TEST_API_KEY",
            model_count=2,
            sample_models=["model1", "model2"],
        )

        mock_models = [
            ModelInfo(
                name="model1",
                litellm_id="test_provider/model1",
                input_cost_per_million=1.0,
                output_cost_per_million=2.0,
                supports_function_calling=True,
            ),
        ]

        with mock.patch(
            "pdd.provider_manager.is_litellm_available", return_value=True
        ):
            with mock.patch(
                "pdd.provider_manager.get_top_providers",
                return_value=[mock_provider],
            ):
                with mock.patch(
                    "pdd.provider_manager.get_models_for_provider",
                    return_value=mock_models,
                ):
                    with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
                        # Select provider 1, then model 1
                        mock_prompt.ask.side_effect = ["1", "1", "test-api-key"]

                        with mock.patch("pdd.provider_manager.Confirm") as mock_confirm:
                            mock_confirm.ask.return_value = False

                            with mock.patch("pdd.provider_manager.console"):
                                with mock.patch(
                                    "pdd.provider_manager._is_key_set",
                                    return_value=None,
                                ):
                                    result = add_provider_from_registry()

        # Check that model was added to CSV
        csv_path = temp_home / ".pdd" / "llm_model.csv"
        if csv_path.exists():
            rows = _read_csv(csv_path)
            assert any(r["model"] == "test_provider/model1" for r in rows)


# ---------------------------------------------------------------------------
# Tests for add_custom_provider (mocked)
# ---------------------------------------------------------------------------


class TestAddCustomProvider:
    """Tests for add_custom_provider function."""

    def test_returns_false_on_empty_provider(self, temp_home):
        """Should return False when provider name is empty."""
        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.return_value = ""
            with mock.patch("pdd.provider_manager.console"):
                result = add_custom_provider()

        assert result is False

    def test_adds_custom_provider_to_csv(self, temp_home):
        """Should add custom provider to user CSV."""
        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.side_effect = [
                "custom_llm",      # provider prefix
                "my-model",        # model name
                "CUSTOM_API_KEY",  # api key env var
                "",                # base url (optional)
                "1.0",             # input cost
                "2.0",             # output cost
            ]
            with mock.patch("pdd.provider_manager.Confirm") as mock_confirm:
                mock_confirm.ask.return_value = False  # Don't enter key value now
                with mock.patch("pdd.provider_manager.console"):
                    result = add_custom_provider()

        assert result is True

        # Verify CSV was updated
        csv_path = temp_home / ".pdd" / "llm_model.csv"
        rows = _read_csv(csv_path)
        assert len(rows) == 1
        assert rows[0]["provider"] == "custom_llm"
        assert rows[0]["model"] == "custom_llm/my-model"
        assert rows[0]["api_key"] == "CUSTOM_API_KEY"

    def test_saves_api_key_when_provided(self, temp_home, monkeypatch):
        """Should save API key to api-env when user provides it."""
        monkeypatch.setenv("SHELL", "/bin/bash")

        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.side_effect = [
                "custom_llm",
                "my-model",
                "CUSTOM_API_KEY",
                "",
                "0.0",
                "0.0",
                "sk-my-secret-key",  # API key value
            ]
            with mock.patch("pdd.provider_manager.Confirm") as mock_confirm:
                mock_confirm.ask.return_value = True  # Yes, enter key value
                with mock.patch("pdd.provider_manager.console"):
                    result = add_custom_provider()

        assert result is True

        # Verify api-env was updated
        env_path = temp_home / ".pdd" / "api-env.bash"
        content = env_path.read_text()
        assert "CUSTOM_API_KEY" in content


# ---------------------------------------------------------------------------
# Tests for remove_models_by_provider (mocked)
# ---------------------------------------------------------------------------


class TestRemoveModelsByProvider:
    """Tests for remove_models_by_provider function."""

    def test_returns_false_when_no_models(self, temp_home):
        """Should return False when no models configured."""
        with mock.patch("pdd.provider_manager.console"):
            result = remove_models_by_provider()

        assert result is False

    def test_returns_false_on_cancel(self, sample_csv, temp_home):
        """Should return False when user cancels."""
        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.return_value = ""  # Empty = cancel
            with mock.patch("pdd.provider_manager.console"):
                result = remove_models_by_provider()

        assert result is False

    def test_removes_all_models_for_provider(self, sample_csv, temp_home, monkeypatch):
        """Should remove all models with matching api_key."""
        monkeypatch.setenv("SHELL", "/bin/bash")

        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.return_value = "1"  # Select first provider
            with mock.patch("pdd.provider_manager.Confirm") as mock_confirm:
                mock_confirm.ask.return_value = True  # Confirm removal
                with mock.patch("pdd.provider_manager.console"):
                    result = remove_models_by_provider()

        assert result is True

        # Check that models were removed
        rows = _read_csv(sample_csv)
        # One provider should have been removed
        assert len(rows) < 3


# ---------------------------------------------------------------------------
# Tests for remove_individual_models (mocked)
# ---------------------------------------------------------------------------


class TestRemoveIndividualModels:
    """Tests for remove_individual_models function."""

    def test_returns_false_when_no_models(self, temp_home):
        """Should return False when no models configured."""
        with mock.patch("pdd.provider_manager.console"):
            result = remove_individual_models()

        assert result is False

    def test_returns_false_on_cancel(self, sample_csv, temp_home):
        """Should return False when user cancels."""
        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.return_value = ""  # Empty = cancel
            with mock.patch("pdd.provider_manager.console"):
                result = remove_individual_models()

        assert result is False

    def test_removes_selected_models(self, sample_csv, temp_home):
        """Should remove only selected models."""
        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.return_value = "1"  # Remove first model
            with mock.patch("pdd.provider_manager.Confirm") as mock_confirm:
                mock_confirm.ask.return_value = True  # Confirm
                with mock.patch("pdd.provider_manager.console"):
                    result = remove_individual_models()

        assert result is True

        # Check that one model was removed
        rows = _read_csv(sample_csv)
        assert len(rows) == 2

    def test_removes_multiple_models(self, sample_csv, temp_home):
        """Should handle comma-separated model selection."""
        with mock.patch("pdd.provider_manager.Prompt") as mock_prompt:
            mock_prompt.ask.return_value = "1, 2"  # Remove first two models
            with mock.patch("pdd.provider_manager.Confirm") as mock_confirm:
                mock_confirm.ask.return_value = True  # Confirm
                with mock.patch("pdd.provider_manager.console"):
                    result = remove_individual_models()

        assert result is True

        # Check that two models were removed
        rows = _read_csv(sample_csv)
        assert len(rows) == 1


# ---------------------------------------------------------------------------
# Edge case tests
# ---------------------------------------------------------------------------


class TestEdgeCases:
    """Test edge cases and error handling."""

    def test_csv_write_atomic_cleans_up_on_error(self, temp_home):
        """Should clean up temp file on write error."""
        csv_path = temp_home / ".pdd" / "test.csv"

        # Create a scenario where write might fail
        with mock.patch("os.fdopen", side_effect=IOError("Simulated error")):
            with pytest.raises(IOError):
                _write_csv_atomic(csv_path, [{"provider": "Test"}])

        # No temp files should remain
        temp_files = list((temp_home / ".pdd").glob(".llm_model_*.tmp"))
        assert len(temp_files) == 0

    def test_handles_special_characters_in_api_keys(self, temp_home, monkeypatch):
        """Should handle API key values with special shell characters."""
        monkeypatch.setenv("SHELL", "/bin/bash")

        # Characters that might cause issues in shell scripts
        special_values = [
            'key$with$dollars',
            'key"with"quotes',
            "key'with'single",
            'key`with`backticks',
            'key\\with\\backslashes',
            'key with spaces',
            'key;with;semicolons',
        ]

        for i, value in enumerate(special_values):
            key_name = f"SPECIAL_KEY_{i}"
            _save_key_to_api_env(key_name, value)

        env_path = temp_home / ".pdd" / "api-env.bash"
        content = env_path.read_text()

        # All keys should be present
        for i in range(len(special_values)):
            assert f"SPECIAL_KEY_{i}" in content

    def test_handles_unicode_in_model_names(self, temp_home):
        """Should handle unicode characters in model names."""
        csv_path = temp_home / ".pdd" / "llm_model.csv"
        rows = [
            {
                "provider": "Tëst",
                "model": "模型-émoji-🤖",
                "input": "1.0",
                "output": "2.0",
            }
        ]

        _write_csv_atomic(csv_path, rows)

        result = _read_csv(csv_path)
        assert result[0]["provider"] == "Tëst"
        assert "模型" in result[0]["model"]

    def test_handles_empty_csv_fields(self, temp_home):
        """Should handle rows with empty optional fields."""
        csv_path = temp_home / ".pdd" / "llm_model.csv"
        rows = [
            {
                "provider": "Test",
                "model": "test-model",
                # All other fields will be filled with empty strings
            }
        ]

        _write_csv_atomic(csv_path, rows)

        result = _read_csv(csv_path)
        assert result[0]["provider"] == "Test"
        assert result[0]["api_key"] == ""

    def test_concurrent_writes_safe(self, temp_home):
        """Atomic writes should be safe for concurrent access."""
        csv_path = temp_home / ".pdd" / "llm_model.csv"

        # Write initial data
        _write_csv_atomic(csv_path, [{"provider": "Initial"}])

        # Simulate concurrent write
        _write_csv_atomic(csv_path, [{"provider": "Updated"}])

        result = _read_csv(csv_path)
        assert len(result) == 1
        assert result[0]["provider"] == "Updated"


# ---------------------------------------------------------------------------
# Shell script execution tests (following test_setup_tool.py pattern)
# ---------------------------------------------------------------------------


class TestApiEnvShellExecution:
    """
    Tests that verify generated api-env scripts can be sourced and
    correctly preserve API key values, especially with special characters.

    These tests follow the rigorous pattern from test_setup_tool.py,
    actually executing shell scripts to verify correctness.
    """

    def _shell_available(self, shell: str) -> bool:
        """Check if a shell is available on the system."""
        import shutil
        return shutil.which(shell) is not None

    def test_api_env_script_valid_bash_syntax(self, temp_home, monkeypatch):
        """
        Generated api-env script should have valid bash syntax.
        This test catches quoting errors that would break shell parsing.
        """
        monkeypatch.setenv("SHELL", "/bin/bash")

        # Save a key with special characters
        special_key = 'AIzaSyAbCdEf123456$var"quote\'backtick\\slash'
        _save_key_to_api_env("TEST_KEY", special_key)

        env_path = temp_home / ".pdd" / "api-env.bash"

        # Run bash syntax check
        import subprocess
        result = subprocess.run(
            ["bash", "-n", str(env_path)],
            capture_output=True,
            text=True,
            timeout=5,
        )

        assert result.returncode == 0, (
            f"Generated script has bash syntax errors: {result.stderr}\n"
            f"Script content:\n{env_path.read_text()}"
        )

    def test_api_env_script_valid_zsh_syntax(self, temp_home, monkeypatch):
        """Generated api-env script should have valid zsh syntax."""
        if not self._shell_available("zsh"):
            pytest.skip("zsh not available")

        monkeypatch.setenv("SHELL", "/bin/zsh")

        special_key = 'AIzaSyAbCdEf123456$var"quote\'backtick\\slash'
        _save_key_to_api_env("TEST_KEY", special_key)

        env_path = temp_home / ".pdd" / "api-env.zsh"

        import subprocess
        result = subprocess.run(
            ["zsh", "-n", str(env_path)],
            capture_output=True,
            text=True,
            timeout=5,
        )

        assert result.returncode == 0, (
            f"Generated script has zsh syntax errors: {result.stderr}\n"
            f"Script content:\n{env_path.read_text()}"
        )

    def test_api_env_script_can_be_sourced_bash(self, temp_home, monkeypatch):
        """Script should be sourceable in bash without errors."""
        monkeypatch.setenv("SHELL", "/bin/bash")

        special_key = 'key"with\'many$special`characters'
        _save_key_to_api_env("TEST_KEY", special_key)

        env_path = temp_home / ".pdd" / "api-env.bash"

        import subprocess
        result = subprocess.run(
            ["bash", "-c", f"source {env_path} && exit 0"],
            capture_output=True,
            text=True,
            timeout=5,
        )

        assert result.returncode == 0, (
            f"Cannot source script in bash: {result.stderr}\n"
            f"Script content:\n{env_path.read_text()}"
        )

    def test_api_env_preserves_key_value_bash(self, temp_home, monkeypatch):
        """
        API key value should be preserved exactly when script is sourced.
        This is the critical test - verifies the key survives shell escaping.
        """
        monkeypatch.setenv("SHELL", "/bin/bash")

        original_key = 'AIzaSyAbCdEf123456$var"quote\'backtick\\slash'
        _save_key_to_api_env("TEST_KEY", original_key)

        env_path = temp_home / ".pdd" / "api-env.bash"

        import subprocess
        result = subprocess.run(
            [
                "bash", "-c",
                f"source {env_path} && python3 -c \"import os; print(os.environ.get('TEST_KEY', ''))\""
            ],
            capture_output=True,
            text=True,
            timeout=5,
        )

        assert result.returncode == 0, (
            f"Failed to source script and read env var: {result.stderr}\n"
            f"Script content:\n{env_path.read_text()}"
        )

        extracted_key = result.stdout.strip()
        assert extracted_key == original_key, (
            f"Key value was corrupted during shell escaping.\n"
            f"Original:  {repr(original_key)}\n"
            f"Extracted: {repr(extracted_key)}\n"
            f"Script content:\n{env_path.read_text()}"
        )

    def test_api_env_preserves_key_value_zsh(self, temp_home, monkeypatch):
        """API key value should be preserved exactly in zsh."""
        if not self._shell_available("zsh"):
            pytest.skip("zsh not available")

        monkeypatch.setenv("SHELL", "/bin/zsh")

        original_key = 'AIzaSyAbCdEf123456$var"quote\'backtick\\slash'
        _save_key_to_api_env("TEST_KEY", original_key)

        env_path = temp_home / ".pdd" / "api-env.zsh"

        import subprocess
        result = subprocess.run(
            [
                "zsh", "-c",
                f"source {env_path} && python3 -c \"import os; print(os.environ.get('TEST_KEY', ''))\""
            ],
            capture_output=True,
            text=True,
            timeout=5,
        )

        assert result.returncode == 0, (
            f"Failed to source script: {result.stderr}\n"
            f"Script content:\n{env_path.read_text()}"
        )

        extracted_key = result.stdout.strip()
        assert extracted_key == original_key, (
            f"Key value was corrupted in zsh.\n"
            f"Original:  {repr(original_key)}\n"
            f"Extracted: {repr(extracted_key)}\n"
            f"Script content:\n{env_path.read_text()}"
        )

    def test_api_env_with_various_problematic_characters(self, temp_home, monkeypatch):
        """
        Test with various characters that commonly cause shell escaping issues.
        Each character tested individually to identify specific failures.
        """
        monkeypatch.setenv("SHELL", "/bin/bash")

        problematic_chars = [
            ('dollar', 'key$value'),
            ('double_quote', 'key"value'),
            ('single_quote', "key'value"),
            ('backtick', 'key`value'),
            ('backslash', 'key\\value'),
            ('space', 'key value'),
            ('semicolon', 'key;value'),
            ('ampersand', 'key&value'),
            ('pipe', 'key|value'),
            ('newline', 'key\nvalue'),
            ('tab', 'key\tvalue'),
        ]

        import subprocess

        for name, test_value in problematic_chars:
            key_name = f"TEST_{name.upper()}"
            _save_key_to_api_env(key_name, test_value)

            env_path = temp_home / ".pdd" / "api-env.bash"

            # Verify syntax is valid
            syntax_result = subprocess.run(
                ["bash", "-n", str(env_path)],
                capture_output=True,
                text=True,
                timeout=5,
            )

            assert syntax_result.returncode == 0, (
                f"Syntax error with '{name}' character: {syntax_result.stderr}\n"
                f"Script:\n{env_path.read_text()}"
            )

            # Verify value is preserved
            extract_result = subprocess.run(
                [
                    "bash", "-c",
                    f"source {env_path} && python3 -c \"import os; print(repr(os.environ.get('{key_name}', '')))\""
                ],
                capture_output=True,
                text=True,
                timeout=5,
            )

            if extract_result.returncode == 0:
                extracted = eval(extract_result.stdout.strip())
                assert extracted == test_value, (
                    f"Value corrupted for '{name}' character.\n"
                    f"Expected: {repr(test_value)}\n"
                    f"Got: {repr(extracted)}"
                )

    def test_multiple_keys_preserved(self, temp_home, monkeypatch):
        """Multiple keys should all be preserved correctly."""
        monkeypatch.setenv("SHELL", "/bin/bash")

        keys = {
            "OPENAI_API_KEY": "sk-test123",
            "ANTHROPIC_API_KEY": "ant-key$special",
            "GEMINI_API_KEY": 'gem"quoted\'key',
        }

        for key_name, key_value in keys.items():
            _save_key_to_api_env(key_name, key_value)

        env_path = temp_home / ".pdd" / "api-env.bash"

        import subprocess

        for key_name, expected_value in keys.items():
            result = subprocess.run(
                [
                    "bash", "-c",
                    f"source {env_path} && python3 -c \"import os; print(os.environ.get('{key_name}', ''))\""
                ],
                capture_output=True,
                text=True,
                timeout=5,
            )

            assert result.returncode == 0
            extracted = result.stdout.strip()
            assert extracted == expected_value, (
                f"{key_name} was corrupted.\n"
                f"Expected: {repr(expected_value)}\n"
                f"Got: {repr(extracted)}"
            )

    def test_normal_key_still_works(self, temp_home, monkeypatch):
        """Normal keys without special characters should still work."""
        monkeypatch.setenv("SHELL", "/bin/bash")

        normal_key = "sk-proj-abcdef1234567890ABCDEF"
        _save_key_to_api_env("OPENAI_API_KEY", normal_key)

        env_path = temp_home / ".pdd" / "api-env.bash"

        import subprocess
        result = subprocess.run(
            [
                "bash", "-c",
                f"source {env_path} && echo $OPENAI_API_KEY"
            ],
            capture_output=True,
            text=True,
            timeout=5,
        )

        assert result.returncode == 0
        assert result.stdout.strip() == normal_key
