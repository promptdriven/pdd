"""Tests for setup_tool.py — deterministic auto-configuration."""

import pytest
from unittest.mock import MagicMock, patch
from pathlib import Path

from pdd import setup_tool


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def mock_cli_result():
    result = MagicMock()
    result.cli_name = "test_cli"
    result.provider = "test_provider"
    result.api_key_configured = True
    return result


@pytest.fixture
def mock_detect_cli():
    with patch("pdd.cli_detector.detect_and_bootstrap_cli") as m:
        yield m


@pytest.fixture
def mock_auto_phase():
    with patch("pdd.setup_tool._run_auto_phase") as m:
        yield m


@pytest.fixture
def mock_fallback_menu():
    with patch("pdd.setup_tool._run_fallback_menu") as m:
        yield m


@pytest.fixture
def mock_input():
    with patch("builtins.input") as m:
        yield m


@pytest.fixture
def mock_print():
    with patch("builtins.print") as m:
        yield m


# ---------------------------------------------------------------------------
# Tests for run_setup
# ---------------------------------------------------------------------------

def test_run_setup_no_cli_detected(mock_detect_cli, mock_auto_phase, mock_print):
    """Test that setup exits early if no CLI is detected."""
    result = MagicMock()
    result.cli_name = ""
    mock_detect_cli.return_value = result

    setup_tool.run_setup()

    mock_detect_cli.assert_called_once()
    mock_auto_phase.assert_not_called()
    assert any("Agentic features require at least one CLI tool" in str(c) for c in mock_print.call_args_list)


def test_run_setup_success_path(mock_detect_cli, mock_auto_phase, mock_input, mock_print, mock_cli_result):
    """Test the happy path where auto phase succeeds."""
    mock_detect_cli.return_value = mock_cli_result
    mock_auto_phase.return_value = True

    with patch("pdd.setup_tool._console") as mock_console:
        setup_tool.run_setup()

    mock_detect_cli.assert_called_once()
    mock_auto_phase.assert_called_once()
    assert any("Setup complete" in str(c) for c in mock_console.print.call_args_list)


def test_run_setup_fallback_path(mock_detect_cli, mock_auto_phase, mock_fallback_menu, mock_input, mock_cli_result):
    """Test that fallback menu is triggered if auto phase fails."""
    mock_detect_cli.return_value = mock_cli_result
    mock_auto_phase.return_value = False

    setup_tool.run_setup()

    mock_auto_phase.assert_called_once()
    mock_fallback_menu.assert_called_once()


def test_run_setup_keyboard_interrupt(mock_detect_cli, mock_print):
    """Test handling of KeyboardInterrupt during setup."""
    mock_detect_cli.side_effect = KeyboardInterrupt

    setup_tool.run_setup()

    assert any("Setup interrupted" in str(c) for c in mock_print.call_args_list)


def test_run_setup_no_api_key_warning(mock_detect_cli, mock_auto_phase, mock_input, mock_print):
    """Test that a warning is printed if API key is not configured, but proceeds."""
    result = MagicMock()
    result.cli_name = "test_cli"
    result.api_key_configured = False
    mock_detect_cli.return_value = result
    mock_auto_phase.return_value = True

    setup_tool.run_setup()

    assert any("No API key configured" in str(c) for c in mock_print.call_args_list)
    mock_auto_phase.assert_called_once()


# ---------------------------------------------------------------------------
# Tests for _run_auto_phase
# ---------------------------------------------------------------------------

@patch("pdd.setup_tool._step4_test_and_summary")
@patch("pdd.setup_tool._step3_local_llms_and_pddrc")
@patch("pdd.setup_tool._step2_configure_models")
@patch("pdd.setup_tool._step1_scan_keys")
@patch("builtins.input")
def test_run_auto_phase_success(mock_input, mock_step1, mock_step2, mock_step3, mock_step4):
    """Test that all 4 steps run sequentially on success."""
    mock_step1.return_value = [("ANTHROPIC_API_KEY", "shell environment")]
    mock_step2.return_value = {"Anthropic": 3}
    mock_step3.return_value = {"Ollama": ["llama3.2:3b"]}

    result = setup_tool._run_auto_phase()

    assert result is True
    mock_step1.assert_called_once()
    mock_step2.assert_called_once_with([("ANTHROPIC_API_KEY", "shell environment")])
    mock_step3.assert_called_once()
    mock_step4.assert_called_once()
    # 3 "Press Enter" prompts between steps
    assert mock_input.call_count == 3


@patch("pdd.setup_tool._step1_scan_keys")
@patch("builtins.input")
def test_run_auto_phase_exception_returns_false(mock_input, mock_step1):
    """Test that exceptions in steps cause fallback."""
    mock_step1.side_effect = RuntimeError("test error")

    result = setup_tool._run_auto_phase()

    assert result is False


# ---------------------------------------------------------------------------
# Tests for _step1_scan_keys
# ---------------------------------------------------------------------------

@patch("pdd.setup_tool._prompt_for_api_key")
@patch("pdd.api_key_scanner._parse_api_env_file")
@patch("pdd.api_key_scanner._detect_shell")
@patch("pdd.litellm_registry.PROVIDER_API_KEY_MAP", {"anthropic": "ANTHROPIC_API_KEY", "openai": "OPENAI_API_KEY"})
def test_step1_finds_keys_in_env(mock_detect_shell, mock_parse, mock_prompt, tmp_path, monkeypatch):
    """Test that step 1 finds keys from os.environ."""
    monkeypatch.setenv("ANTHROPIC_API_KEY", "sk-test")
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    mock_detect_shell.return_value = "bash"
    mock_parse.return_value = {}

    found = setup_tool._step1_scan_keys()

    assert len(found) == 1
    assert found[0] == ("ANTHROPIC_API_KEY", "shell environment")
    mock_prompt.assert_not_called()


@patch("pdd.setup_tool._prompt_for_api_key")
@patch("pdd.api_key_scanner._parse_api_env_file")
@patch("pdd.api_key_scanner._detect_shell")
@patch("pdd.litellm_registry.PROVIDER_API_KEY_MAP", {"anthropic": "ANTHROPIC_API_KEY"})
def test_step1_no_keys_triggers_prompt(mock_detect_shell, mock_parse, mock_prompt, tmp_path, monkeypatch):
    """Test that step 1 prompts for a key when none found."""
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    monkeypatch.setattr(Path, "home", lambda: tmp_path)
    mock_detect_shell.return_value = "bash"
    mock_parse.return_value = {}
    mock_prompt.return_value = [("ANTHROPIC_API_KEY", "~/.pdd/api-env.bash")]

    found = setup_tool._step1_scan_keys()

    assert len(found) == 1
    mock_prompt.assert_called_once()


# ---------------------------------------------------------------------------
# Tests for _step2_configure_models
# ---------------------------------------------------------------------------

@patch("pdd.provider_manager._get_user_csv_path")
@patch("pdd.provider_manager._write_csv_atomic")
@patch("pdd.provider_manager._read_csv")
def test_step2_adds_matching_models(mock_read, mock_write, mock_csv_path, tmp_path):
    """Test that step 2 filters reference CSV by found keys and writes user CSV."""
    mock_csv_path.return_value = tmp_path / "llm_model.csv"

    # First call: reference CSV, second call: existing user CSV (empty)
    mock_read.side_effect = [
        [
            {"provider": "Anthropic", "model": "claude-sonnet", "api_key": "ANTHROPIC_API_KEY", "base_url": ""},
            {"provider": "OpenAI", "model": "gpt-4", "api_key": "OPENAI_API_KEY", "base_url": ""},
        ],
        [],  # empty user CSV
    ]

    found_keys = [("ANTHROPIC_API_KEY", "shell environment")]
    result = setup_tool._step2_configure_models(found_keys)

    assert result == {"Anthropic": 1}
    mock_write.assert_called_once()
    written_rows = mock_write.call_args[0][1]
    assert len(written_rows) == 1
    assert written_rows[0]["model"] == "claude-sonnet"


@patch("pdd.provider_manager._get_user_csv_path")
@patch("pdd.provider_manager._write_csv_atomic")
@patch("pdd.provider_manager._read_csv")
def test_step2_deduplicates_existing(mock_read, mock_write, mock_csv_path, tmp_path):
    """Test that step 2 skips models already in user CSV."""
    mock_csv_path.return_value = tmp_path / "llm_model.csv"

    mock_read.side_effect = [
        [{"provider": "Anthropic", "model": "claude-sonnet", "api_key": "ANTHROPIC_API_KEY", "base_url": ""}],
        [{"provider": "Anthropic", "model": "claude-sonnet", "api_key": "ANTHROPIC_API_KEY"}],
    ]

    found_keys = [("ANTHROPIC_API_KEY", "shell environment")]
    result = setup_tool._step2_configure_models(found_keys)

    assert result == {"Anthropic": 1}
    mock_write.assert_not_called()


@patch("pdd.provider_manager._get_user_csv_path")
@patch("pdd.provider_manager._write_csv_atomic")
@patch("pdd.provider_manager._read_csv")
def test_step2_skips_local_models(mock_read, mock_write, mock_csv_path, tmp_path):
    """Test that step 2 skips local models (ollama, lm_studio, localhost)."""
    mock_csv_path.return_value = tmp_path / "llm_model.csv"

    mock_read.side_effect = [
        [
            {"provider": "Ollama", "model": "ollama/llama", "api_key": "", "base_url": "http://localhost:11434"},
            {"provider": "lm_studio", "model": "lm/model", "api_key": "", "base_url": "http://localhost:1234"},
            {"provider": "OpenAI", "model": "gpt-local", "api_key": "OPENAI_API_KEY", "base_url": "http://localhost:8080"},
            {"provider": "Anthropic", "model": "claude", "api_key": "ANTHROPIC_API_KEY", "base_url": ""},
        ],
        [],
    ]

    found_keys = [("ANTHROPIC_API_KEY", "env"), ("OPENAI_API_KEY", "env")]
    result = setup_tool._step2_configure_models(found_keys)

    assert result == {"Anthropic": 1}


# ---------------------------------------------------------------------------
# Tests for local LLM helpers
# ---------------------------------------------------------------------------

def test_extract_ollama_models():
    """Test Ollama model name extraction from API response."""
    data = {"models": [{"name": "llama3.2:3b"}, {"name": "openhermes:latest"}, {"name": ""}]}
    result = setup_tool._extract_ollama_models(data)
    assert result == ["llama3.2:3b", "openhermes:latest"]


def test_extract_ollama_models_empty():
    """Test Ollama extraction with empty models list."""
    assert setup_tool._extract_ollama_models({"models": []}) == []
    assert setup_tool._extract_ollama_models({}) == []


def test_extract_lm_studio_models():
    """Test LM Studio model name extraction from API response."""
    data = {"data": [{"id": "model-a"}, {"id": "model-b"}, {"id": ""}]}
    result = setup_tool._extract_lm_studio_models(data)
    assert result == ["model-a", "model-b"]


def test_extract_lm_studio_models_empty():
    """Test LM Studio extraction with empty data list."""
    assert setup_tool._extract_lm_studio_models({"data": []}) == []
    assert setup_tool._extract_lm_studio_models({}) == []


# ---------------------------------------------------------------------------
# Tests for _run_fallback_menu
# ---------------------------------------------------------------------------

@patch("pdd.pddrc_initializer.offer_pddrc_init")
@patch("pdd.model_tester.test_model_interactive")
@patch("pdd.provider_manager.add_provider_from_registry")
@patch("builtins.input")
def test_run_fallback_menu_options(mock_input, mock_add_provider, mock_test_model, mock_init_pddrc):
    """Test the fallback menu loop and options."""
    mock_input.side_effect = ["1", "2", "3", "5", "4"]

    setup_tool._run_fallback_menu()

    mock_add_provider.assert_called_once()
    mock_test_model.assert_called_once()
    mock_init_pddrc.assert_called_once()
    assert mock_input.call_count == 5


@patch("builtins.input")
def test_run_fallback_menu_interrupt(mock_input, mock_print):
    """Test exiting fallback menu via KeyboardInterrupt."""
    mock_input.side_effect = KeyboardInterrupt

    setup_tool._run_fallback_menu()

    assert any("Setup interrupted" in str(c) for c in mock_print.call_args_list)


# ---------------------------------------------------------------------------
# Tests for _prompt_for_api_key
# ---------------------------------------------------------------------------

@patch("pdd.provider_manager._save_key_to_api_env")
@patch("pdd.setup_tool.getpass")
@patch("builtins.input")
def test_prompt_for_api_key_adds_key(mock_input, mock_getpass, mock_save):
    """Test that prompt flow saves a key and returns it."""
    mock_input.side_effect = [
        "1",   # Select Anthropic
        "n",   # Don't add another
    ]
    mock_getpass.getpass.return_value = "sk-test-key-123"

    result = setup_tool._prompt_for_api_key()

    assert len(result) == 1
    assert result[0][0] == "ANTHROPIC_API_KEY"
    mock_save.assert_called_once_with("ANTHROPIC_API_KEY", "sk-test-key-123")


@patch("pdd.provider_manager._save_key_to_api_env")
@patch("pdd.setup_tool.getpass")
@patch("builtins.input")
def test_prompt_for_api_key_skip(mock_input, mock_getpass, mock_save):
    """Test that skip option returns empty list."""
    skip_idx = len(setup_tool._PROMPT_PROVIDERS) + 2
    mock_input.side_effect = [str(skip_idx)]

    result = setup_tool._prompt_for_api_key()

    assert result == []
    mock_save.assert_not_called()


@patch("pdd.provider_manager._save_key_to_api_env")
@patch("pdd.setup_tool.getpass")
@patch("builtins.input")
def test_prompt_for_api_key_empty_value_skips(mock_input, mock_getpass, mock_save):
    """Test that empty key value is rejected gracefully."""
    skip_idx = len(setup_tool._PROMPT_PROVIDERS) + 2
    mock_input.side_effect = [
        "1",           # Select Anthropic
        str(skip_idx), # Skip after empty key
    ]
    mock_getpass.getpass.return_value = ""

    result = setup_tool._prompt_for_api_key()

    assert result == []
    mock_save.assert_not_called()
