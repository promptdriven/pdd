
import os
import pytest
from click.testing import CliRunner
from pathlib import Path
import pandas as pd

from pdd.cli import cli

@pytest.fixture
def runner():
    return CliRunner()

def test_config_command_with_env_keys(runner, tmp_path, monkeypatch):
    """
    Tests the `pdd config` command when API keys are present in the environment.
    """
    # 1. Setup: Create a temporary directory and set mock environment variables
    test_dir = tmp_path / "test_project"
    test_dir.mkdir()
    # The order of keys is important for the input simulation, so we rely on the sorted discovery
    monkeypatch.setenv("ANTHROPIC_API_KEY", "test_anthropic_key_456")
    monkeypatch.setenv("GEMINI_API_KEY", "test_gemini_key_789")
    monkeypatch.setenv("OPENAI_API_KEY", "test_openai_key_123")


    # 2. Execution: Run the `pdd config` command
    # The input 'y\nn\ny\n' corresponds to the sorted key order:
    # - Yes, use ANTHROPIC_API_KEY
    # - No, do not use GEMINI_API_KEY
    # - Yes, use OPENAI_API_KEY
    result = runner.invoke(cli, ['config', str(test_dir)], input='y\nn\ny\n')

    # 3. Verification: Check the results
    assert result.exit_code == 0, f"CLI command failed with output: {result.output}"
    assert "Successfully created configuration file" in result.output

    pdd_dir = test_dir / ".pdd"
    assert pdd_dir.exists()

    # Verify llm_model.csv
    csv_path = pdd_dir / "llm_model.csv"
    assert csv_path.exists()
    df = pd.read_csv(csv_path)
    assert "OPENAI_API_KEY" in df['api_key'].values
    assert "ANTHROPIC_API_KEY" in df['api_key'].values
    assert "GEMINI_API_KEY" not in df['api_key'].values
    assert len(df) > 0

    # Verify api-env file
    api_env_path = pdd_dir / "api-env"
    assert api_env_path.exists()
    content = api_env_path.read_text()
    assert 'export OPENAI_API_KEY="test_openai_key_123"' in content
    assert 'export ANTHROPIC_API_KEY="test_anthropic_key_456"' in content
    assert "GEMINI_API_KEY" not in content

def test_config_command_manual_entry(runner, tmp_path, monkeypatch):
    """
    Tests the `pdd config` command for manual API key entry when no keys are in the environment.
    """
    # 1. Setup: Ensure no relevant env vars are set
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)

    # 2. Execution: Run the command and simulate manual entry
    input_sequence = (
        "y\n"  # Yes, enter keys manually
        "OpenAI\n"  # Provider
        "my_manual_openai_key\n"  # Key
        "Google\n" # Provider
        "my_manual_google_key\n" # Key
        "\n"  # Finish
    )
    result = runner.invoke(cli, ['config', str(tmp_path)], input=input_sequence)

    # 3. Verification
    assert result.exit_code == 0, f"CLI command failed with output: {result.output}"
    pdd_dir = tmp_path / ".pdd"
    assert pdd_dir.exists()

    # Verify llm_model.csv
    csv_path = pdd_dir / "llm_model.csv"
    assert csv_path.exists()
    df = pd.read_csv(csv_path)
    assert "OPENAI_API_KEY" in df['api_key'].values
    assert "GEMINI_API_KEY" in df['api_key'].values
    assert len(df) > 0

    # Verify api-env file
    api_env_path = pdd_dir / "api-env"
    assert api_env_path.exists()
    content = api_env_path.read_text()
    assert 'export OPENAI_API_KEY="my_manual_openai_key"' in content
    assert 'export GEMINI_API_KEY="my_manual_google_key"' in content

def test_config_command_no_directory(runner, monkeypatch):
    """
    Tests that `pdd config` runs in the current directory when no directory is provided.
    """
    monkeypatch.setenv("OPENAI_API_KEY", "test_openai_key_123")
    
    with runner.isolated_filesystem():
        # Run config in the isolated current directory
        result = runner.invoke(cli, ['config'], input='y\n')

        assert result.exit_code == 0
        pdd_dir = Path(".pdd")
        assert pdd_dir.exists()
        assert (pdd_dir / "llm_model.csv").exists()
        assert (pdd_dir / "api-env").exists()
