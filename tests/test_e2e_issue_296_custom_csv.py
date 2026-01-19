"""
E2E Test for Issue #296: No warning when user removes base model from custom CSV

This test exercises the full CLI path from `pdd generate` down to the llm_invoke
layer to verify that when users intentionally remove the hardcoded DEFAULT_LLM_MODEL
('gpt-5.1-codex-mini') from their custom ~/.pdd/llm_model.csv, PDD does NOT log
a warning about the missing model.

The bug: When users customize their llm_model.csv by removing unwanted models
like 'gpt-5.1-codex-mini', PDD would still log a warning:
    "Base model 'gpt-5.1-codex-mini' not found in CSV. Falling back to surrogate
     base 'gemini/gemini-2.0-flash-exp' (Option A')."

This is confusing because the user intentionally removed it. The CSV should be
treated as the single source of truth.

This E2E test:
1. Sets up a temp directory with a custom llm_model.csv that excludes gpt-5.1-codex-mini
2. Runs the generate command through Click's CliRunner
3. Mocks litellm to avoid real API calls
4. Captures log output using caplog
5. Verifies that NO warning is logged about the missing base model

The test should FAIL on buggy code (warning is logged) and PASS once the fix is applied.
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
from click.testing import CliRunner
import logging
import os


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory for all tests in this module.

    This is required because construct_paths uses PDD_PATH to find the language_format.csv
    file for language detection.
    """
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


@pytest.mark.e2e
class TestCustomCSVNoWarningE2E:
    """
    E2E tests for Issue #296: Verify users who remove the hardcoded default model
    from their custom CSV do NOT see warnings about the missing model.
    """

    def test_no_warning_when_user_removes_hardcoded_base_model_e2e(
        self, tmp_path, monkeypatch, caplog
    ):
        """
        E2E Test: pdd generate with custom CSV excluding gpt-5.1-codex-mini

        This test simulates the exact scenario from issue #296:
        1. User has a custom llm_model.csv that excludes gpt-5.1-codex-mini
        2. User runs a PDD command (pdd generate)
        3. NO warning should be logged about the missing base model

        Expected behavior (after fix):
        - PDD silently uses the first available model from user's CSV
        - No warning about "Base model 'gpt-5.1-codex-mini' not found"

        Bug behavior (Issue #296):
        - PDD logs: "Base model 'gpt-5.1-codex-mini' not found in CSV. Falling back..."
        - This confuses users who intentionally removed it
        """
        # 1. Create a simple prompt file for generate command
        prompt_content = """Write a simple Python function that adds two numbers."""
        (tmp_path / "test_python.prompt").write_text(prompt_content)

        # 2. Create a custom llm_model.csv WITHOUT gpt-5.1-codex-mini
        # This simulates the user's intentional removal of unwanted models
        csv_content = """provider,model,input,output,coding_arena_elo,structured_output,base_url,api_key,max_tokens,max_completion_tokens,reasoning_type,max_reasoning_tokens
Gemini,gemini/gemini-2.0-flash-exp,0.0,0.0,1500,TRUE,,,,,none,0
OpenAI,gpt-4o-mini,0.15,0.6,1450,TRUE,,OPENAI_API_KEY,,,none,0
"""
        csv_path = tmp_path / "custom_llm_model.csv"
        csv_path.write_text(csv_content)

        monkeypatch.chdir(tmp_path)

        # Force local execution and point to custom CSV
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-openai-key-for-testing")
        monkeypatch.setenv("GEMINI_API_KEY", "fake-gemini-key-for-testing")

        # 3. Mock litellm.completion to avoid real API calls
        def mock_completion(*args, **kwargs):
            """Mock that returns a simple code response."""
            mock_response = MagicMock()
            mock_response.choices = [MagicMock()]
            mock_response.choices[0].message.content = '''```python
def add(a, b):
    return a + b
```'''
            mock_response.choices[0].finish_reason = "stop"
            mock_response.model = "gemini/gemini-2.0-flash-exp"
            mock_response.usage = MagicMock()
            mock_response.usage.prompt_tokens = 50
            mock_response.usage.completion_tokens = 30
            mock_response.usage.total_tokens = 80
            return mock_response

        # 4. Patch _load_model_data to use our custom CSV
        import pandas as pd

        def load_custom_csv(path=None):
            """Load model data from custom CSV - ignores path parameter."""
            df = pd.read_csv(csv_path)
            df['avg_cost'] = (df['input'] + df['output']) / 2
            df['structured_output'] = df['structured_output'].fillna(False).astype(bool)
            df['coding_arena_elo'] = df['coding_arena_elo'].fillna(0).astype(int)
            df['max_reasoning_tokens'] = df['max_reasoning_tokens'].fillna(0).astype(int)
            # Also need to ensure api_key column is handled properly
            df['api_key'] = df['api_key'].fillna('').astype(str)
            return df

        # Make sure PDD_MODEL_DEFAULT is not set (use hardcoded default)
        if "PDD_MODEL_DEFAULT" in os.environ:
            del os.environ["PDD_MODEL_DEFAULT"]

        # 5. Run the CLI command and capture logs
        with caplog.at_level(logging.WARNING, logger="pdd.llm_invoke"):
            # Patch both the CSV path and the loader function
            with patch('pdd.llm_invoke.LLM_MODEL_CSV_PATH', csv_path):
                with patch('pdd.llm_invoke._load_model_data', side_effect=load_custom_csv):
                    with patch('pdd.llm_invoke.litellm.completion', side_effect=mock_completion):
                        with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": 0.001, "input_tokens": 50, "output_tokens": 30}):
                            from pdd import cli

                            runner = CliRunner()
                            result = runner.invoke(cli.cli, [
                                "--local",  # Force local execution
                                "generate",
                                "test_python.prompt",
                                "--output", "output.py"
                            ], catch_exceptions=False)

        # 6. THE KEY ASSERTION: No warning about missing base model
        # Check that the command completed successfully
        assert result.exit_code == 0, f"Command failed with: {result.output}"

        # THE BUG CHECK: Verify NO warning about 'gpt-5.1-codex-mini' not found
        warning_messages = [record.message for record in caplog.records if record.levelname == "WARNING"]
        base_model_warnings = [
            msg for msg in warning_messages
            if "gpt-5.1-codex-mini" in msg and "not found in CSV" in msg
        ]

        assert len(base_model_warnings) == 0, (
            f"BUG DETECTED (Issue #296): PDD logged a warning about the base model not being in CSV.\n"
            f"Users who intentionally remove models from their CSV should NOT see this warning.\n"
            f"Warning found: {base_model_warnings}\n\n"
            f"All warnings logged: {warning_messages}\n\n"
            f"The user explicitly removed 'gpt-5.1-codex-mini' from their custom CSV, so this warning "
            f"is confusing and incorrect. The CSV should be treated as the single source of truth."
        )

    def test_csv_exclusion_works_for_entire_model_family_e2e(
        self, tmp_path, monkeypatch, caplog
    ):
        """
        E2E Test: Real-world scenario where user removes entire gpt-5* family

        This matches the exact issue from #296 where the user said:
        "All those gpt 5.1 models do is generate errors and slow down my pdd usage."

        The user wants to completely exclude the gpt-5* family from their workflow.

        Expected behavior (after fix):
        - PDD uses available models from CSV without warnings
        - No mention of gpt-5* models anywhere in the output

        Bug behavior (Issue #296):
        - Warnings about gpt-5.1-codex-mini not found
        - User can't fully control which models are used
        """
        # 1. Create a simple prompt file
        prompt_content = """Write a Python hello world."""
        (tmp_path / "hello.prompt").write_text(prompt_content)

        # 2. Custom CSV with NO gpt-5* models (user intentionally removed entire family)
        csv_content = """provider,model,input,output,coding_arena_elo,structured_output,base_url,api_key,max_tokens,max_completion_tokens,reasoning_type,max_reasoning_tokens
Gemini,gemini/gemini-2.0-flash-exp,0.0,0.0,1500,TRUE,,,,,none,0
OpenAI,gpt-4o,0.0025,0.01,1600,TRUE,,OPENAI_API_KEY,,,none,0
OpenAI,gpt-4o-mini,0.15,0.6,1450,TRUE,,OPENAI_API_KEY,,,none,0
"""
        csv_path = tmp_path / "no_gpt5_models.csv"
        csv_path.write_text(csv_content)

        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key")
        monkeypatch.setenv("GEMINI_API_KEY", "fake-key")

        # Mock LLM response
        def mock_completion(*args, **kwargs):
            mock_response = MagicMock()
            mock_response.choices = [MagicMock()]
            mock_response.choices[0].message.content = 'print("Hello, World!")'
            mock_response.choices[0].finish_reason = "stop"
            mock_response.model = "gemini/gemini-2.0-flash-exp"
            mock_response.usage = MagicMock()
            mock_response.usage.prompt_tokens = 20
            mock_response.usage.completion_tokens = 10
            mock_response.usage.total_tokens = 30
            return mock_response

        import pandas as pd

        def load_no_gpt5_csv(path=None):
            """Load model data without gpt-5* models - ignores path parameter."""
            df = pd.read_csv(csv_path)
            df['avg_cost'] = (df['input'] + df['output']) / 2
            df['structured_output'] = df['structured_output'].fillna(False).astype(bool)
            df['coding_arena_elo'] = df['coding_arena_elo'].fillna(0).astype(int)
            df['max_reasoning_tokens'] = df['max_reasoning_tokens'].fillna(0).astype(int)
            df['api_key'] = df['api_key'].fillna('').astype(str)
            return df

        # Make sure PDD_MODEL_DEFAULT is not set (use hardcoded default)
        if "PDD_MODEL_DEFAULT" in os.environ:
            del os.environ["PDD_MODEL_DEFAULT"]

        # Run command and capture all output
        with caplog.at_level(logging.DEBUG, logger="pdd.llm_invoke"):
            with patch('pdd.llm_invoke.LLM_MODEL_CSV_PATH', csv_path):
                with patch('pdd.llm_invoke._load_model_data', side_effect=load_no_gpt5_csv):
                    with patch('pdd.llm_invoke.litellm.completion', side_effect=mock_completion):
                        with patch('pdd.llm_invoke._LAST_CALLBACK_DATA', {"cost": 0.001, "input_tokens": 20, "output_tokens": 10}):
                            from pdd import cli

                            runner = CliRunner()
                            result = runner.invoke(cli.cli, [
                                "--local",
                                "generate",
                                "hello.prompt",
                                "--output", "hello.py"
                            ], catch_exceptions=False)

        # Verify success
        assert result.exit_code == 0, f"Command failed: {result.output}"

        # THE KEY CHECK: No mentions of gpt-5 models in any logs
        all_messages = [record.message for record in caplog.records]
        gpt5_mentions = [msg for msg in all_messages if "gpt-5" in msg.lower()]

        assert len(gpt5_mentions) == 0, (
            f"BUG DETECTED (Issue #296): PDD mentioned gpt-5 models even though user excluded them.\n"
            f"User removed entire gpt-5* family from CSV to avoid errors and slowdowns.\n"
            f"gpt-5 mentions found in logs: {gpt5_mentions}\n\n"
            f"The user's CSV should be the single source of truth. If a model isn't in the CSV, "
            f"PDD should not mention it, warn about it, or try to use it."
        )
