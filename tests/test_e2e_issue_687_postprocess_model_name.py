"""
E2E Test for Issue #687: code_generator.py returns wrong model name after postprocessing

This test exercises the full code_generator() pipeline (preprocess -> llm_invoke ->
unfinished_prompt -> postprocess) to verify that when postprocessing uses a different
model than initial generation, the postprocess model name is returned.

The bug: In code_generator.py:162, the return statement uses `model_name` (from initial
generation) instead of `model_name_post` (from postprocessing).

This E2E test mocks at the llm_invoke boundary (the LLM edge) while exercising the
full code_generator pipeline logic, including the buggy return statement at line 162.

The test should FAIL on buggy code and PASS once the fix is applied.
"""

import pytest
from pathlib import Path
from unittest.mock import patch
from click.testing import CliRunner

from pdd import cli


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory for language detection."""
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


INITIAL_MODEL = "gpt-4o-initial"
POSTPROCESS_MODEL = "claude-3-5-sonnet-postprocess"


class TestPostprocessModelNameE2E:
    """
    E2E tests for Issue #687: Verify the model name returned by code_generator()
    reflects the postprocessing model, not the initial generation model.
    """

    def test_generate_cli_returns_postprocess_model_name(
        self, tmp_path, monkeypatch
    ):
        """
        E2E Test: pdd generate -> code_generator_main -> code_generator pipeline

        Exercises the full CLI path with mocks at the llm_invoke boundary.
        The code_generator function calls llm_invoke for generation, unfinished_prompt
        for completion check, and postprocess for code extraction — each getting
        distinct model names. The returned model name should be from postprocess.

        Bug behavior (Issue #687):
        - Returns "gpt-4o-initial" (initial generation model)

        Expected behavior:
        - Returns "claude-3-5-sonnet-postprocess" (postprocess model)
        """
        prompt_content = """Write a Python function that adds two numbers."""
        (tmp_path / "test_python.prompt").write_text(prompt_content)

        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key-for-testing")

        # Mock llm_invoke at the code_generator module level — this is the LLM boundary
        # The code_generator calls: llm_invoke (generation), unfinished_prompt, postprocess
        # We mock llm_invoke for generation, and the other two as separate functions
        # that still exercise code_generator's pipeline logic

        generation_response = {
            'result': '```python\ndef add(a, b):\n    return a + b\n```',
            'cost': 0.001,
            'model_name': INITIAL_MODEL,
        }

        # Mock at the sub-function level to let code_generator's pipeline logic run
        # but control the model names returned by each step
        with patch('pdd.code_generator.llm_invoke', return_value=generation_response):
            with patch('pdd.code_generator.unfinished_prompt', return_value=(
                "Code is complete", True, 0.0005, "check-model"
            )):
                with patch('pdd.code_generator.postprocess', return_value=(
                    "def add(a, b):\n    return a + b", 0.0003, POSTPROCESS_MODEL
                )):
                    runner = CliRunner()
                    result = runner.invoke(cli.cli, [
                        "--local",
                        "--verbose",
                        "generate",
                        "test_python.prompt",
                        "--output", "output.py"
                    ], catch_exceptions=False)

        assert result.exit_code == 0, (
            f"CLI exited with code {result.exit_code}. Output:\n{result.output}"
        )

        # Verify the output file was created
        output_file = tmp_path / "output.py"
        assert output_file.exists(), "Output file was not created"

        # Verify the verbose output shows the postprocess model, not the initial model
        assert POSTPROCESS_MODEL in result.output, (
            f"BUG DETECTED (Issue #687): Verbose output shows initial model "
            f"'{INITIAL_MODEL}' instead of postprocess model '{POSTPROCESS_MODEL}'.\n"
            f"CLI output:\n{result.output}"
        )

    def test_code_generator_returns_postprocess_model_directly(self):
        """
        E2E Test: Direct call to code_generator() verifying the returned model name.

        This calls code_generator() directly (not through CLI) with mocks at the
        llm_invoke/unfinished_prompt/postprocess boundary. The code_generator function's
        own pipeline logic (lines 44-162) runs unmocked — including the buggy
        return statement at line 162.

        This is the primary test that catches issue #687.
        """
        from pdd.code_generator import code_generator

        generation_response = {
            'result': '```python\ndef add(a, b):\n    return a + b\n```',
            'cost': 0.001,
            'model_name': INITIAL_MODEL,
        }

        with patch('pdd.code_generator.llm_invoke', return_value=generation_response):
            with patch('pdd.code_generator.unfinished_prompt', return_value=(
                "Code is complete", True, 0.0005, "check-model"
            )):
                with patch('pdd.code_generator.postprocess', return_value=(
                    "def add(a, b):\n    return a + b", 0.0003, POSTPROCESS_MODEL
                )):
                    code, cost, returned_model = code_generator(
                        prompt="Write a Python function that adds two numbers.",
                        language="python",
                        strength=0.5,
                        temperature=0.0,
                    )

        # Verify code was generated
        assert "def add" in code, f"Expected generated code, got: {code}"

        # THE BUG CHECK: returned model should be the postprocess model
        assert returned_model == POSTPROCESS_MODEL, (
            f"BUG DETECTED (Issue #687): code_generator() returned model name "
            f"'{returned_model}' from initial generation instead of "
            f"'{POSTPROCESS_MODEL}' from postprocessing.\n"
            f"The return statement at code_generator.py:162 uses 'model_name' "
            f"instead of 'model_name_post'."
        )

    def test_code_generator_with_continuation_returns_postprocess_model(self):
        """
        E2E Test: When generation is incomplete and continuation runs,
        the final model name should still be from postprocess (not continuation).

        Pipeline: llm_invoke -> unfinished_prompt(False) -> continue_generation -> postprocess
        Expected model: postprocess model (the last LLM step)
        """
        from pdd.code_generator import code_generator

        CONTINUE_MODEL = "gpt-4o-continue"

        generation_response = {
            'result': '```python\ndef add(a, b):\n    return a +',
            'cost': 0.001,
            'model_name': INITIAL_MODEL,
        }

        with patch('pdd.code_generator.llm_invoke', return_value=generation_response):
            with patch('pdd.code_generator.unfinished_prompt', return_value=(
                "Code is incomplete — truncated mid-expression", False, 0.0005, "check-model"
            )):
                with patch('pdd.code_generator.continue_generation', return_value=(
                    '```python\ndef add(a, b):\n    return a + b\n```',
                    0.0008, CONTINUE_MODEL
                )):
                    with patch('pdd.code_generator.postprocess', return_value=(
                        "def add(a, b):\n    return a + b", 0.0003, POSTPROCESS_MODEL
                    )):
                        code, cost, returned_model = code_generator(
                            prompt="Write a Python function that adds two numbers.",
                            language="python",
                            strength=0.5,
                            temperature=0.0,
                        )

        assert returned_model == POSTPROCESS_MODEL, (
            f"BUG DETECTED (Issue #687): After continuation + postprocess, "
            f"code_generator() returned '{returned_model}' instead of "
            f"'{POSTPROCESS_MODEL}'. The return statement uses 'model_name' "
            f"(which was updated to '{CONTINUE_MODEL}' by continuation) "
            f"instead of 'model_name_post' from postprocessing."
        )

    def test_json_language_skips_postprocess_returns_initial_model(self):
        """
        Negative test: When language is JSON, postprocess is skipped.
        The initial generation model should be returned (this is correct behavior).

        Ensures the fix for #687 doesn't break the JSON path.
        """
        from pdd.code_generator import code_generator

        generation_response = {
            'result': '{"key": "value"}',
            'cost': 0.001,
            'model_name': INITIAL_MODEL,
        }

        with patch('pdd.code_generator.llm_invoke', return_value=generation_response):
            with patch('pdd.code_generator.unfinished_prompt', return_value=(
                "JSON is complete", True, 0.0005, "check-model"
            )):
                with patch('pdd.code_generator.postprocess') as mock_postprocess:
                    code, cost, returned_model = code_generator(
                        prompt="Generate a JSON config.",
                        language="json",
                        strength=0.5,
                        temperature=0.0,
                    )

        # postprocess should NOT have been called for JSON
        mock_postprocess.assert_not_called()

        # model_name should be the initial model (correct behavior for JSON)
        assert returned_model == INITIAL_MODEL, (
            f"JSON path should return initial model '{INITIAL_MODEL}', "
            f"got '{returned_model}'"
        )

    def test_verbose_cli_output_shows_postprocess_model(
        self, tmp_path, monkeypatch
    ):
        """
        E2E Test: In verbose mode, code_generator_main displays the model name.
        With the bug, it shows the initial model instead of the postprocess model.
        """
        prompt_content = """Write a Python hello world."""
        (tmp_path / "test_python.prompt").write_text(prompt_content)

        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key-for-testing")

        generation_response = {
            'result': '```python\nprint("Hello, World!")\n```',
            'cost': 0.001,
            'model_name': INITIAL_MODEL,
        }

        with patch('pdd.code_generator.llm_invoke', return_value=generation_response):
            with patch('pdd.code_generator.unfinished_prompt', return_value=(
                "Code is complete", True, 0.0005, "check-model"
            )):
                with patch('pdd.code_generator.postprocess', return_value=(
                    'print("Hello, World!")', 0.0003, POSTPROCESS_MODEL
                )):
                    runner = CliRunner()
                    result = runner.invoke(cli.cli, [
                        "--local",
                        "--verbose",
                        "generate",
                        "test_python.prompt",
                        "--output", "output.py"
                    ], catch_exceptions=False)

        assert result.exit_code == 0, (
            f"CLI exited with code {result.exit_code}. Output:\n{result.output}"
        )

        # In verbose mode, code_generator_main shows:
        # "Full generation successful. Model: {model_name}, Cost: $..."
        # The model_name comes from code_generator()'s return value.
        assert POSTPROCESS_MODEL in result.output, (
            f"BUG DETECTED (Issue #687): Verbose output shows initial model "
            f"'{INITIAL_MODEL}' instead of postprocess model '{POSTPROCESS_MODEL}'.\n"
            f"CLI output:\n{result.output}"
        )
