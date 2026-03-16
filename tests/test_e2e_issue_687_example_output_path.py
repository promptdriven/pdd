"""
E2E Test for Issue #687: Prompt generation creates code file includes instead of
example file includes.

Root cause: code_generator_main.py resolves `example_output_path` from .pddrc via
construct_paths(), but never injects it into env_vars for template variable
substitution. Templates using ${EXAMPLE_OUTPUT_PATH} are left unexpanded, so the
LLM has no guidance on example file paths and falls back to emitting raw source
code paths like `src/core/storage_layer.py` instead of `_example.py` paths.

This E2E test exercises the real code_generator_main → construct_paths →
_expand_vars pipeline with a .pddrc that specifies example_output_path. Only the
LLM call itself is mocked (to capture the prompt). Everything else runs for real.

The test FAILS on buggy code (${EXAMPLE_OUTPUT_PATH} remains unexpanded) and
PASSES once example_output_path is injected into env_vars.
"""

import os
import json
from pathlib import Path
from unittest.mock import patch, MagicMock

import click
import pytest

from pdd.code_generator_main import code_generator_main


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory for all tests in this module."""
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


def _make_click_ctx(*, local=True, force=True, quiet=True, verbose=False, strength=0.5):
    """Build a minimal Click context matching what the CLI would provide."""
    ctx = click.Context(click.Command("generate"))
    ctx.obj = {
        "local": local,
        "force": force,
        "quiet": quiet,
        "verbose": verbose,
        "strength": strength,
        "temperature": 0.0,
        "time": 60,
    }
    return ctx


@pytest.mark.e2e
class TestIssue687ExampleOutputPathE2E:
    """
    E2E tests for Issue #687: When .pddrc specifies example_output_path, that
    value must be available as ${EXAMPLE_OUTPUT_PATH} in prompt templates so the
    LLM knows where example files live.
    """

    def test_example_output_path_from_pddrc_expands_in_prompt(
        self, tmp_path, monkeypatch
    ):
        """
        E2E: A .pddrc with example_output_path should cause ${EXAMPLE_OUTPUT_PATH}
        in a prompt template to be expanded before the prompt reaches the LLM.

        Setup:
        - .pddrc in tmp_path with example_output_path: "context/examples"
        - A prompt file referencing ${EXAMPLE_OUTPUT_PATH}
        - Real construct_paths and _expand_vars (NOT mocked)
        - Only the LLM call (local_code_generator_func) is mocked

        Expected (after fix):
        - The prompt received by the LLM contains "context/examples"
        - ${EXAMPLE_OUTPUT_PATH} is NOT present as a literal

        Bug behavior (Issue #687):
        - ${EXAMPLE_OUTPUT_PATH} remains as a literal in the LLM prompt
        - The LLM has no info about example paths and emits source code paths
        """
        monkeypatch.chdir(tmp_path)

        # 1. Create .pddrc with example_output_path in the default context
        pddrc_content = """\
prompts_dir: prompts
contexts:
  default:
    defaults:
      example_output_path: context/examples
      generate_output_path: src
"""
        (tmp_path / ".pddrc").write_text(pddrc_content, encoding="utf-8")

        # 2. Create the prompt file that uses ${EXAMPLE_OUTPUT_PATH}
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir(exist_ok=True)
        prompt_content = """\
You are generating a Python module.

Example files are located at: ${EXAMPLE_OUTPUT_PATH}

When specifying dependency includes, use the example_output_path prefix:
<include>${EXAMPLE_OUTPUT_PATH}/storage_layer_example.py</include>

Do NOT use raw source code paths like src/core/storage_layer.py.
"""
        prompt_file = prompts_dir / "staleness_review_Python.prompt"
        prompt_file.write_text(prompt_content, encoding="utf-8")

        # 3. Create output directory
        output_dir = tmp_path / "src"
        output_dir.mkdir(exist_ok=True)
        output_file = output_dir / "staleness_review.py"

        # 4. Build the Click context
        ctx = _make_click_ctx(local=True, force=True, quiet=True)

        # 5. Mock the LLM call to capture the prompt it receives
        captured_prompts = []

        def mock_code_generator(**kwargs):
            """Capture the prompt sent to the LLM."""
            captured_prompts.append(kwargs.get("prompt", ""))
            return "# Generated code\npass", 0.01, "mock-model"

        with patch(
            "pdd.code_generator_main.local_code_generator_func",
            side_effect=mock_code_generator,
        ):
            code_generator_main(
                ctx,
                prompt_file=str(prompt_file),
                output=str(output_file),
                original_prompt_file_path=None,
                force_incremental_flag=False,
            )

        # 6. CRITICAL ASSERTIONS
        assert len(captured_prompts) > 0, (
            "LLM was never called — code_generator_main failed before reaching "
            "the local code generator"
        )

        llm_prompt = captured_prompts[0]

        # THE KEY ASSERTION: ${EXAMPLE_OUTPUT_PATH} must be expanded.
        # The preprocessor doubles curly brackets, so unexpanded vars appear as
        # ${{EXAMPLE_OUTPUT_PATH}} in the final prompt. Check for both forms.
        unexpanded = (
            "${EXAMPLE_OUTPUT_PATH}" in llm_prompt
            or "${{EXAMPLE_OUTPUT_PATH}}" in llm_prompt
        )
        assert not unexpanded, (
            "BUG #687 DETECTED: ${EXAMPLE_OUTPUT_PATH} was NOT expanded in the "
            "prompt sent to the LLM.\n\n"
            "Setup:\n"
            "  - .pddrc specifies example_output_path: 'context/examples'\n"
            "  - Prompt template uses ${EXAMPLE_OUTPUT_PATH}\n\n"
            "Expected:\n"
            "  - code_generator_main injects example_output_path from "
            "resolved_config into env_vars\n"
            "  - _expand_vars replaces ${EXAMPLE_OUTPUT_PATH} with "
            "'context/examples'\n\n"
            "Actual:\n"
            "  - ${EXAMPLE_OUTPUT_PATH} remains as a literal string\n"
            "  - LLM has no guidance on example paths\n"
            "  - LLM falls back to emitting raw source code paths\n\n"
            f"Prompt snippet: {llm_prompt[:500]}"
        )

        # Verify the expanded value is present
        assert "context/examples" in llm_prompt, (
            "Expected 'context/examples' (from .pddrc example_output_path) to "
            f"appear in the LLM prompt, but it was not found.\n"
            f"Prompt snippet: {llm_prompt[:500]}"
        )

    def test_example_output_path_absent_without_pddrc_no_crash(
        self, tmp_path, monkeypatch
    ):
        """
        E2E: When no .pddrc exists, code_generator_main should not crash.
        ${EXAMPLE_OUTPUT_PATH} may remain unexpanded (acceptable fallback) but
        the function must not raise an exception.

        This tests graceful degradation — the primary fix is for the case when
        .pddrc IS present (covered by the test above).
        """
        monkeypatch.chdir(tmp_path)

        # No .pddrc — just a bare prompt file
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir(exist_ok=True)
        prompt_content = "Examples at ${EXAMPLE_OUTPUT_PATH}/module_example.py"
        prompt_file = prompts_dir / "test_Python.prompt"
        prompt_file.write_text(prompt_content, encoding="utf-8")

        output_dir = tmp_path / "src"
        output_dir.mkdir(exist_ok=True)
        output_file = output_dir / "test.py"

        ctx = _make_click_ctx(local=True, force=True, quiet=True)

        captured_prompts = []

        def mock_code_generator(**kwargs):
            captured_prompts.append(kwargs.get("prompt", ""))
            return "# Generated code\npass", 0.01, "mock-model"

        with patch(
            "pdd.code_generator_main.local_code_generator_func",
            side_effect=mock_code_generator,
        ):
            # Should not raise
            result = code_generator_main(
                ctx,
                prompt_file=str(prompt_file),
                output=str(output_file),
                original_prompt_file_path=None,
                force_incremental_flag=False,
            )

        # The function completed without crashing
        assert result is not None, "code_generator_main returned None unexpectedly"
