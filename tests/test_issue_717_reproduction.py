"""
Reproduction tests for GitHub Issue #717:
  pdd test --manual ignores --manual flag and invokes agentic test generation instead.

Bug summary:
  When `--manual` is passed to `pdd test`, the command should use the legacy
  single-LLM prompt-based test generation. Instead, for non-Python languages,
  `cmd_test_main()` unconditionally routes to the agentic pipeline because:
    1. `cmd_test_main()` does not accept a `manual` parameter.
    2. Line 120 sets `use_agentic_tests` without considering `--manual`.
    3. The call in `generate.py:375` does not pass `manual` to `cmd_test_main()`.

These tests assert the CORRECT (expected) behavior.
They will FAIL on the buggy code and PASS once the bug is fixed.
"""
import inspect
from unittest.mock import patch, MagicMock, mock_open

import click
import pytest
from click import Context

from pdd.cmd_test_main import cmd_test_main


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def mock_ctx():
    """Click context with default settings, forcing local execution."""
    m_ctx = MagicMock(spec=Context)
    m_ctx.obj = {
        "verbose": False,
        "strength": 0.88,
        "temperature": 0.0,
        "force": True,
        "quiet": False,
        "local": True,
        "agentic_mode": False,
    }
    return m_ctx


@pytest.fixture
def construct_paths_shell():
    """Return value for construct_paths that reports 'shell' as the detected language."""
    return (
        {},  # resolved_config
        {
            "prompt_file": "prompt contents",
            "code_file": "code contents",
        },
        {"output": "tests/infra/test_deploy_script.sh"},
        "shell",  # detected_language — non-Python triggers the bug
    )


@pytest.fixture
def construct_paths_javascript():
    """Return value for construct_paths that reports 'javascript' as the detected language."""
    return (
        {},
        {
            "prompt_file": "prompt contents",
            "code_file": "code contents",
        },
        {"output": "tests/test_app.test.js"},
        "javascript",
    )


# ---------------------------------------------------------------------------
# Test 1: cmd_test_main signature should accept a 'manual' parameter
# ---------------------------------------------------------------------------

def test_cmd_test_main_accepts_manual_parameter():
    """
    Issue #717: cmd_test_main() does not accept a 'manual' parameter, so the
    --manual flag from the CLI can never be forwarded to it.

    After the fix, cmd_test_main should accept manual as a keyword argument.
    """
    sig = inspect.signature(cmd_test_main)
    param_names = list(sig.parameters.keys())
    assert "manual" in param_names, (
        "cmd_test_main() must accept a 'manual' parameter so the CLI can "
        "forward the --manual flag. Current params: " + ", ".join(param_names)
    )


# ---------------------------------------------------------------------------
# Test 2: Non-Python language with manual=True should NOT use agentic pipeline
# ---------------------------------------------------------------------------

def test_manual_flag_prevents_agentic_for_shell(mock_ctx, construct_paths_shell):
    """
    Issue #717: When manual=True, cmd_test_main should use the legacy single-LLM
    generation path even for non-Python languages like shell.

    The buggy code unconditionally routes non-Python languages to
    run_agentic_test_generate(), ignoring --manual entirely.
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_cp, \
         patch("pdd.cmd_test_main.generate_test") as mock_gen, \
         patch("builtins.open", mock_open()):

        mock_cp.return_value = construct_paths_shell
        mock_gen.return_value = ("generated test code", 0.05, "test_model")

        # Call with manual=True — this should use generate_test, not agentic
        result = cmd_test_main(
            ctx=mock_ctx,
            prompt_file="prompts/infra/deploy_script_Shell.prompt",
            code_file="src/infra/deploy_script.sh",
            output="tests/infra/test_deploy_script.sh",
            language=None,
            manual=True,
        )

        # generate_test (legacy path) should have been called
        mock_gen.assert_called_once()

        # Result should contain generated content, not an error
        assert result[0] == "generated test code"


def test_manual_flag_prevents_agentic_for_javascript(mock_ctx, construct_paths_javascript):
    """
    Issue #717: Same as above but for JavaScript — another non-Python language
    that would trigger the agentic pipeline without the fix.
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_cp, \
         patch("pdd.cmd_test_main.generate_test") as mock_gen, \
         patch("builtins.open", mock_open()):

        mock_cp.return_value = construct_paths_javascript
        mock_gen.return_value = ("js test code", 0.03, "test_model")

        result = cmd_test_main(
            ctx=mock_ctx,
            prompt_file="prompts/app_javascript.prompt",
            code_file="src/app.js",
            output="tests/test_app.test.js",
            language=None,
            manual=True,
        )

        mock_gen.assert_called_once()
        assert result[0] == "js test code"


# ---------------------------------------------------------------------------
# Test 3: Agentic pipeline should still be used when manual is False/absent
# ---------------------------------------------------------------------------

def test_agentic_still_used_for_non_python_without_manual(mock_ctx, construct_paths_shell):
    """
    Ensure that the agentic pipeline is still used for non-Python languages
    when manual=False (the default behavior should be preserved).
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_cp, \
         patch("pdd.cmd_test_main.run_agentic_test_generate", create=True) as mock_agentic, \
         patch("pdd.cmd_test_main.generate_test") as mock_gen:

        mock_cp.return_value = construct_paths_shell
        mock_agentic.return_value = ("agentic test code", 0.10, "agentic_model", True)

        result = cmd_test_main(
            ctx=mock_ctx,
            prompt_file="prompts/infra/deploy_script_Shell.prompt",
            code_file="src/infra/deploy_script.sh",
            output="tests/infra/test_deploy_script.sh",
            language=None,
            manual=False,
        )

        # Legacy generate_test should NOT be called
        mock_gen.assert_not_called()


# ---------------------------------------------------------------------------
# Test 4: The CLI test() command passes manual through to cmd_test_main
# ---------------------------------------------------------------------------

def test_cli_test_command_passes_manual_to_cmd_test_main():
    """
    Issue #717: The test() Click command in generate.py must forward the
    --manual flag to cmd_test_main(). Currently, the call at generate.py:375
    does not include manual=True in the kwargs.

    We verify this by patching cmd_test_main at its source module and invoking
    the CLI command through Click's test infrastructure.
    """
    from click.testing import CliRunner
    from pdd.commands.generate import test as test_cmd

    with patch("pdd.cmd_test_main.cmd_test_main", wraps=None) as mock_cmd_test:
        mock_cmd_test.return_value = ("test code", 0.05, "model", None)

        runner = CliRunner()
        result = runner.invoke(
            test_cmd,
            [
                "--manual",
                "prompts/infra/deploy_script_Shell.prompt",
                "src/infra/deploy_script.sh",
                "--output", "tests/infra/test_deploy_script.sh",
            ],
            obj={
                "verbose": False,
                "strength": 0.88,
                "temperature": 0.0,
                "force": True,
                "quiet": False,
                "local": True,
                "agentic_mode": False,
                "context": None,
                "confirm_callback": None,
                "time": 0.25,
            },
            catch_exceptions=False,
        )

        # cmd_test_main should have been called
        mock_cmd_test.assert_called_once()
        call_kwargs = mock_cmd_test.call_args.kwargs
        assert call_kwargs.get("manual") is True, (
            "The test() Click command must pass manual=True to cmd_test_main(). "
            f"Actual call kwargs: {mock_cmd_test.call_args}"
        )
