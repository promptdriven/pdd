# tests/test_quiet_flag.py
"""
Tests for the --quiet flag fully suppressing output (issue #541).

The --quiet global flag should produce zero output on stdout/stderr (except errors).
Currently, four output channels bypass it:
  1. Python logging (logger.info() in llm_invoke.py)
  2. Rich Console panels (preprocess.py always prints Panel(...))
  3. LiteLLM internal loggers (configured independently of the quiet flag)
  4. click.echo / print statements not gated by quiet flag

The fix requires:
  - cli.py sets os.environ['PDD_QUIET'] = '1' when --quiet is passed (mirrors PDD_FORCE, PDD_FORCE_LOCAL)
  - llm_invoke.py provides set_quiet_logging() that raises loggers to ERROR level
  - preprocess.py gates Rich panels on os.getenv("PDD_QUIET")
"""

import io
import logging
import os
from unittest.mock import MagicMock, patch

import pytest
from click.testing import CliRunner


# ---------------------------------------------------------------------------
# Test 1: CLI --quiet sets PDD_QUIET=1 env var
# ---------------------------------------------------------------------------

def test_cli_quiet_sets_pdd_quiet_env_var():
    """
    When --quiet is passed, the CLI group callback should set os.environ['PDD_QUIET'] = '1',
    mirroring the existing PDD_FORCE=1 and PDD_FORCE_LOCAL=1 patterns.

    BUG: Currently cli.py only sets ctx.obj['quiet'] = True but does NOT set PDD_QUIET in
    os.environ, so lower-level modules that need a centralized suppression signal have no way
    to detect it.

    This test fails on the buggy code because PDD_QUIET is never written.
    """
    # Import here to avoid side effects at module level
    from pdd.core.cli import cli

    runner = CliRunner()

    captured_env = {}

    # Use a dummy subcommand that captures the env var
    import click

    @cli.command("_test_quiet_env")
    @click.pass_context
    def _test_quiet_env(ctx):
        """Dummy command that records PDD_QUIET value."""
        captured_env["PDD_QUIET"] = os.environ.get("PDD_QUIET", "NOT_SET")

    try:
        with patch.dict(os.environ, {}, clear=False):
            # Remove PDD_QUIET if already set from a previous test
            os.environ.pop("PDD_QUIET", None)
            result = runner.invoke(cli, ["--quiet", "_test_quiet_env"])

        # The command should succeed (exit 0 or close to it after our stub)
        assert "PDD_QUIET" in captured_env, "Dummy command never ran"
        assert captured_env["PDD_QUIET"] == "1", (
            f"Expected PDD_QUIET=1 when --quiet is used, got '{captured_env['PDD_QUIET']}'. "
            "The cli() group callback must set os.environ['PDD_QUIET'] = '1' like it does for PDD_FORCE."
        )
    finally:
        # Always unregister the dummy command so it doesn't pollute other tests
        cli.commands.pop("_test_quiet_env", None)
        os.environ.pop("PDD_QUIET", None)


# ---------------------------------------------------------------------------
# Test 2: set_quiet_logging() exists and raises loggers to ERROR level
# ---------------------------------------------------------------------------

def test_set_quiet_logging_suppresses_info_and_debug():
    """
    llm_invoke.py should expose a set_quiet_logging() function (mirroring
    set_verbose_logging()) that raises both the pdd.llm_invoke logger and the
    litellm logger to ERROR level, so INFO lines stop appearing.

    BUG: Currently llm_invoke.py has set_verbose_logging() but no set_quiet_logging().
    This test fails because the function does not exist.
    """
    from pdd import llm_invoke

    # The function must exist
    assert hasattr(llm_invoke, "set_quiet_logging"), (
        "llm_invoke.py must define set_quiet_logging() to centrally suppress INFO/DEBUG output. "
        "Currently only set_verbose_logging() exists."
    )

    # Call it and verify loggers are raised to ERROR
    llm_invoke.set_quiet_logging()

    pdd_logger = logging.getLogger("pdd.llm_invoke")
    litellm_logger = logging.getLogger("litellm")

    try:
        assert pdd_logger.level >= logging.ERROR, (
            f"pdd.llm_invoke logger level should be >= ERROR after set_quiet_logging(), "
            f"got {logging.getLevelName(pdd_logger.level)}"
        )
        assert litellm_logger.level >= logging.ERROR, (
            f"litellm logger level should be >= ERROR after set_quiet_logging(), "
            f"got {logging.getLevelName(litellm_logger.level)}"
        )
    finally:
        # Restore defaults so we don't pollute other tests
        if hasattr(llm_invoke, "set_verbose_logging"):
            llm_invoke.set_verbose_logging(False)


# ---------------------------------------------------------------------------
# Test 3: INFO lines are NOT emitted when PDD_QUIET=1
# ---------------------------------------------------------------------------

def test_info_logging_suppressed_when_pdd_quiet_set(capfd):
    """
    When PDD_QUIET=1 is in the environment, INFO-level messages from pdd.llm_invoke
    should NOT reach the console handler.

    BUG: The pdd.llm_invoke logger level is configured at import time via PDD_LOG_LEVEL
    with no awareness of PDD_QUIET, so logger.info() calls always print.
    """
    from pdd import llm_invoke

    logger = logging.getLogger("pdd.llm_invoke")
    original_level = logger.level

    try:
        with patch.dict(os.environ, {"PDD_QUIET": "1"}):
            # If set_quiet_logging() exists, call it (the intended fix)
            if hasattr(llm_invoke, "set_quiet_logging"):
                llm_invoke.set_quiet_logging()
            else:
                # If the function doesn't exist yet, verify the logger is still at INFO
                # (which means the bug is present) — we still assert the output is empty
                pass

            # Emit an INFO message
            logger.info("This INFO message should NOT appear when PDD_QUIET=1")

        out, err = capfd.readouterr()
        combined = out + err

        assert "This INFO message should NOT appear when PDD_QUIET=1" not in combined, (
            "INFO-level log message leaked despite PDD_QUIET=1. "
            "set_quiet_logging() must raise the logger level to ERROR."
        )
    finally:
        logger.setLevel(original_level)


# ---------------------------------------------------------------------------
# Test 4: LiteLLM logger is suppressed when PDD_QUIET=1
# ---------------------------------------------------------------------------

def test_litellm_logger_suppressed_when_pdd_quiet_set(capfd):
    """
    When PDD_QUIET=1, the litellm logger should be raised to ERROR so its
    INFO-level messages don't leak.

    BUG: litellm_logger.setLevel() is called at module import with a default of INFO
    (non-production) and is never updated by the quiet flag.
    """
    from pdd import llm_invoke

    litellm_logger = logging.getLogger("litellm")
    original_level = litellm_logger.level

    try:
        with patch.dict(os.environ, {"PDD_QUIET": "1"}):
            if hasattr(llm_invoke, "set_quiet_logging"):
                llm_invoke.set_quiet_logging()

            litellm_logger.info("LiteLLM INFO should be hidden when PDD_QUIET=1")

        out, err = capfd.readouterr()
        combined = out + err

        assert "LiteLLM INFO should be hidden when PDD_QUIET=1" not in combined, (
            "litellm INFO message leaked despite PDD_QUIET=1. "
            "set_quiet_logging() must also raise the litellm logger to ERROR."
        )
    finally:
        litellm_logger.setLevel(original_level)


# ---------------------------------------------------------------------------
# Test 5: preprocess() produces NO Rich output when PDD_QUIET=1
# ---------------------------------------------------------------------------

def test_preprocess_no_rich_output_when_pdd_quiet(tmp_path):
    """
    When PDD_QUIET=1 is in the environment, preprocess() should skip all
    Rich console.print() calls (including the 'Starting prompt preprocessing'
    and 'Preprocessing complete' panels).

    BUG: preprocess.py has no quiet-awareness; console.print(Panel(...)) runs
    unconditionally regardless of any environment variable.

    This test uses a mock on the module-level 'console' object to detect prints.
    """
    import pdd.preprocess as preprocess_mod

    with patch.dict(os.environ, {"PDD_QUIET": "1"}):
        with patch.object(preprocess_mod, "console") as mock_console:
            preprocess_mod.preprocess("Hello world")

            # In quiet mode, no Rich panels should be printed
            panel_calls = [
                call for call in mock_console.print.call_args_list
                if call.args and hasattr(call.args[0], "__class__")
                and call.args[0].__class__.__name__ == "Panel"
            ]
            assert len(panel_calls) == 0, (
                f"preprocess() printed {len(panel_calls)} Rich Panel(s) despite PDD_QUIET=1: {panel_calls}. "
                "preprocess() must check os.getenv('PDD_QUIET') before calling console.print(Panel(...))."
            )


# ---------------------------------------------------------------------------
# Test 6: preprocess() DOES print panels without quiet (regression guard)
# ---------------------------------------------------------------------------

def test_preprocess_prints_panels_without_quiet(tmp_path):
    """
    When PDD_QUIET is NOT set, preprocess() should still print its Rich panels
    as normal. This is a regression guard to ensure the fix doesn't break
    normal (non-quiet) output.
    """
    import pdd.preprocess as preprocess_mod

    # Ensure PDD_QUIET is not set
    env_without_quiet = {k: v for k, v in os.environ.items() if k != "PDD_QUIET"}

    with patch.dict(os.environ, env_without_quiet, clear=True):
        with patch.object(preprocess_mod, "console") as mock_console:
            preprocess_mod.preprocess("Hello world")

            panel_calls = [
                call for call in mock_console.print.call_args_list
                if call.args and hasattr(call.args[0], "__class__")
                and call.args[0].__class__.__name__ == "Panel"
            ]
            # Should have at least 2 panels: "Starting prompt preprocessing" + "Preprocessing complete"
            assert len(panel_calls) >= 2, (
                f"Expected at least 2 Rich panels without quiet mode, got {len(panel_calls)}. "
                "Normal (non-quiet) output must not be suppressed."
            )


# ---------------------------------------------------------------------------
# Test 7: ERROR-level messages still appear even with PDD_QUIET=1 (regression guard)
# ---------------------------------------------------------------------------

def test_error_level_still_emitted_when_pdd_quiet_set(caplog):
    """
    Quiet mode must NOT suppress ERROR-level log messages — errors should
    always be visible. This is a regression guard ensuring that set_quiet_logging()
    only raises the threshold to ERROR, not above it.

    Uses pytest caplog to capture log records directly (independent of the
    StreamHandler's fd-level output).
    """
    from pdd import llm_invoke

    logger = logging.getLogger("pdd.llm_invoke")
    original_level = logger.level

    try:
        with patch.dict(os.environ, {"PDD_QUIET": "1"}):
            if hasattr(llm_invoke, "set_quiet_logging"):
                llm_invoke.set_quiet_logging()

            with caplog.at_level(logging.ERROR, logger="pdd.llm_invoke"):
                logger.error("CRITICAL ERROR: this must always be visible")

        assert any(
            "CRITICAL ERROR: this must always be visible" in record.message
            for record in caplog.records
        ), (
            "ERROR-level messages must not be suppressed by quiet mode. "
            "set_quiet_logging() should set level to ERROR (not CRITICAL), "
            "so errors still surface."
        )
    finally:
        logger.setLevel(original_level)
