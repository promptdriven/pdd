"""
E2E CLI Test for Issue #486: --quiet flag does not suppress output

Tests the full CLI path: `pdd --quiet generate <prompt>` should suppress
INFO logs, Rich panels, warnings, and success messages. Currently FAILS
because preprocess() unconditionally prints Rich panels regardless of --quiet.
"""

import pytest
from unittest.mock import patch, MagicMock
from click.testing import CliRunner

from pdd.cli import cli


@pytest.fixture
def prompt_file(tmp_path):
    """Create a minimal prompt file for testing."""
    p = tmp_path / "test_python.prompt"
    p.write_text("Write a function that returns 'hello'.")
    return str(p)


# Noisy patterns that --quiet should suppress
NOISY_PATTERNS = [
    "Starting prompt preprocessing",
    "Preprocessing complete",
    "Doubling curly brackets",
    "Successfully loaded prompt",
]


class TestQuietFlagE2E:
    """E2E tests verifying --quiet suppresses output through the full CLI path.

    These tests let preprocess() actually execute (producing Rich output)
    but mock the LLM generators to avoid needing API keys.
    The key assertion: preprocess's Rich panel output must NOT appear when --quiet.
    """

    def _run_generate(self, runner, args, prompt_file):
        """Run generate command with mocked LLM generators so preprocess runs."""
        with patch("pdd.code_generator_main.local_code_generator_func") as mock_local, \
             patch("pdd.code_generator_main.incremental_code_generator_func") as mock_incr, \
             patch("pdd.code_generator_main.requests") as mock_requests:
            mock_local.return_value = ("def hello(): return 'hello'", 0.01, "mock-model")
            mock_incr.return_value = ("def hello(): return 'hello'", False, 0.01, "mock-model")
            # Make cloud check fail so it goes to local path
            mock_requests.post.side_effect = Exception("no cloud")
            mock_requests.get.side_effect = Exception("no cloud")

            return runner.invoke(cli, args + [prompt_file])

    def test_quiet_generate_suppresses_preprocessing_output(self, prompt_file):
        """pdd --quiet generate should not show preprocessing panels.

        FAILS on buggy code because preprocess() unconditionally prints
        'Starting prompt preprocessing' and 'Preprocessing complete' panels.
        """
        runner = CliRunner(mix_stderr=False)
        result = self._run_generate(runner, ["--quiet", "generate"], prompt_file)

        stdout = result.output
        found = [p for p in NOISY_PATTERNS if p in stdout]
        assert not found, (
            f"--quiet should suppress preprocessing output.\n"
            f"Found noisy patterns: {found}\n"
            f"Full output:\n{stdout}"
        )

    def test_non_quiet_generate_shows_preprocessing_output(self, prompt_file):
        """Without --quiet, generate should show preprocessing panels (regression guard)."""
        runner = CliRunner(mix_stderr=False)
        result = self._run_generate(runner, ["generate"], prompt_file)

        stdout = result.output
        has_panel = any(p in stdout for p in ["Starting prompt preprocessing", "Preprocessing complete"])
        assert has_panel, (
            f"Without --quiet, preprocessing panels should be visible.\n"
            f"Output:\n{stdout}"
        )

    def test_quiet_flag_still_shows_errors(self, tmp_path):
        """pdd --quiet generate with nonexistent file should still show error."""
        runner = CliRunner(mix_stderr=False)
        result = runner.invoke(cli, ["--quiet", "generate", str(tmp_path / "nonexistent.prompt")])

        assert result.exit_code != 0 or "does not exist" in result.output, (
            "Errors should still be shown even in quiet mode"
        )
