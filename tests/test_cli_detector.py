"""Tests for pdd/cli_detector.py

Behavioral tests driven through the two public entry points:
  - detect_and_bootstrap_cli()
  - detect_cli_tools()

Test plan
---------

1. CliBootstrapResult data model
   1.1 Defaults to empty strings and False flags
   1.2 Skipped result has skipped=True, rest defaults

2. detect_and_bootstrap_cli — Selection table & input parsing
   2.1 Table shows all three CLIs with install/key status
   2.2 Selecting "1" picks Claude CLI
   2.3 Comma-separated input "1,3" selects multiple CLIs
   2.4 Spaces in input "1, 3" are tolerated
   2.5 Duplicate input "1,1,3" is deduplicated
   2.6 Empty input defaults to best available (installed+key)
   2.7 Empty input defaults to installed-only when no keys set
   2.8 Invalid input falls back to default
   2.9 "q" quits with skipped result
   2.10 "n" quits with skipped result

3. detect_and_bootstrap_cli — Install flow
   3.1 Already-installed CLI skips install prompt
   3.2 Not-installed CLI prompts for install, user accepts, npm succeeds
   3.3 Not-installed CLI, user accepts install but npm missing
   3.4 Not-installed CLI, install fails (non-zero exit)
   3.5 Not-installed CLI, user declines install → skipped
   3.6 Install succeeds but binary not found on PATH afterwards

4. detect_and_bootstrap_cli — API key flow
   4.1 Key already set skips prompt
   4.2 Key not set, user provides key → saved to file and os.environ
   4.3 Key not set, user skips (Enter) → api_key_configured=False
   4.4 Anthropic skip shows subscription auth note
   4.5 Non-anthropic skip shows limited functionality note
   4.6 Google provider checks both GOOGLE_API_KEY and GEMINI_API_KEY

5. detect_and_bootstrap_cli — CLI test step
   5.1 CLI test always runs after install+key steps
   5.2 --version success shows version output
   5.3 --version fails, falls back to --help

6. detect_and_bootstrap_cli — Interrupt handling
   6.1 KeyboardInterrupt on selection prompt → skipped
   6.2 EOFError on selection prompt → skipped
   6.3 KeyboardInterrupt during per-CLI processing → stops remaining

7. detect_and_bootstrap_cli — API key persistence
   7.1 Key saved to ~/.pdd/api-env.{shell} with correct export syntax
   7.2 Source line added to shell RC file
   7.3 Fish shell uses set -gx syntax and fish source line
   7.4 Duplicate keys are deduplicated in api-env file

8. detect_cli_tools — Legacy detection
   8.1 Shows header with command context
   8.2 Found CLI shows checkmark and path
   8.3 Missing CLI shows X
   8.4 Key set but CLI missing → suggests install
   8.5 All CLIs installed with keys → success message
   8.6 No CLIs found → quick start message
"""

from __future__ import annotations

import os
import subprocess
from pathlib import Path
from unittest import mock

import pytest

from pdd.cli_detector import (
    CliBootstrapResult,
    detect_and_bootstrap_cli,
    detect_cli_tools,
)


# ---------------------------------------------------------------------------
# Module-level constants — realistic scenarios for test fixtures
# ---------------------------------------------------------------------------

# Provider/CLI status: all three CLIs installed with keys
ALL_INSTALLED = {
    "claude": "/usr/local/bin/claude",
    "codex": "/usr/local/bin/codex",
    "gemini": "/usr/local/bin/gemini",
}

ALL_KEYS = {
    "ANTHROPIC_API_KEY": "sk-ant-test",
    "OPENAI_API_KEY": "sk-oai-test",
    "GEMINI_API_KEY": "gm-test",
    "GOOGLE_API_KEY": "gm-test",
}

# Only Claude installed with key
CLAUDE_ONLY = {"claude": "/usr/local/bin/claude"}
CLAUDE_KEY = {"ANTHROPIC_API_KEY": "sk-ant-test"}

# No CLIs installed, no keys
NOTHING = {}


# ---------------------------------------------------------------------------
# Helper: capture output from detect_and_bootstrap_cli
# ---------------------------------------------------------------------------

def _run_bootstrap_capture(
    monkeypatch,
    tmp_path: Path,
    user_inputs: list[str],
    *,
    cli_paths: dict[str, str] | None = None,
    env_keys: dict[str, str] | None = None,
    npm_available: bool = False,
    install_succeeds: bool = False,
    install_then_found: str | None = None,
    version_output: str = "1.0.0",
    version_returncode: int = 0,
) -> tuple[str, list[CliBootstrapResult]]:
    """Run detect_and_bootstrap_cli with mocked boundaries.

    Args:
        monkeypatch: pytest monkeypatch fixture
        tmp_path: temporary directory for home
        user_inputs: sequence of strings for _prompt_input
        cli_paths: mapping of cli_name -> path (None = not found)
        env_keys: environment variables to set
        npm_available: whether npm is on PATH
        install_succeeds: whether subprocess install returns 0
        install_then_found: path to return after install succeeds (None = not found)
        version_output: stdout from --version
        version_returncode: exit code from --version

    Returns:
        (captured_output, results) tuple
    """
    cli_paths = cli_paths or {}
    env_keys = env_keys or {}

    # Clean environment
    for var in ("ANTHROPIC_API_KEY", "OPENAI_API_KEY", "GOOGLE_API_KEY",
                "GEMINI_API_KEY", "SHELL"):
        monkeypatch.delenv(var, raising=False)
    for k, v in env_keys.items():
        monkeypatch.setenv(k, v)
    monkeypatch.setenv("SHELL", "/bin/bash")

    # Mock Path.home to tmp_path
    monkeypatch.setattr(Path, "home", staticmethod(lambda: tmp_path))

    # Create shell RC file
    rc_file = tmp_path / ".bashrc"
    if not rc_file.exists():
        rc_file.write_text("# existing\n")

    # Mock user input
    input_iter = iter(user_inputs)
    monkeypatch.setattr(
        "pdd.cli_detector._prompt_input",
        lambda _prompt="": next(input_iter),
    )

    # Track _find_cli_binary calls to simulate post-install discovery
    find_call_count = {}

    def mock_find_cli_binary(name):
        find_call_count[name] = find_call_count.get(name, 0) + 1
        if name in cli_paths:
            return cli_paths[name]
        # After install, return install_then_found for the CLI being installed
        if install_then_found and find_call_count[name] > 1:
            return install_then_found
        return None

    # Mock subprocess.run for both install and --version/--help
    def mock_subprocess_run(cmd, **kwargs):
        result = mock.MagicMock()
        if kwargs.get("shell"):
            # Install command
            result.returncode = 0 if install_succeeds else 1
            result.stdout = ""
            result.stderr = ""
        else:
            # CLI test (--version or --help)
            result.returncode = version_returncode
            result.stdout = version_output
            result.stderr = ""
        return result

    # Mock npm availability
    def mock_shutil_which(cmd):
        if cmd == "npm":
            return "/usr/bin/npm" if npm_available else None
        return cli_paths.get(cmd)

    # Capture console output
    printed = []

    def capture_print(*args, **kwargs):
        printed.append(" ".join(str(a) for a in args))

    # Apply mocks
    with mock.patch("pdd.cli_detector._find_cli_binary", side_effect=mock_find_cli_binary), \
         mock.patch("pdd.cli_detector.console") as mock_console, \
         mock.patch("subprocess.run", side_effect=mock_subprocess_run), \
         mock.patch("shutil.which", side_effect=mock_shutil_which), \
         mock.patch("pdd.setup_tool._print_step_banner"):

        mock_console.print.side_effect = capture_print
        results = detect_and_bootstrap_cli()

    output = "\n".join(printed)
    return output, results


# ---------------------------------------------------------------------------
# Helper: capture output from detect_cli_tools
# ---------------------------------------------------------------------------

def _run_legacy_capture(
    monkeypatch,
    cli_paths: dict[str, str] | None = None,
    env_keys: dict[str, str] | None = None,
) -> str:
    """Run detect_cli_tools with mocked boundaries, return captured output."""
    cli_paths = cli_paths or {}
    env_keys = env_keys or {}

    for var in ("ANTHROPIC_API_KEY", "OPENAI_API_KEY", "GOOGLE_API_KEY",
                "GEMINI_API_KEY"):
        monkeypatch.delenv(var, raising=False)
    for k, v in env_keys.items():
        monkeypatch.setenv(k, v)

    def mock_which(cmd):
        return cli_paths.get(cmd)

    printed = []

    def capture_print(*args, **kwargs):
        printed.append(" ".join(str(a) for a in args))

    with mock.patch("pdd.cli_detector._which", side_effect=mock_which), \
         mock.patch("pdd.cli_detector.console") as mock_console, \
         mock.patch("pdd.cli_detector._npm_available", return_value=False):
        mock_console.print.side_effect = capture_print
        detect_cli_tools()

    return "\n".join(printed)


# ===================================================================
# 1. CliBootstrapResult data model
# ===================================================================


class TestCliBootstrapResult:
    """Pure contract tests for the result dataclass."""

    def test_defaults_to_empty(self):
        r = CliBootstrapResult()
        assert r.cli_name == ""
        assert r.provider == ""
        assert r.cli_path == ""
        assert r.api_key_configured is False
        assert r.skipped is False

    def test_skipped_result(self):
        r = CliBootstrapResult(skipped=True)
        assert r.skipped is True
        assert r.cli_name == ""

    def test_populated_result(self):
        r = CliBootstrapResult(
            cli_name="claude", provider="anthropic",
            cli_path="/usr/local/bin/claude", api_key_configured=True,
        )
        assert r.cli_name == "claude"
        assert r.provider == "anthropic"
        assert r.cli_path == "/usr/local/bin/claude"
        assert r.api_key_configured is True
        assert r.skipped is False


# ===================================================================
# 2. detect_and_bootstrap_cli — Selection table & input parsing
# ===================================================================


class TestBootstrapSelectionTable:
    """Tests for the numbered table display and user input parsing."""

    def test_table_shows_all_three_clis(self, monkeypatch, tmp_path):
        output, _ = _run_bootstrap_capture(
            monkeypatch, tmp_path, ["1"],
            cli_paths=CLAUDE_ONLY, env_keys=CLAUDE_KEY,
        )
        assert "Claude CLI" in output
        assert "Codex CLI" in output
        assert "Gemini CLI" in output

    def test_table_shows_install_and_key_status(self, monkeypatch, tmp_path):
        output, _ = _run_bootstrap_capture(
            monkeypatch, tmp_path, ["1"],
            cli_paths=CLAUDE_ONLY, env_keys=CLAUDE_KEY,
        )
        # Claude is installed with key
        assert "Found at" in output
        assert "ANTHROPIC_API_KEY" in output
        # Others are not installed
        assert "Not found" in output

    def test_select_single_cli(self, monkeypatch, tmp_path):
        _, results = _run_bootstrap_capture(
            monkeypatch, tmp_path, ["1"],
            cli_paths=CLAUDE_ONLY, env_keys=CLAUDE_KEY,
        )
        assert len(results) == 1
        assert results[0].cli_name == "claude"
        assert results[0].provider == "anthropic"
        assert results[0].api_key_configured is True

    def test_multi_select_comma_separated(self, monkeypatch, tmp_path):
        _, results = _run_bootstrap_capture(
            monkeypatch, tmp_path, ["1,3"],
            cli_paths=ALL_INSTALLED, env_keys=ALL_KEYS,
        )
        assert len(results) == 2
        assert results[0].cli_name == "claude"
        assert results[1].cli_name == "gemini"

    def test_multi_select_with_spaces(self, monkeypatch, tmp_path):
        _, results = _run_bootstrap_capture(
            monkeypatch, tmp_path, ["1, 3"],
            cli_paths=ALL_INSTALLED, env_keys=ALL_KEYS,
        )
        assert len(results) == 2
        assert results[0].cli_name == "claude"
        assert results[1].cli_name == "gemini"

    def test_duplicate_input_deduplicated(self, monkeypatch, tmp_path):
        _, results = _run_bootstrap_capture(
            monkeypatch, tmp_path, ["1,1,3"],
            cli_paths=ALL_INSTALLED, env_keys=ALL_KEYS,
        )
        assert len(results) == 2
        assert results[0].cli_name == "claude"
        assert results[1].cli_name == "gemini"

    def test_empty_input_defaults_to_installed_with_key(self, monkeypatch, tmp_path):
        """Empty input → default to first CLI that is installed AND has a key."""
        output, results = _run_bootstrap_capture(
            monkeypatch, tmp_path, [""],
            cli_paths={"gemini": "/usr/bin/gemini"},
            env_keys={"GEMINI_API_KEY": "gm-test"},
        )
        assert len(results) == 1
        assert results[0].cli_name == "gemini"
        assert "Defaulting" in output

    def test_empty_input_defaults_to_installed_when_no_keys(self, monkeypatch, tmp_path):
        """No keys set → default to first installed CLI."""
        output, results = _run_bootstrap_capture(
            monkeypatch, tmp_path, ["", ""],  # selection + key prompt skip
            cli_paths={"codex": "/usr/bin/codex"},
        )
        assert len(results) == 1
        assert results[0].cli_name == "codex"

    def test_invalid_input_falls_back_to_default(self, monkeypatch, tmp_path):
        output, results = _run_bootstrap_capture(
            monkeypatch, tmp_path, ["xyz"],
            cli_paths=CLAUDE_ONLY, env_keys=CLAUDE_KEY,
        )
        assert len(results) == 1
        assert "Invalid input" in output or "Defaulting" in output

    @pytest.mark.parametrize("quit_input", ["q", "n"])
    def test_quit_returns_skipped(self, monkeypatch, tmp_path, quit_input):
        _, results = _run_bootstrap_capture(
            monkeypatch, tmp_path, [quit_input],
            cli_paths=CLAUDE_ONLY, env_keys=CLAUDE_KEY,
        )
        assert len(results) == 1
        assert results[0].skipped is True


# ===================================================================
# 3. detect_and_bootstrap_cli — Install flow
# ===================================================================


class TestBootstrapInstallFlow:
    """Tests for CLI installation behavior."""

    def test_installed_cli_skips_install_prompt(self, monkeypatch, tmp_path):
        """If CLI is already found, no install prompt is shown."""
        output, results = _run_bootstrap_capture(
            monkeypatch, tmp_path, ["1"],
            cli_paths=CLAUDE_ONLY, env_keys=CLAUDE_KEY,
        )
        assert results[0].cli_name == "claude"
        assert "Install now?" not in output

    def test_not_installed_user_accepts_npm_succeeds(self, monkeypatch, tmp_path):
        """User accepts install, npm present, install succeeds."""
        _, results = _run_bootstrap_capture(
            monkeypatch, tmp_path,
            ["1", "y", ""],  # select, accept install, skip key
            npm_available=True,
            install_succeeds=True,
            install_then_found="/usr/local/bin/claude",
        )
        assert len(results) == 1
        assert results[0].cli_name == "claude"
        assert results[0].cli_path == "/usr/local/bin/claude"
        assert results[0].skipped is False

    def test_not_installed_npm_missing(self, monkeypatch, tmp_path):
        """User accepts install but npm is not available."""
        output, results = _run_bootstrap_capture(
            monkeypatch, tmp_path,
            ["1", "y"],  # select, accept install
            npm_available=False,
        )
        assert results[0].skipped is True
        assert "npm" in output.lower()

    def test_not_installed_install_fails(self, monkeypatch, tmp_path):
        """Install command exits non-zero."""
        output, results = _run_bootstrap_capture(
            monkeypatch, tmp_path,
            ["1", "y"],  # select, accept install
            npm_available=True,
            install_succeeds=False,
        )
        assert results[0].skipped is True
        assert "failed" in output.lower() or "manually" in output.lower()

    def test_not_installed_user_declines(self, monkeypatch, tmp_path):
        """User declines install."""
        output, results = _run_bootstrap_capture(
            monkeypatch, tmp_path,
            ["1", "n"],  # select, decline install
        )
        assert results[0].skipped is True
        assert "not configured" in output.lower()

    def test_install_succeeds_but_binary_not_found(self, monkeypatch, tmp_path):
        """Install exits 0 but binary still not on PATH."""
        output, results = _run_bootstrap_capture(
            monkeypatch, tmp_path,
            ["1", "y"],  # select, accept install
            npm_available=True,
            install_succeeds=True,
            install_then_found=None,  # not found after install
        )
        assert results[0].skipped is True
        assert "not found on PATH" in output or "not configured" in output.lower()


# ===================================================================
# 4. detect_and_bootstrap_cli — API key flow
# ===================================================================


class TestBootstrapApiKeyFlow:
    """Tests for API key configuration behavior."""

    def test_key_already_set_skips_prompt(self, monkeypatch, tmp_path):
        """If key is already in env, no prompt for it."""
        output, results = _run_bootstrap_capture(
            monkeypatch, tmp_path, ["1"],
            cli_paths=CLAUDE_ONLY, env_keys=CLAUDE_KEY,
        )
        assert results[0].api_key_configured is True
        assert "Enter your" not in output

    def test_key_not_set_user_provides(self, monkeypatch, tmp_path):
        """User provides key when prompted."""
        _, results = _run_bootstrap_capture(
            monkeypatch, tmp_path,
            ["1", "sk-new-key"],  # select, provide key
            cli_paths=CLAUDE_ONLY,
        )
        assert results[0].api_key_configured is True
        assert os.environ.get("ANTHROPIC_API_KEY") == "sk-new-key"

    def test_key_saved_to_file(self, monkeypatch, tmp_path):
        """Provided key is written to ~/.pdd/api-env.bash."""
        _run_bootstrap_capture(
            monkeypatch, tmp_path,
            ["1", "sk-saved-key"],
            cli_paths=CLAUDE_ONLY,
        )
        api_env = tmp_path / ".pdd" / "api-env.bash"
        assert api_env.exists()
        content = api_env.read_text()
        assert "export ANTHROPIC_API_KEY=sk-saved-key" in content

    def test_source_line_added_to_rc(self, monkeypatch, tmp_path):
        """Source line is added to ~/.bashrc."""
        _run_bootstrap_capture(
            monkeypatch, tmp_path,
            ["1", "sk-test"],
            cli_paths=CLAUDE_ONLY,
        )
        rc_content = (tmp_path / ".bashrc").read_text()
        api_env_path = str(tmp_path / ".pdd" / "api-env.bash")
        assert f"source {api_env_path}" in rc_content

    def test_key_not_set_user_skips(self, monkeypatch, tmp_path):
        """User presses Enter to skip key."""
        _, results = _run_bootstrap_capture(
            monkeypatch, tmp_path,
            ["1", ""],  # select, skip key
            cli_paths=CLAUDE_ONLY,
        )
        assert results[0].api_key_configured is False

    def test_anthropic_skip_shows_subscription_note(self, monkeypatch, tmp_path):
        """Skipping Anthropic key mentions subscription auth."""
        output, _ = _run_bootstrap_capture(
            monkeypatch, tmp_path,
            ["1", ""],  # select, skip key
            cli_paths=CLAUDE_ONLY,
        )
        assert "subscription" in output.lower()

    def test_non_anthropic_skip_shows_limited_note(self, monkeypatch, tmp_path):
        """Skipping non-Anthropic key mentions limited functionality."""
        output, _ = _run_bootstrap_capture(
            monkeypatch, tmp_path,
            ["2", ""],  # select codex, skip key
            cli_paths={"codex": "/usr/bin/codex"},
        )
        assert "limited functionality" in output.lower()

    def test_google_checks_gemini_key(self, monkeypatch, tmp_path):
        """Google provider recognizes GEMINI_API_KEY."""
        _, results = _run_bootstrap_capture(
            monkeypatch, tmp_path, ["3"],
            cli_paths={"gemini": "/usr/bin/gemini"},
            env_keys={"GEMINI_API_KEY": "gm-test"},
        )
        assert results[0].api_key_configured is True

    def test_google_checks_google_api_key(self, monkeypatch, tmp_path):
        """Google provider recognizes GOOGLE_API_KEY."""
        _, results = _run_bootstrap_capture(
            monkeypatch, tmp_path, ["3"],
            cli_paths={"gemini": "/usr/bin/gemini"},
            env_keys={"GOOGLE_API_KEY": "gm-test"},
        )
        assert results[0].api_key_configured is True


# ===================================================================
# 5. detect_and_bootstrap_cli — CLI test step
# ===================================================================


class TestBootstrapCliTest:
    """Tests for the forced CLI verification step."""

    def test_cli_test_runs_after_setup(self, monkeypatch, tmp_path):
        """CLI test always runs, output includes version info."""
        output, _ = _run_bootstrap_capture(
            monkeypatch, tmp_path, ["1"],
            cli_paths=CLAUDE_ONLY, env_keys=CLAUDE_KEY,
            version_output="2.5.0",
        )
        assert "Testing" in output
        assert "2.5.0" in output or "version" in output.lower()


# ===================================================================
# 6. detect_and_bootstrap_cli — Interrupt handling
# ===================================================================


class TestBootstrapInterrupts:
    """Tests for graceful interrupt handling."""

    def test_keyboard_interrupt_on_selection(self, monkeypatch, tmp_path):
        """KeyboardInterrupt at selection prompt → skipped result."""
        for var in ("ANTHROPIC_API_KEY", "OPENAI_API_KEY", "GOOGLE_API_KEY",
                     "GEMINI_API_KEY"):
            monkeypatch.delenv(var, raising=False)
        monkeypatch.setenv("SHELL", "/bin/bash")
        monkeypatch.setattr(Path, "home", staticmethod(lambda: tmp_path))

        monkeypatch.setattr(
            "pdd.cli_detector._prompt_input",
            mock.MagicMock(side_effect=KeyboardInterrupt),
        )

        with mock.patch("pdd.cli_detector._find_cli_binary", return_value=None), \
             mock.patch("pdd.cli_detector.console"), \
             mock.patch("pdd.setup_tool._print_step_banner"):
            results = detect_and_bootstrap_cli()

        assert len(results) == 1
        assert results[0].skipped is True

    def test_eof_on_selection(self, monkeypatch, tmp_path):
        """EOFError at selection prompt → skipped result."""
        for var in ("ANTHROPIC_API_KEY", "OPENAI_API_KEY", "GOOGLE_API_KEY",
                     "GEMINI_API_KEY"):
            monkeypatch.delenv(var, raising=False)
        monkeypatch.setenv("SHELL", "/bin/bash")
        monkeypatch.setattr(Path, "home", staticmethod(lambda: tmp_path))

        monkeypatch.setattr(
            "pdd.cli_detector._prompt_input",
            mock.MagicMock(side_effect=EOFError),
        )

        with mock.patch("pdd.cli_detector._find_cli_binary", return_value=None), \
             mock.patch("pdd.cli_detector.console"), \
             mock.patch("pdd.setup_tool._print_step_banner"):
            results = detect_and_bootstrap_cli()

        assert len(results) == 1
        assert results[0].skipped is True


# ===================================================================
# 7. detect_and_bootstrap_cli — API key persistence (shell variants)
# ===================================================================


class TestApiKeyPersistence:
    """Tests for key file format across shell types."""

    def test_fish_shell_syntax(self, monkeypatch, tmp_path):
        """Fish shell uses set -gx and fish source syntax."""
        monkeypatch.setenv("SHELL", "/usr/bin/fish")
        monkeypatch.setattr(Path, "home", staticmethod(lambda: tmp_path))

        # Create fish config
        fish_config = tmp_path / ".config" / "fish" / "config.fish"
        fish_config.parent.mkdir(parents=True)
        fish_config.write_text("")

        for var in ("ANTHROPIC_API_KEY", "OPENAI_API_KEY", "GOOGLE_API_KEY",
                     "GEMINI_API_KEY"):
            monkeypatch.delenv(var, raising=False)

        input_iter = iter(["1", "sk-fish-key"])
        monkeypatch.setattr(
            "pdd.cli_detector._prompt_input",
            lambda _prompt="": next(input_iter),
        )

        with mock.patch("pdd.cli_detector._find_cli_binary") as mock_find, \
             mock.patch("pdd.cli_detector.console"), \
             mock.patch("subprocess.run") as mock_run, \
             mock.patch("shutil.which", return_value=None), \
             mock.patch("pdd.setup_tool._print_step_banner"):
            mock_find.side_effect = lambda n: "/usr/bin/claude" if n == "claude" else None
            mock_run.return_value = mock.MagicMock(returncode=0, stdout="1.0", stderr="")
            detect_and_bootstrap_cli()

        api_env = tmp_path / ".pdd" / "api-env.fish"
        assert api_env.exists()
        content = api_env.read_text()
        assert "set -gx ANTHROPIC_API_KEY sk-fish-key" in content

        rc_content = fish_config.read_text()
        assert "test -f" in rc_content
        assert "and source" in rc_content

    def test_duplicate_key_deduplicated(self, monkeypatch, tmp_path):
        """Saving the same key twice doesn't create duplicate lines."""
        monkeypatch.setenv("SHELL", "/bin/bash")
        monkeypatch.setattr(Path, "home", staticmethod(lambda: tmp_path))
        (tmp_path / ".bashrc").write_text("")

        for var in ("ANTHROPIC_API_KEY", "OPENAI_API_KEY", "GOOGLE_API_KEY",
                     "GEMINI_API_KEY"):
            monkeypatch.delenv(var, raising=False)

        # First save
        input_iter = iter(["1", "sk-first"])
        monkeypatch.setattr(
            "pdd.cli_detector._prompt_input",
            lambda _prompt="": next(input_iter),
        )
        with mock.patch("pdd.cli_detector._find_cli_binary") as mock_find, \
             mock.patch("pdd.cli_detector.console"), \
             mock.patch("subprocess.run") as mock_run, \
             mock.patch("shutil.which", return_value=None), \
             mock.patch("pdd.setup_tool._print_step_banner"):
            mock_find.side_effect = lambda n: "/usr/bin/claude" if n == "claude" else None
            mock_run.return_value = mock.MagicMock(returncode=0, stdout="1.0", stderr="")
            detect_and_bootstrap_cli()

        # Second save (overwrite key)
        monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
        input_iter2 = iter(["1", "sk-second"])
        monkeypatch.setattr(
            "pdd.cli_detector._prompt_input",
            lambda _prompt="": next(input_iter2),
        )
        with mock.patch("pdd.cli_detector._find_cli_binary") as mock_find, \
             mock.patch("pdd.cli_detector.console"), \
             mock.patch("subprocess.run") as mock_run, \
             mock.patch("shutil.which", return_value=None), \
             mock.patch("pdd.setup_tool._print_step_banner"):
            mock_find.side_effect = lambda n: "/usr/bin/claude" if n == "claude" else None
            mock_run.return_value = mock.MagicMock(returncode=0, stdout="1.0", stderr="")
            detect_and_bootstrap_cli()

        api_env = tmp_path / ".pdd" / "api-env.bash"
        content = api_env.read_text()
        # Should have only one export line for ANTHROPIC_API_KEY
        export_lines = [l for l in content.splitlines()
                        if "ANTHROPIC_API_KEY" in l]
        assert len(export_lines) == 1
        assert "sk-second" in export_lines[0]


# ===================================================================
# 8. detect_cli_tools — Legacy detection
# ===================================================================


class TestDetectCliToolsLegacy:
    """Tests for the legacy detect_cli_tools function."""

    def test_shows_header(self, monkeypatch):
        output = _run_legacy_capture(monkeypatch)
        assert "Agentic CLI Tool Detection" in output
        assert "pdd fix" in output

    def test_found_cli_shows_checkmark_and_path(self, monkeypatch):
        output = _run_legacy_capture(
            monkeypatch,
            cli_paths={"claude": "/usr/local/bin/claude"},
            env_keys=CLAUDE_KEY,
        )
        assert "Claude CLI" in output
        assert "Found at" in output or "/usr/local/bin/claude" in output

    def test_missing_cli_shows_not_found(self, monkeypatch):
        output = _run_legacy_capture(monkeypatch)
        assert "Not found" in output

    def test_key_set_but_cli_missing_suggests_install(self, monkeypatch):
        output = _run_legacy_capture(
            monkeypatch,
            env_keys={"OPENAI_API_KEY": "sk-test"},
        )
        assert "OPENAI_API_KEY" in output
        assert "not installed" in output.lower() or "install" in output.lower()

    def test_all_installed_with_keys_shows_success(self, monkeypatch):
        output = _run_legacy_capture(
            monkeypatch,
            cli_paths=ALL_INSTALLED,
            env_keys=ALL_KEYS,
        )
        assert "All CLI tools" in output

    def test_no_clis_found_shows_quick_start(self, monkeypatch):
        output = _run_legacy_capture(monkeypatch)
        assert "No CLI tools found" in output or "Quick start" in output
