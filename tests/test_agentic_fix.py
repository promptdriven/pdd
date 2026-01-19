import os
import shutil
from pathlib import Path
from unittest.mock import patch, MagicMock

import pandas as pd
import pytest

from pdd.agentic_fix import (
    run_agentic_fix,
    _verify_and_log,
    _is_suspicious_path,
    _extract_files_from_output,
    _apply_file_map,
)


def _df():
    return pd.DataFrame(
        [
            {"provider": "anthropic", "model": "claude-3",   "api_key": "ANTHROPIC_API_KEY"},
            {"provider": "google",    "model": "gemini-pro", "api_key": "GOOGLE_API_KEY"},
            {"provider": "openai",    "model": "gpt-4",      "api_key": "OPENAI_API_KEY"},
        ]
    )


def _prep_files(tmp_path: Path):
    prompt = tmp_path / "prompt.txt"
    code   = tmp_path / "buggy.py"
    testf  = tmp_path / "test_file.py"
    err    = tmp_path / "error.log"
    prompt.write_text("prompt", encoding="utf-8")
    code.write_text("print('bug')\n", encoding="utf-8")
    testf.write_text("assert True\n", encoding="utf-8")
    err.write_text("", encoding="utf-8")
    return str(prompt), str(code), str(testf), str(err)


@pytest.fixture
def patch_env(monkeypatch):
    monkeypatch.setenv("PDD_PATH", ".")
    monkeypatch.setenv("ANTHROPIC_API_KEY", "x")
    monkeypatch.setenv("GOOGLE_API_KEY", "x")
    monkeypatch.setenv("OPENAI_API_KEY", "x")
    monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", "quiet")


def test_run_agentic_fix_success_via_harvest(monkeypatch, tmp_path, patch_env):
    p_prompt, p_code, p_test, p_err = _prep_files(tmp_path)

    # Force model CSV to our in-test DF
    monkeypatch.setattr("pdd.agentic_fix._load_model_data", lambda _: _df())

    # Minimal prompt template (we just need .format(...) to succeed)
    monkeypatch.setattr(
        "pdd.agentic_fix.load_prompt_template",
        lambda name: "{code_abs}{test_abs}{begin}{end}{prompt_content}{code_content}{test_content}{error_content}",
    )

    # Pretend CLIs exist so selection proceeds
    monkeypatch.setattr("pdd.agentic_fix._find_cli_binary", lambda name, config=None: "/usr/bin/shim")

    # Mock variant runners to return success without making real calls
    mock_result = MagicMock(returncode=0, stdout="", stderr="")
    monkeypatch.setattr("pdd.agentic_fix._run_anthropic_variants", lambda *a, **k: mock_result)
    monkeypatch.setattr("pdd.agentic_fix._run_google_variants", lambda *a, **k: mock_result)
    monkeypatch.setattr("pdd.agentic_fix._run_openai_variants", lambda *a, **k: mock_result)

    # Short-circuit harvest path to succeed — NOTE: uses leading underscore (private function)
    monkeypatch.setattr("pdd.agentic_fix._try_harvest_then_verify", lambda *a, **k: True)

    ok, msg, cost, model, changed_files = run_agentic_fix(
        p_prompt, p_code, p_test, p_err, cwd=tmp_path
    )
    assert ok is True
    assert isinstance(changed_files, list)
    assert "successful" in msg.lower()
    assert cost > 0.0
    assert model.startswith("agentic-")


def test_run_agentic_fix_handles_no_keys(monkeypatch, tmp_path):
    p_prompt, p_code, p_test, p_err = _prep_files(tmp_path)
    # Force model CSV to in-test DF
    monkeypatch.setattr("pdd.agentic_fix._load_model_data", lambda _: _df())

    # Remove all relevant keys
    monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
    monkeypatch.delenv("GEMINI_API_KEY", raising=False)
    monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)

    # Also hide Claude CLI so subscription auth isn't detected
    monkeypatch.setattr("pdd.agentic_fix._find_cli_binary", lambda name, config=None: None)

    ok, msg, cost, model, changed_files = run_agentic_fix(
        prompt_file=str(p_prompt),
        code_file=str(p_code),
        unit_test_file=str(p_test),
        error_log_file=str(p_err),
        cwd=tmp_path,
    )
    assert isinstance(changed_files, list)
    assert ok is False
    assert "No configured agent API keys" in msg


AGENTS = [
    ("anthropic", "ANTHROPIC_API_KEY", "claude"),
    ("google",    "GOOGLE_API_KEY",    "gemini"),  # allow GEMINI_API_KEY alias
    ("openai",    "OPENAI_API_KEY",    "codex"),
]


def _has_cli(cmd: str) -> bool:
    return shutil.which(cmd) is not None


def _mk_files(tmp_path: Path):
    p_prompt = tmp_path / "prompt.txt"
    p_code   = tmp_path / "buggy.py"
    p_test   = tmp_path / "test_dummy.py"
    p_err    = tmp_path / "error.log"
    p_prompt.write_text("Generate a simple function.", encoding="utf-8")
    p_code.write_text("def f():\n    return 1/0\n", encoding="utf-8")
    p_test.write_text("def test_ok(): assert True\n", encoding="utf-8")
    p_err.write_text("ZeroDivisionError", encoding="utf-8")
    return p_prompt, p_code, p_test, p_err


@pytest.mark.parametrize("provider,env_key,cli", AGENTS)
def test_run_agentic_fix_real_call_when_available(provider, env_key, cli, tmp_path, monkeypatch):
    # Only run if API key (or Gemini alias for Google) + CLI are present
    detected_key = os.getenv(env_key)
    if provider == "google" and not detected_key:
        detected_key = os.getenv("GEMINI_API_KEY")

    if not detected_key or not _has_cli(cli):
        pytest.skip(f"{provider} not available (missing API key and/or '{cli}' CLI).")

    # Ensure the model CSV used by the code matches our expected env var names
    monkeypatch.setattr("pdd.agentic_fix._load_model_data", lambda _: _df())

    # Prefer only this provider: drop others
    for k in ("ANTHROPIC_API_KEY", "GOOGLE_API_KEY", "GEMINI_API_KEY", "OPENAI_API_KEY"):
        if k != env_key:
            monkeypatch.delenv(k, raising=False)

    # For non-anthropic providers, hide Claude CLI so subscription auth isn't used
    if provider != "anthropic":
        from pdd.agentic_common import _find_cli_binary as original_find
        monkeypatch.setattr("pdd.agentic_fix._find_cli_binary", lambda name, config=None: None if name == "claude" else original_find(name, config))

    # Re-apply the cached key to the env var our CSV expects
    if provider == "google":
        monkeypatch.setenv("GOOGLE_API_KEY", detected_key)
    else:
        monkeypatch.setenv(env_key, detected_key)

    monkeypatch.setenv("PDD_PATH", ".")
    # Keep local verification off (agents may run on remote infra)
    monkeypatch.setenv("PDD_AGENTIC_VERIFY", "0")
    monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", "quiet")
    # Note: PDD_AGENTIC_TIMEOUT removed - timeout now configured via --timeout-adder CLI option
    monkeypatch.setenv("PDD_AGENTIC_VERIFY_TIMEOUT", "60")

    p_prompt, p_code, p_test, p_err = _mk_files(tmp_path)

    ok, msg, cost, model, changed_files = run_agentic_fix(
        prompt_file=str(p_prompt),
        code_file=str(p_code),
        unit_test_file=str(p_test),
        error_log_file=str(p_err),
        cwd=tmp_path,
    )
    assert isinstance(changed_files, list)

    # Don't require success; just verify the chosen agent tag
    assert model.startswith(f"agentic-{provider}")


# --- Tests for _verify_and_log with run_command ---

class TestVerifyAndLog:
    """Tests for _verify_and_log function using run_command from language_format.csv."""

    def test_verify_and_log_disabled(self, tmp_path):
        """When verification is disabled, should return True immediately."""
        test_file = tmp_path / "test.py"
        test_file.write_text("raise Exception('fail')")

        result = _verify_and_log(str(test_file), tmp_path, verify_cmd=None, enabled=False)
        assert result is True

    def test_verify_and_log_with_verify_cmd(self, tmp_path):
        """When verify_cmd is provided, should use it instead of run_command."""
        test_file = tmp_path / "test.py"
        test_file.write_text("print('hello')")

        # Use a command that will succeed
        result = _verify_and_log(
            str(test_file),
            tmp_path,
            verify_cmd="echo 'success'",
            enabled=True
        )
        assert result is True

    def test_verify_and_log_uses_run_command_for_python(self, tmp_path, monkeypatch):
        """Should use python run command from CSV for .py files."""
        # Set up PDD_PATH to point to actual data directory
        monkeypatch.setenv("PDD_PATH", str(Path(__file__).parent.parent))

        test_file = tmp_path / "example.py"
        test_file.write_text("print('success')\n")

        result = _verify_and_log(str(test_file), tmp_path, verify_cmd=None, enabled=True)
        assert result is True

    def test_verify_and_log_detects_failure(self, tmp_path, monkeypatch):
        """Should detect when script exits with non-zero code."""
        monkeypatch.setenv("PDD_PATH", str(Path(__file__).parent.parent))

        test_file = tmp_path / "failing_example.py"
        test_file.write_text("import sys; sys.exit(1)\n")

        result = _verify_and_log(str(test_file), tmp_path, verify_cmd=None, enabled=True)
        assert result is False

    def test_verify_and_log_detects_exception(self, tmp_path, monkeypatch):
        """Should detect when script raises an exception."""
        monkeypatch.setenv("PDD_PATH", str(Path(__file__).parent.parent))

        test_file = tmp_path / "crashing_example.py"
        test_file.write_text("raise ValueError('intentional crash')\n")

        result = _verify_and_log(str(test_file), tmp_path, verify_cmd=None, enabled=True)
        assert result is False

    def test_verify_and_log_with_javascript(self, tmp_path, monkeypatch):
        """Should use node run command for .js files if node is available."""
        monkeypatch.setenv("PDD_PATH", str(Path(__file__).parent.parent / "pdd"))

        # Skip if node is not installed
        if not shutil.which("node"):
            pytest.skip("node not available")

        test_file = tmp_path / "example.js"
        test_file.write_text("console.log('success');\n")

        result = _verify_and_log(str(test_file), tmp_path, verify_cmd=None, enabled=True)
        assert result is True

    def test_verify_and_log_fallback_to_python(self, tmp_path, monkeypatch):
        """Should fallback to Python interpreter when no run_command found."""
        monkeypatch.setenv("PDD_PATH", str(Path(__file__).parent.parent / "pdd"))

        # Mock get_run_command_for_file to return empty string
        with patch("pdd.agentic_fix.get_run_command_for_file", return_value=""):
            test_file = tmp_path / "example.py"
            test_file.write_text("print('fallback works')\n")

            result = _verify_and_log(str(test_file), tmp_path, verify_cmd=None, enabled=True)
            assert result is True


# --- Tests for agentic mode invocation (TDD: should fail until code is fixed) ---

class TestAgenticModeInvocation:
    """
    Tests verifying agents are invoked with full file access, not completion mode.

    These tests check that:
    1. Claude is NOT invoked with -p flag (which prevents file tool access)
    2. Codex is NOT invoked with --sandbox read-only (which prevents file writes)
    3. Gemini is NOT invoked with -p flag (which prevents tool access)

    These tests should FAIL initially (RED phase) and PASS after the fix (GREEN phase).
    """

    @pytest.fixture
    def mock_subprocess_run(self):
        """Mock subprocess.run to capture CLI commands without executing them."""
        with patch('pdd.agentic_fix.subprocess.run') as mock_run:
            mock_run.return_value = MagicMock(
                returncode=0,
                stdout="<<<BEGIN_FILE:test.py>>>fixed<<<END_FILE:test.py>>>",
                stderr=""
            )
            yield mock_run

    def test_claude_not_in_completion_mode(self, mock_subprocess_run, tmp_path):
        """
        Claude should NOT use -p/--print flag with full prompt - it prevents file tool access.

        Current (buggy): ["claude", "-p", "--dangerously-skip-permissions", <full_prompt>]
        Expected: Claude invoked without -p, so it can use file tools in agentic mode

        When -p (print mode) is used, Claude runs in completion mode and cannot use
        file tools like Read, Write, Edit, etc. For agentic fix to work, we need
        Claude to have full file access.
        """
        from pdd.agentic_fix import _run_anthropic_variants

        # Call the function with a long prompt (simulating real usage)
        long_prompt = "Fix this code: " + "x" * 1000  # Simulate a real prompt
        _run_anthropic_variants(long_prompt, tmp_path, 60, "test")

        # Get the command that was called
        assert mock_subprocess_run.called, "subprocess.run should have been called"
        call_args = mock_subprocess_run.call_args[0][0]

        # -p flag is a boolean flag (print mode), NOT an option with a value
        # Command structure: claude -p --dangerously-skip-permissions <prompt>
        # The prompt is the LAST argument, not the argument after -p
        has_p_flag = "-p" in call_args or "--print" in call_args

        if has_p_flag:
            # In print mode, the prompt is passed as the last positional argument
            # Check if it's a long embedded prompt (bad) vs a short instruction pointing to a file (ok)
            last_arg = call_args[-1]
            assert len(last_arg) < 500, \
                f"Claude in -p mode receives full prompt as argument (got {len(last_arg)} chars); " \
                "this prevents file tool access. Remove -p flag to enable agentic mode."

    def test_codex_not_read_only_sandbox(self, mock_subprocess_run, tmp_path):
        """
        Codex should NOT have --sandbox read-only in any variant definition.

        Current (buggy) variants in code:
        1. ["codex", "exec", full]
        2. ["codex", "exec", "--skip-git-repo-check", full]
        3. ["codex", "exec", "--skip-git-repo-check", "--sandbox", "read-only", full]  <-- BAD

        The third variant uses read-only which prevents file writes.
        This test inspects the source code to verify no variants use read-only.
        """
        import inspect
        from pdd.agentic_fix import _run_openai_variants

        # Get the source code of the function
        source = inspect.getsource(_run_openai_variants)

        # Check that read-only is NOT in the source code
        assert "read-only" not in source.lower(), \
            "Codex variants should not include 'read-only' sandbox; " \
            "agents need write access to modify files"

    def test_gemini_not_in_completion_mode(self, mock_subprocess_run, tmp_path):
        """
        Gemini should NOT use -p flag with full prompt - it may prevent tool access.

        Current (buggy): ["gemini", "-p", <full_prompt>]
        Expected: Gemini invoked without -p, or with -p pointing to a file
        """
        from pdd.agentic_fix import _run_google_variants

        # Call with a long prompt
        long_prompt = "Fix this code: " + "y" * 1000
        _run_google_variants(long_prompt, tmp_path, 60, "test")

        # Get the command that was called
        assert mock_subprocess_run.called, "subprocess.run should have been called"
        call_args = mock_subprocess_run.call_args[0][0]

        # Check: -p flag should NOT be present with a long prompt
        has_p_flag = "-p" in call_args
        if has_p_flag:
            p_index = call_args.index("-p")
            if p_index + 1 < len(call_args):
                prompt_arg = call_args[p_index + 1]
                assert len(prompt_arg) < 500, \
                    f"Gemini should not receive full prompt via -p flag (got {len(prompt_arg)} chars); " \
                    "use file-based prompt to enable agentic mode"


class TestPromptFileHandling:
    """Tests for secure temp prompt file handling to prevent race conditions."""

    @pytest.fixture
    def mock_subprocess_run(self):
        """Mock subprocess.run to capture CLI commands without executing."""
        with patch('pdd.agentic_fix.subprocess.run') as mock_run:
            mock_run.return_value = MagicMock(
                returncode=0, stdout="output", stderr=""
            )
            yield mock_run

    def test_no_hardcoded_prompt_filename(self):
        """
        Static analysis: source should not use hardcoded '.agentic_prompt.txt'.

        Bug: Hardcoded filename causes race conditions in concurrent execution.
        """
        import inspect
        from pdd.agentic_fix import (
            _run_anthropic_variants,
            _run_openai_variants,
            _run_google_variants
        )

        for func in [_run_anthropic_variants, _run_openai_variants, _run_google_variants]:
            source = inspect.getsource(func)
            assert '".agentic_prompt.txt"' not in source, \
                f"{func.__name__}: hardcoded '.agentic_prompt.txt' causes race conditions"

    def test_prompt_file_cleaned_up_after_execution(self, mock_subprocess_run, tmp_path):
        """
        Behavioral: temp prompt files must be deleted after execution.

        Bug: Leaving files on disk exposes sensitive prompt content.
        """
        from pdd.agentic_fix import _run_anthropic_variants

        _run_anthropic_variants("test prompt", tmp_path, 60, "test")

        # No prompt files should remain (any naming pattern)
        remaining = list(tmp_path.glob("*prompt*"))
        assert len(remaining) == 0, \
            f"Temp prompt files should be cleaned up, found: {remaining}"


class TestCwdHandling:
    """
    Tests for working directory handling in run_agentic_fix.

    Bug: run_agentic_fix uses Path.cwd() for path resolution, which fails
    when called from a different directory than where the module files live.

    Example: Running `pdd sync hello` from repo root for examples/hello/ module
    causes paths like "src/hello.py" to resolve to /repo/src/hello.py instead
    of /repo/examples/hello/src/hello.py.
    """

    def test_run_agentic_fix_respects_cwd_parameter(self, tmp_path, monkeypatch):
        """
        Regression test: run_agentic_fix should use passed cwd for path resolution,
        not Path.cwd().

        This test simulates the scenario where:
        - Process cwd is repo root (wrong directory)
        - Module files are in a subdirectory (correct directory)
        - Relative paths should resolve against the module directory
        """
        # Setup two directories - wrong_dir simulates repo root, correct_dir is module
        wrong_dir = tmp_path / "repo_root"
        wrong_dir.mkdir()

        correct_dir = tmp_path / "repo_root" / "examples" / "hello"
        correct_dir.mkdir(parents=True)

        # Create files in correct directory
        src_dir = correct_dir / "src"
        src_dir.mkdir()
        (src_dir / "hello.py").write_text("def hello(): print('hello')")

        tests_dir = correct_dir / "tests"
        tests_dir.mkdir()
        (tests_dir / "test_hello.py").write_text("from hello import hello")

        prompt_file = correct_dir / "hello.prompt"
        prompt_file.write_text("print hello")

        # Create error log in correct dir
        error_log = correct_dir / "error.log"
        error_log.write_text("test error")

        # Set process cwd to WRONG directory (simulates running pdd from repo root)
        monkeypatch.chdir(wrong_dir)

        # Mock dependencies to prevent actual agent calls
        monkeypatch.setattr("pdd.agentic_fix._load_model_data", lambda _: _df())
        monkeypatch.setattr(
            "pdd.agentic_fix.load_prompt_template",
            lambda name: "{code_abs}{test_abs}{begin}{end}{prompt_content}{code_content}{test_content}{error_content}{verify_cmd}",
        )
        monkeypatch.setattr("pdd.agentic_fix._find_cli_binary", lambda name, config=None: "/usr/bin/shim")
        monkeypatch.setenv("OPENAI_API_KEY", "test-key")
        monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", "quiet")

        # Track instruction file creation
        instruction_file_paths = []
        original_write_text = Path.write_text

        def track_write(self, content, *args, **kwargs):
            if "agentic_fix_instructions" in str(self):
                instruction_file_paths.append(str(self))
            return original_write_text(self, content, *args, **kwargs)

        monkeypatch.setattr(Path, "write_text", track_write)

        # Mock agent runners to return success without making real calls
        # With PRIMARY-FIRST logic, we need to mock the primary path functions
        mock_result = MagicMock(returncode=0, stdout="", stderr="")
        monkeypatch.setattr("pdd.agentic_fix._run_anthropic_variants", lambda *a, **k: mock_result)
        monkeypatch.setattr("pdd.agentic_fix._run_google_variants", lambda *a, **k: mock_result)
        monkeypatch.setattr("pdd.agentic_fix._run_openai_variants", lambda *a, **k: mock_result)
        # Also mock harvest fallback
        monkeypatch.setattr("pdd.agentic_fix._try_harvest_then_verify", lambda *a, **k: True)

        # Call with relative paths AND explicit cwd parameter
        ok, msg, cost, model, changed_files = run_agentic_fix(
            prompt_file=str(prompt_file),
            code_file="src/hello.py",
            unit_test_file="tests/test_hello.py",
            error_log_file="error.log",
            cwd=correct_dir,  # NEW: explicit cwd - should resolve paths against this
        )

        # Instruction file should be in correct_dir, not wrong_dir
        assert any(str(correct_dir) in p for p in instruction_file_paths), \
            f"Instruction file should be created in {correct_dir}, but found: {instruction_file_paths}"

        assert not any(str(wrong_dir) + "/agentic" in p for p in instruction_file_paths), \
            f"Instruction file should NOT be in {wrong_dir}"

    def test_run_agentic_fix_resolves_paths_against_cwd(self, tmp_path, monkeypatch):
        """
        Verify that relative code/test paths are resolved against the cwd parameter,
        not against Path.cwd().
        """
        # Setup
        module_dir = tmp_path / "examples" / "hello"
        module_dir.mkdir(parents=True)

        src_dir = module_dir / "src"
        src_dir.mkdir()
        code_file = src_dir / "hello.py"
        code_file.write_text("def hello(): print('hello')")

        tests_dir = module_dir / "tests"
        tests_dir.mkdir()
        test_file = tests_dir / "test_hello.py"
        test_file.write_text("from hello import hello")

        prompt_file = module_dir / "hello.prompt"
        prompt_file.write_text("print hello")

        error_log = module_dir / "error.log"
        error_log.write_text("test error")

        # Set cwd to somewhere else entirely
        other_dir = tmp_path / "other"
        other_dir.mkdir()
        monkeypatch.chdir(other_dir)

        # Mock dependencies
        monkeypatch.setattr("pdd.agentic_fix._load_model_data", lambda _: _df())
        monkeypatch.setenv("OPENAI_API_KEY", "test-key")
        monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", "quiet")

        # Capture the resolved paths used in the instruction template
        captured_template_args = {}
        original_format = str.format

        def capture_format(fmt_string, **kwargs):
            if "code_abs" in kwargs:
                captured_template_args.update(kwargs)
            return original_format(fmt_string, **kwargs)

        monkeypatch.setattr(
            "pdd.agentic_fix.load_prompt_template",
            lambda name: "{code_abs}{test_abs}{begin}{end}{prompt_content}{code_content}{test_content}{error_content}{verify_cmd}",
        )
        monkeypatch.setattr("pdd.agentic_fix._find_cli_binary", lambda name, config=None: "/usr/bin/shim")

        # Mock agent runners to return success without making real calls
        # With PRIMARY-FIRST logic, we need to mock the primary path functions
        mock_result = MagicMock(returncode=0, stdout="", stderr="")
        monkeypatch.setattr("pdd.agentic_fix._run_anthropic_variants", lambda *a, **k: mock_result)
        monkeypatch.setattr("pdd.agentic_fix._run_google_variants", lambda *a, **k: mock_result)
        monkeypatch.setattr("pdd.agentic_fix._run_openai_variants", lambda *a, **k: mock_result)
        monkeypatch.setattr("pdd.agentic_fix._try_harvest_then_verify", lambda *a, **k: True)

        # Call with relative paths and explicit cwd
        run_agentic_fix(
            prompt_file=str(prompt_file),
            code_file="src/hello.py",
            unit_test_file="tests/test_hello.py",
            error_log_file="error.log",
            cwd=module_dir,
        )

        # Check that the instruction file was created in the correct location
        instruction_file = module_dir / "agentic_fix_instructions.txt"
        if instruction_file.exists():
            content = instruction_file.read_text()
            # Paths in content should reference module_dir, not other_dir
            assert str(module_dir / "src" / "hello.py") in content, \
                f"Code path should reference {module_dir}, got: {content[:200]}"
            assert str(other_dir / "src" / "hello.py") not in content, \
                "Code path should NOT reference the process cwd (other_dir)"


class TestSuspiciousPathDetection:
    """Tests for the _is_suspicious_path() function and its integration.

    This tests the defense against LLM artifacts like:
    - Single-character filenames (C, E, T from agent misbehavior)
    - Template variables ({path}, {code_abs}) captured by regex
    """

    def test_single_char_paths_are_suspicious(self):
        """Single character filenames should be rejected."""
        assert _is_suspicious_path("C") is True
        assert _is_suspicious_path("E") is True
        assert _is_suspicious_path("T") is True
        assert _is_suspicious_path("X") is True
        assert _is_suspicious_path("/tmp/C") is True
        assert _is_suspicious_path("./E") is True

    def test_double_char_paths_are_suspicious(self):
        """Double character filenames should also be rejected."""
        assert _is_suspicious_path("ab") is True
        assert _is_suspicious_path("/foo/xy") is True

    def test_template_variables_are_suspicious(self):
        """Template variable patterns like {path} should be rejected."""
        assert _is_suspicious_path("{path}") is True
        assert _is_suspicious_path("{code_abs}") is True
        assert _is_suspicious_path("{test_abs}") is True
        assert _is_suspicious_path("/some/dir/{path}") is True
        assert _is_suspicious_path("file_{name}.py") is True

    def test_dot_only_paths_are_suspicious(self):
        """Paths that are just dots should be rejected."""
        assert _is_suspicious_path("..") is True
        assert _is_suspicious_path("...") is True

    def test_empty_path_is_suspicious(self):
        """Empty paths should be rejected."""
        assert _is_suspicious_path("") is True
        assert _is_suspicious_path(None) is True  # type: ignore

    def test_legitimate_paths_are_not_suspicious(self):
        """Normal file paths should NOT be rejected."""
        assert _is_suspicious_path("hello.py") is False
        assert _is_suspicious_path("src/main.py") is False
        assert _is_suspicious_path("/Users/test/code.py") is False
        assert _is_suspicious_path("test_module.py") is False
        assert _is_suspicious_path("__init__.py") is False
        assert _is_suspicious_path(".gitignore") is False
        assert _is_suspicious_path("Makefile") is False

    def test_three_char_paths_are_allowed(self):
        """Three+ character filenames should be allowed."""
        assert _is_suspicious_path("foo") is False
        assert _is_suspicious_path("bar") is False
        assert _is_suspicious_path("abc") is False


class TestExtractFilesFromOutputWithSuspiciousPathRejection:
    """Tests that _extract_files_from_output rejects suspicious paths."""

    def test_rejects_single_char_paths(self):
        """Should reject single-char paths from LLM output."""
        blob = "<<<BEGIN_FILE:C>>>some content<<<END_FILE:C>>>"
        result = _extract_files_from_output(blob)
        assert "C" not in result
        assert result == {}

    def test_rejects_template_variable_paths(self):
        """Should reject template variable paths like {path}."""
        blob = "<<<BEGIN_FILE:{path}>>>some code<<<END_FILE:{path}>>>"
        result = _extract_files_from_output(blob)
        assert "{path}" not in result
        assert result == {}

    def test_rejects_code_abs_template(self):
        """Should reject {code_abs} template variable."""
        blob = "<<<BEGIN_FILE:{code_abs}>>>def hello(): pass<<<END_FILE:{code_abs}>>>"
        result = _extract_files_from_output(blob)
        assert "{code_abs}" not in result
        assert result == {}

    def test_allows_legitimate_paths(self):
        """Should allow legitimate file paths."""
        blob = "<<<BEGIN_FILE:hello.py>>>def hello(): print('hello')<<<END_FILE:hello.py>>>"
        result = _extract_files_from_output(blob)
        assert "hello.py" in result
        assert "def hello():" in result["hello.py"]

    def test_mixed_paths_filters_suspicious(self):
        """Should filter suspicious paths while keeping legitimate ones."""
        blob = """
        <<<BEGIN_FILE:C>>>bad<<<END_FILE:C>>>
        <<<BEGIN_FILE:hello.py>>>good content<<<END_FILE:hello.py>>>
        <<<BEGIN_FILE:{path}>>>template garbage<<<END_FILE:{path}>>>
        <<<BEGIN_FILE:test_file.py>>>test content<<<END_FILE:test_file.py>>>
        """
        result = _extract_files_from_output(blob)
        assert "C" not in result
        assert "{path}" not in result
        assert "hello.py" in result
        assert "test_file.py" in result
        assert len(result) == 2


class TestBugReplication:
    """Integration tests that replicate the exact bug scenario.

    Bug: When LLM produces malformed output with single-letter file markers like
    <<<BEGIN_FILE:C>>><<<END_FILE:C>>>, the regex captures 'C' as a filename
    and writes a 0-byte file to disk.

    These tests verify the fix prevents this by checking actual file creation.
    """

    def test_suspicious_paths_not_written_to_disk(self, tmp_path):
        """
        INTEGRATION TEST: Verify C, E, T files are NOT created on disk.

        This replicates the exact bug scenario where malformed LLM output
        would result in empty files being created in the working directory.
        """
        # Create a legitimate code file that _apply_file_map expects
        code_file = tmp_path / "hello.py"
        code_file.write_text("# original\n")

        # Simulate the file_map that would be created from malformed LLM output
        # The content is empty string (0 bytes) when markers are on same line:
        # <<<BEGIN_FILE:C>>><<<END_FILE:C>>>
        file_map = {
            "C": "",                              # Would create 0-byte file
            "E": "",                              # Would create 0-byte file
            "T": "",                              # Would create 0-byte file
            "hello.py": "def hello():\n    print('hello')\n",  # Legitimate file
        }

        # Apply the file map (this is where the bug would manifest)
        # Signature: _apply_file_map(file_map, project_root, primary_code_path, allow_new)
        _apply_file_map(file_map, tmp_path, code_file, allow_new=True)

        # CRITICAL ASSERTIONS: These files should NOT exist
        assert not (tmp_path / "C").exists(), "Bug: C file was created on disk"
        assert not (tmp_path / "E").exists(), "Bug: E file was created on disk"
        assert not (tmp_path / "T").exists(), "Bug: T file was created on disk"

        # Legitimate file SHOULD be updated
        assert (tmp_path / "hello.py").exists()
        assert "def hello():" in (tmp_path / "hello.py").read_text()

    def test_template_variables_not_written_to_disk(self, tmp_path):
        """
        INTEGRATION TEST: Verify {path} template files are NOT created.

        Bug scenario: LLM outputs code containing f-string templates like
        <<<BEGIN_FILE:{path}>>> which gets captured as a filename.
        """
        code_file = tmp_path / "hello.py"
        code_file.write_text("# original\n")

        file_map = {
            "{path}": "def _end_marker(path): return f'<<<END_FILE:{path}>>>'",
            "{code_abs}": "some garbage",
            "hello.py": "def hello(): print('hello')\n",
        }

        # Signature: _apply_file_map(file_map, project_root, primary_code_path, allow_new)
        _apply_file_map(file_map, tmp_path, code_file, allow_new=True)

        # These template variable files should NOT exist
        assert not (tmp_path / "{path}").exists(), "Bug: {path} file was created"
        assert not (tmp_path / "{code_abs}").exists(), "Bug: {code_abs} file was created"

        # Legitimate file SHOULD exist
        assert (tmp_path / "hello.py").exists()

    def test_full_extraction_to_disk_pipeline(self, tmp_path):
        """
        END-TO-END TEST: Full pipeline from malformed LLM output to disk.

        Simulates the complete bug scenario:
        1. LLM produces malformed output with C, E, T markers
        2. Regex extracts these as file paths
        3. _apply_file_map attempts to write files
        4. Validation prevents suspicious files from being created
        """
        code_file = tmp_path / "hello.py"
        code_file.write_text("# original\n")

        # Simulate exact malformed LLM output that caused the bug
        malformed_llm_output = """
Here's the fix for the code:

<<<BEGIN_FILE:C>>><<<END_FILE:C>>>
<<<BEGIN_FILE:E>>><<<END_FILE:E>>>
<<<BEGIN_FILE:T>>><<<END_FILE:T>>>

And here's the actual fix:
<<<BEGIN_FILE:hello.py>>>
def hello():
    print("hello, world!")
<<<END_FILE:hello.py>>>
"""

        # Step 1: Extract files from output (this includes suspicious path filtering)
        file_map = _extract_files_from_output(malformed_llm_output)

        # Verify extraction filtering worked
        assert "C" not in file_map
        assert "E" not in file_map
        assert "T" not in file_map
        assert "hello.py" in file_map

        # Step 2: Apply to disk
        # Signature: _apply_file_map(file_map, project_root, primary_code_path, allow_new)
        _apply_file_map(file_map, tmp_path, code_file, allow_new=True)

        # Step 3: Verify disk state
        assert not (tmp_path / "C").exists(), "C file should not exist on disk"
        assert not (tmp_path / "E").exists(), "E file should not exist on disk"
        assert not (tmp_path / "T").exists(), "T file should not exist on disk"
        assert (tmp_path / "hello.py").exists()
        assert "hello, world!" in (tmp_path / "hello.py").read_text()


class TestCliDiscoveryIntegration:
    """
    Integration tests verifying run_agentic_fix uses _find_cli_binary for CLI discovery.

    This ensures Issue #234 is resolved: Claude should be found even when not in PATH
    but installed in common locations like ~/.local/bin or ~/.nvm/versions/node/*/bin/.
    """

    def test_run_agentic_fix_uses_find_cli_binary(self, monkeypatch, tmp_path):
        """
        Verify run_agentic_fix uses _find_cli_binary instead of shutil.which.

        This test ensures the fix for Issue #234 is properly integrated:
        - _find_cli_binary should be called for CLI discovery
        - The discovered path should be used in subprocess calls
        """
        p_prompt, p_code, p_test, p_err = _prep_files(tmp_path)

        # Track _find_cli_binary calls
        find_cli_calls = []

        def mock_find_cli_binary(name, config=None):
            find_cli_calls.append(name)
            # Return a fake path for claude
            if name == "claude":
                return "/home/user/.local/bin/claude"
            return None

        monkeypatch.setattr("pdd.agentic_fix._find_cli_binary", mock_find_cli_binary)

        # Mock other dependencies
        monkeypatch.setattr("pdd.agentic_fix._load_model_data", lambda _: _df())
        monkeypatch.setattr(
            "pdd.agentic_fix.load_prompt_template",
            lambda name: "{code_abs}{test_abs}{begin}{end}{prompt_content}{code_content}{test_content}{error_content}",
        )

        # Clear API keys to force CLI auth detection
        monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
        monkeypatch.delenv("GEMINI_API_KEY", raising=False)
        monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
        monkeypatch.delenv("OPENAI_API_KEY", raising=False)
        monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", "quiet")

        # Short-circuit to avoid actual agent calls
        monkeypatch.setattr("pdd.agentic_fix._try_harvest_then_verify", lambda *a, **k: True)

        run_agentic_fix(p_prompt, p_code, p_test, p_err, cwd=tmp_path)

        # Verify _find_cli_binary was called for claude
        assert "claude" in find_cli_calls, (
            "_find_cli_binary should be called for 'claude' CLI discovery. "
            "If this fails, run_agentic_fix may still be using shutil.which()."
        )

    def test_run_agentic_fix_passes_cli_path_to_variant_runners(self, monkeypatch, tmp_path):
        """
        Verify the discovered CLI path is passed to variant runners.

        This ensures the full path is used in subprocess calls, not just the binary name.
        """
        p_prompt, p_code, p_test, p_err = _prep_files(tmp_path)

        # Track cli_path passed to variant runner
        captured_cli_path = []

        def mock_anthropic_variants(prompt_text, cwd, total_timeout, label, cli_path=None):
            captured_cli_path.append(cli_path)
            return MagicMock(returncode=0, stdout="fixed", stderr="")

        # Return a specific path for claude
        monkeypatch.setattr(
            "pdd.agentic_fix._find_cli_binary",
            lambda name, config=None: "/home/user/.local/bin/claude" if name == "claude" else None
        )
        monkeypatch.setattr("pdd.agentic_fix._run_anthropic_variants", mock_anthropic_variants)

        # Mock other dependencies
        monkeypatch.setattr("pdd.agentic_fix._load_model_data", lambda _: _df())
        monkeypatch.setattr(
            "pdd.agentic_fix.load_prompt_template",
            lambda name: "{code_abs}{test_abs}{begin}{end}{prompt_content}{code_content}{test_content}{error_content}",
        )

        # Use anthropic with CLI auth (no API key)
        monkeypatch.delenv("ANTHROPIC_API_KEY", raising=False)
        monkeypatch.delenv("GEMINI_API_KEY", raising=False)
        monkeypatch.delenv("GOOGLE_API_KEY", raising=False)
        monkeypatch.delenv("OPENAI_API_KEY", raising=False)
        monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", "quiet")

        # Short-circuit verification
        monkeypatch.setattr("pdd.agentic_fix._try_harvest_then_verify", lambda *a, **k: True)

        run_agentic_fix(p_prompt, p_code, p_test, p_err, cwd=tmp_path)

        # Verify cli_path was passed to variant runner
        assert len(captured_cli_path) > 0, "Variant runner should have been called"
        assert captured_cli_path[0] == "/home/user/.local/bin/claude", (
            f"Expected cli_path='/home/user/.local/bin/claude', got '{captured_cli_path[0]}'. "
            "The discovered CLI path should be passed to the variant runner."
        )
