import os
import shutil
from pathlib import Path
from unittest.mock import patch, MagicMock

import pandas as pd
import pytest

from pdd.agentic_fix import (
    run_agentic_fix,
    _verify_and_log,
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


def test_run_agentic_fix_success_via_run_agentic_task(monkeypatch, tmp_path, patch_env):
    p_prompt, p_code, p_test, p_err = _prep_files(tmp_path)

    # Force model CSV to our in-test DF
    monkeypatch.setattr("pdd.agentic_fix._load_model_data", lambda _: _df())

    # Minimal prompt template (we just need .format(...) to succeed)
    monkeypatch.setattr(
        "pdd.agentic_fix.load_prompt_template",
        lambda name: "{code_abs}{test_abs}{prompt_content}{error_content}{verify_cmd}{protect_tests}",
    )

    # Pretend CLIs exist so selection proceeds
    monkeypatch.setattr("pdd.agentic_common._find_cli_binary", lambda name, config=None: "/usr/bin/shim")

    # Mock run_agentic_task to return success
    monkeypatch.setattr(
        "pdd.agentic_fix.run_agentic_task",
        lambda instruction, cwd, verbose, quiet, label, max_retries: (True, "", 0.05, "anthropic")
    )

    # Mock verification to pass
    monkeypatch.setattr("pdd.agentic_fix._verify_and_log", lambda *a, **k: True)

    ok, msg, cost, model, changed_files = run_agentic_fix(
        p_prompt, p_code, p_test, p_err, cwd=tmp_path
    )
    assert ok is True
    assert isinstance(changed_files, list)
    assert "successful" in msg.lower()
    assert cost >= 0.0
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
    monkeypatch.setattr("pdd.agentic_common._find_cli_binary", lambda name, config=None: None)

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
        monkeypatch.setattr("pdd.agentic_common._find_cli_binary", lambda name, config=None: None if name == "claude" else original_find(name, config))

    # Re-apply the cached key to the env var our CSV expects
    if provider == "google":
        monkeypatch.setenv("GOOGLE_API_KEY", detected_key)
    else:
        monkeypatch.setenv(env_key, detected_key)

    monkeypatch.setenv("PDD_PATH", ".")
    # Keep local verification off (agents may run on remote infra)
    monkeypatch.setenv("PDD_AGENTIC_VERIFY", "0")
    monkeypatch.setenv("PDD_AGENTIC_LOGLEVEL", "quiet")
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


class TestCwdHandling:
    """
    Tests for working directory handling in run_agentic_fix.

    Bug: run_agentic_fix uses Path.cwd() for path resolution, which fails
    when called from a different directory than where the module files live.
    """

    def test_run_agentic_fix_respects_cwd_parameter(self, tmp_path, monkeypatch):
        """
        Regression test: run_agentic_fix should use passed cwd for path resolution,
        not Path.cwd().
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
            lambda name: "{code_abs}{test_abs}{prompt_content}{error_content}{verify_cmd}{protect_tests}",
        )
        monkeypatch.setattr("pdd.agentic_common._find_cli_binary", lambda name, config=None: "/usr/bin/shim")
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

        # Mock run_agentic_task to return success
        monkeypatch.setattr(
            "pdd.agentic_fix.run_agentic_task",
            lambda instruction, cwd, verbose, quiet, label, max_retries: (True, "", 0.05, "anthropic")
        )
        # Mock verification to pass
        monkeypatch.setattr("pdd.agentic_fix._verify_and_log", lambda *a, **k: True)

        # Call with relative paths AND explicit cwd parameter
        ok, msg, cost, model, changed_files = run_agentic_fix(
            prompt_file=str(prompt_file),
            code_file="src/hello.py",
            unit_test_file="tests/test_hello.py",
            error_log_file="error.log",
            cwd=correct_dir,
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

        monkeypatch.setattr(
            "pdd.agentic_fix.load_prompt_template",
            lambda name: "{code_abs}{test_abs}{prompt_content}{error_content}{verify_cmd}{protect_tests}",
        )
        monkeypatch.setattr("pdd.agentic_common._find_cli_binary", lambda name, config=None: "/usr/bin/shim")

        # Mock run_agentic_task to return success
        monkeypatch.setattr(
            "pdd.agentic_fix.run_agentic_task",
            lambda instruction, cwd, verbose, quiet, label, max_retries: (True, "", 0.05, "anthropic")
        )
        # Mock verification to pass
        monkeypatch.setattr("pdd.agentic_fix._verify_and_log", lambda *a, **k: True)

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


class TestMtimeChangeDetection:
    """Tests for mtime-based file change detection."""

    def test_detects_new_files(self, tmp_path):
        """Should detect newly created files."""
        from pdd.agentic_fix import _snapshot_mtimes, _detect_mtime_changes

        before = _snapshot_mtimes(tmp_path)

        # Create a new file
        new_file = tmp_path / "new_file.py"
        new_file.write_text("print('hello')\n")

        after = _snapshot_mtimes(tmp_path)
        changes = _detect_mtime_changes(before, after)

        assert any("new_file.py" in c for c in changes)

    def test_detects_modified_files(self, tmp_path):
        """Should detect modified files."""
        from pdd.agentic_fix import _snapshot_mtimes, _detect_mtime_changes
        import time

        existing = tmp_path / "existing.py"
        existing.write_text("original\n")

        before = _snapshot_mtimes(tmp_path)

        # Ensure mtime changes (some filesystems have 1s granularity)
        time.sleep(0.05)
        existing.write_text("modified\n")

        after = _snapshot_mtimes(tmp_path)
        changes = _detect_mtime_changes(before, after)

        assert any("existing.py" in c for c in changes)

    def test_detects_deleted_files(self, tmp_path):
        """Should detect deleted files."""
        from pdd.agentic_fix import _snapshot_mtimes, _detect_mtime_changes

        to_delete = tmp_path / "to_delete.py"
        to_delete.write_text("will be deleted\n")

        before = _snapshot_mtimes(tmp_path)

        to_delete.unlink()

        after = _snapshot_mtimes(tmp_path)
        changes = _detect_mtime_changes(before, after)

        assert any("to_delete.py" in c for c in changes)

    def test_no_changes_when_nothing_happens(self, tmp_path):
        """Should return empty list when no files change."""
        from pdd.agentic_fix import _snapshot_mtimes, _detect_mtime_changes

        existing = tmp_path / "stable.py"
        existing.write_text("stable\n")

        before = _snapshot_mtimes(tmp_path)
        after = _snapshot_mtimes(tmp_path)
        changes = _detect_mtime_changes(before, after)

        assert changes == []
