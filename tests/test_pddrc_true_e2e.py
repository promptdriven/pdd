"""
TRUE end-to-end tests for pddrc config resolution.

These tests use REAL .pddrc files and REAL construct_paths - no mocking of the config layer.
Only the final LLM function is mocked.

These tests should FAIL before the fix, proving they detect the actual bug.
"""
import pytest
from unittest.mock import patch, MagicMock
from pathlib import Path
from click.testing import CliRunner

from pdd import cli


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory for all tests in this module.

    This is required because construct_paths uses PDD_PATH to find the language_format.csv
    file for language detection.
    """
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


class TestPddrcTrueE2E:
    """
    TRUE end-to-end tests - real pddrc files, real construct_paths.
    These tests should FAIL before the fix, proving they detect the actual bug.
    """

    def test_real_pddrc_strength_reaches_generate_test(self, tmp_path, monkeypatch):
        """
        CRITICAL TRUE E2E TEST:
        1. Create real .pddrc with strength: 0.85
        2. Run through REAL construct_paths (not mocked)
        3. Verify generate_test receives 0.85

        This would have caught ALL THREE fix failures because it tests
        the actual data flow, not mocked intermediate states.
        """
        # 1. Create REAL .pddrc file
        pddrc_content = '''version: "1.0"
contexts:
  test-ctx:
    paths: ["**"]
    defaults:
      strength: 0.85
      temperature: 0.65
'''
        (tmp_path / ".pddrc").write_text(pddrc_content)
        (tmp_path / "test.prompt").write_text("test prompt content")
        (tmp_path / "test.py").write_text("# test code")

        monkeypatch.chdir(tmp_path)

        # 2. Only mock the FINAL function - let everything else run for real
        with patch("pdd.cmd_test_main.generate_test") as mock_generate_test:
            mock_generate_test.return_value = ("generated tests", 0.01, "test-model")

            runner = CliRunner()
            result = runner.invoke(cli.cli, [
                "--local",  # Force local execution for unit test
                "--context", "test-ctx",  # Use our test context
                "test",
                "test.prompt",
                "test.py",
                "--output", "test_output.py"
            ], catch_exceptions=False)

            # 3. THE CRITICAL ASSERTION - did pddrc value reach generate_test?
            assert mock_generate_test.called, "generate_test was not called"
            call_kwargs = mock_generate_test.call_args.kwargs

            assert call_kwargs["strength"] == 0.85, \
                f"PDDRC VALUE NOT USED: Expected strength=0.85 from .pddrc, " \
                f"but generate_test received {call_kwargs['strength']}. " \
                f"The pddrc config is being ignored somewhere in the flow!"

            assert call_kwargs["temperature"] == 0.65, \
                f"PDDRC VALUE NOT USED: Expected temperature=0.65, got {call_kwargs['temperature']}"

    def test_cli_strength_overrides_real_pddrc(self, tmp_path, monkeypatch):
        """
        TRUE E2E: CLI --strength should override pddrc strength.
        Uses real pddrc file, real construct_paths.
        """
        pddrc_content = '''version: "1.0"
contexts:
  test-ctx:
    paths: ["**"]
    defaults:
      strength: 0.85
'''
        (tmp_path / ".pddrc").write_text(pddrc_content)
        (tmp_path / "test.prompt").write_text("test prompt")
        (tmp_path / "test.py").write_text("# code")

        monkeypatch.chdir(tmp_path)

        with patch("pdd.cmd_test_main.generate_test") as mock_generate_test:
            mock_generate_test.return_value = ("tests", 0.01, "model")

            runner = CliRunner()
            result = runner.invoke(cli.cli, [
                "--local",  # Force local execution for unit test
                "--context", "test-ctx",
                "--strength", "0.3",  # CLI override
                "test",
                "test.prompt",
                "test.py",
                "--output", "out.py"
            ], catch_exceptions=False)

            call_kwargs = mock_generate_test.call_args.kwargs
            assert call_kwargs["strength"] == 0.3, \
                f"CLI override failed: Expected 0.3, got {call_kwargs['strength']}"

    def test_default_strength_when_no_pddrc_strength(self, tmp_path, monkeypatch):
        """
        TRUE E2E: When no pddrc context provides strength, DEFAULT_STRENGTH should be used.
        """
        from pdd import DEFAULT_STRENGTH

        # pddrc with context that has NO strength default
        pddrc_content = '''version: "1.0"
contexts:
  test-ctx:
    paths: ["**"]
    defaults: {}
'''
        (tmp_path / ".pddrc").write_text(pddrc_content)
        (tmp_path / "test.prompt").write_text("test")
        (tmp_path / "test.py").write_text("# code")

        monkeypatch.chdir(tmp_path)

        with patch("pdd.cmd_test_main.generate_test") as mock_generate_test:
            mock_generate_test.return_value = ("tests", 0.01, "model")

            runner = CliRunner()
            result = runner.invoke(cli.cli, [
                "--local",  # Force local execution for unit test
                "--context", "test-ctx",
                "test",
                "test.prompt",
                "test.py",
                "--output", "out.py"
            ], catch_exceptions=False)

            call_kwargs = mock_generate_test.call_args.kwargs
            assert call_kwargs["strength"] == DEFAULT_STRENGTH, \
                f"Default not used: Expected {DEFAULT_STRENGTH}, got {call_kwargs['strength']}"


class TestPddrcChangeCommandE2E:
    """
    TRUE E2E tests for the change command.
    """

    def test_change_uses_pddrc_strength(self, tmp_path, monkeypatch):
        """
        TRUE E2E: change command should use strength from .pddrc context.
        """
        pddrc_content = '''version: "1.0"
contexts:
  test-ctx:
    paths: ["**"]
    defaults:
      strength: 0.9
'''
        (tmp_path / ".pddrc").write_text(pddrc_content)
        (tmp_path / "change.prompt").write_text("Add feature X")
        (tmp_path / "code.py").write_text("# code")
        (tmp_path / "input.prompt").write_text("Original prompt")

        monkeypatch.chdir(tmp_path)

        # Mock change_func which is the actual function called in change_main
        with patch("pdd.change_main.change_func") as mock_change_func:
            mock_change_func.return_value = ("changed code", 0.01, "model")

            runner = CliRunner()
            result = runner.invoke(cli.cli, [
                "--local",  # Force local execution for unit test
                "--context", "test-ctx",
                "change",
                "--manual",  # Use legacy/manual mode
                "change.prompt",  # CHANGE_PROMPT_FILE
                "code.py",  # INPUT_CODE
                "input.prompt",  # INPUT_PROMPT_FILE (positional)
                "--output", "out.py"
            ], catch_exceptions=False)

            assert mock_change_func.called, "change_func was not called"
            # change_func uses positional args: (change_prompt, code, input_prompt, strength, temp, ...)
            call_args = mock_change_func.call_args[0]
            strength_arg = call_args[3]  # strength is 4th positional arg
            assert strength_arg == 0.9, \
                f"PDDRC VALUE NOT USED: Expected strength=0.9, got {strength_arg}"


class TestPddrcCrashCommandE2E:
    """
    TRUE E2E tests for the crash command.
    """

    def test_crash_uses_pddrc_strength(self, tmp_path, monkeypatch):
        """
        TRUE E2E: crash command should use strength from .pddrc context.
        """
        pddrc_content = '''version: "1.0"
contexts:
  test-ctx:
    paths: ["**"]
    defaults:
      strength: 0.77
'''
        (tmp_path / ".pddrc").write_text(pddrc_content)
        (tmp_path / "module.prompt").write_text("Generate module")
        (tmp_path / "module.py").write_text("def foo(): pass")
        (tmp_path / "program.py").write_text("from module import foo")
        (tmp_path / "error.txt").write_text("NameError: name 'bar' is not defined")

        monkeypatch.chdir(tmp_path)

        with patch("pdd.crash_main.fix_code_module_errors") as mock_fix:
            mock_fix.return_value = (False, False, "", "", "", 0.01, "model")

            runner = CliRunner()
            result = runner.invoke(cli.cli, [
                "--local",  # Force local execution for unit test
                "--context", "test-ctx",
                "crash",
                "module.prompt",
                "module.py",
                "program.py",
                "error.txt",
                "--output", "out_module.py",
                "--output-program", "out_program.py"
            ], catch_exceptions=False)

            assert mock_fix.called, "fix_code_module_errors was not called"
            # fix_code_module_errors uses positional args for strength (5th arg)
            call_args = mock_fix.call_args[0]
            strength_arg = call_args[4]  # strength is 5th positional arg
            assert strength_arg == 0.77, \
                f"PDDRC VALUE NOT USED: Expected strength=0.77, got {strength_arg}"
