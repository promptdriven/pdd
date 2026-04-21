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
import git

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


class TestPddrcUpdateCommandE2E:
    """TRUE end-to-end tests for the update command."""

    def test_update_uses_pddrc_strength_for_direct_update(self, tmp_path, monkeypatch):
        """Direct update should use the active context's .pddrc strength."""
        pddrc_content = '''version: "1.0"
contexts:
  update-ctx:
    paths: ["**"]
    defaults:
      strength: 0.83
'''
        (tmp_path / ".pddrc").write_text(pddrc_content)
        (tmp_path / "feature_python.prompt").write_text("Existing prompt")
        (tmp_path / "original.py").write_text("def foo():\n    return 1\n")
        (tmp_path / "modified.py").write_text("def foo():\n    return 2\n")

        monkeypatch.chdir(tmp_path)

        with patch("pdd.update_main.get_available_agents", return_value=[]), \
             patch("pdd.update_main.update_prompt") as mock_update_prompt:
            mock_update_prompt.return_value = ("updated prompt", 0.01, "test-model")

            result = CliRunner().invoke(
                cli.cli,
                [
                    "--local",
                    "--context",
                    "update-ctx",
                    "update",
                    "feature_python.prompt",
                    "modified.py",
                    "original.py",
                    "--output",
                    "out.prompt",
                ],
                catch_exceptions=False,
            )

        assert result.exit_code == 0, result.output
        assert mock_update_prompt.called, "update_prompt was not called"
        assert mock_update_prompt.call_args.kwargs["strength"] == 0.83, \
            f"PDDRC VALUE NOT USED: Expected strength=0.83, got {mock_update_prompt.call_args.kwargs['strength']}"

    def test_update_uses_pddrc_strength_for_git_mode(self, tmp_path, monkeypatch):
        """Git-backed update should use the active context's .pddrc strength."""
        pddrc_content = '''version: "1.0"
contexts:
  update-ctx:
    paths: ["**"]
    defaults:
      strength: 0.67
'''
        (tmp_path / ".pddrc").write_text(pddrc_content)
        (tmp_path / "feature_python.prompt").write_text("Existing prompt")
        (tmp_path / "modified.py").write_text("def foo():\n    return 2\n")

        monkeypatch.chdir(tmp_path)

        with patch("pdd.update_main.get_available_agents", return_value=[]), \
             patch("pdd.update_main.git_update") as mock_git_update:
            mock_git_update.return_value = ("updated prompt", 0.01, "test-model")

            result = CliRunner().invoke(
                cli.cli,
                [
                    "--local",
                    "--context",
                    "update-ctx",
                    "update",
                    "--git",
                    "feature_python.prompt",
                    "modified.py",
                    "--output",
                    "out.prompt",
                ],
                catch_exceptions=False,
            )

        assert result.exit_code == 0, result.output
        assert mock_git_update.called, "git_update was not called"
        assert mock_git_update.call_args.kwargs["strength"] == 0.67, \
            f"PDDRC VALUE NOT USED: Expected strength=0.67, got {mock_git_update.call_args.kwargs['strength']}"

    def test_update_regeneration_uses_pddrc_strength(self, tmp_path, monkeypatch):
        """Regeneration mode should use the target file context's .pddrc strength."""
        pddrc_content = '''version: "1.0"
contexts:
  backend:
    paths: ["backend/**"]
    defaults:
      prompts_dir: "prompts/backend"
      generate_output_path: "backend"
      strength: 0.91
'''
        (tmp_path / ".pddrc").write_text(pddrc_content)
        (tmp_path / "backend").mkdir()
        (tmp_path / "backend" / "module.py").write_text("def foo():\n    return 1\n")
        (tmp_path / "prompts" / "backend").mkdir(parents=True)

        monkeypatch.chdir(tmp_path)
        git.Repo.init(tmp_path)

        with patch("pdd.update_main.get_available_agents", return_value=[]), \
             patch("pdd.update_main.update_prompt") as mock_update_prompt:
            mock_update_prompt.return_value = ("generated prompt", 0.01, "test-model")

            result = CliRunner().invoke(
                cli.cli,
                [
                    "--local",
                    "--context",
                    "backend",
                    "update",
                    "backend/module.py",
                ],
                catch_exceptions=False,
            )

        assert result.exit_code == 0, result.output
        assert mock_update_prompt.called, "update_prompt was not called"
        assert mock_update_prompt.call_args.kwargs["strength"] == 0.91, \
            f"PDDRC VALUE NOT USED: Expected strength=0.91, got {mock_update_prompt.call_args.kwargs['strength']}"

    def test_repo_update_uses_per_file_pddrc_strength_across_contexts(self, tmp_path, monkeypatch):
        """Repo-wide update must resolve strength per matched file context, not once per command."""
        pddrc_content = '''version: "1.0"
contexts:
  api:
    paths: ["api/**"]
    defaults:
      prompts_dir: "prompts/api"
      generate_output_path: "api"
      strength: 0.21
  worker:
    paths: ["worker/**"]
    defaults:
      prompts_dir: "prompts/worker"
      generate_output_path: "worker"
      strength: 0.89
'''
        (tmp_path / ".pddrc").write_text(pddrc_content)

        (tmp_path / "api").mkdir()
        (tmp_path / "worker").mkdir()
        (tmp_path / "api" / "users.py").write_text("def list_users():\n    return []\n")
        (tmp_path / "worker" / "jobs.py").write_text("def run_jobs():\n    return []\n")
        (tmp_path / "prompts" / "api").mkdir(parents=True)
        (tmp_path / "prompts" / "worker").mkdir(parents=True)
        (tmp_path / "prompts" / "api" / "users_python.prompt").write_text("Existing API prompt\n")
        (tmp_path / "prompts" / "worker" / "jobs_python.prompt").write_text("Existing worker prompt\n")

        repo = git.Repo.init(tmp_path)
        repo.index.add(
            [
                ".pddrc",
                "api/users.py",
                "worker/jobs.py",
                "prompts/api/users_python.prompt",
                "prompts/worker/jobs_python.prompt",
            ]
        )
        repo.index.commit("init")
        repo.git.branch("-M", "main")

        monkeypatch.chdir(tmp_path)

        captured_strengths = {}

        def fake_git_update(*, input_prompt, modified_code_file, strength, temperature, verbose, time, simple, quiet, prompt_file):
            captured_strengths[Path(prompt_file).name] = strength
            return (f"updated {Path(prompt_file).name}", 0.01, "test-model")

        with patch("pdd.update_main.get_available_agents", return_value=[]), \
             patch("pdd.update_main.is_code_changed", return_value=(True, "changed")), \
             patch("pdd.update_main.git_update", side_effect=fake_git_update), \
             patch("pdd.pddrc_initializer.ensure_pddrc_for_scan"), \
             patch("pdd.operation_log.save_fingerprint"):

            result = CliRunner().invoke(
                cli.cli,
                [
                    "--local",
                    "update",
                ],
                catch_exceptions=False,
            )

        assert result.exit_code == 0, result.output
        assert captured_strengths == {
            "users_python.prompt": 0.21,
            "jobs_python.prompt": 0.89,
        }, f"Per-context strengths were not used in repo mode: {captured_strengths}"
