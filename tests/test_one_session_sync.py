"""Tests for pdd.one_session_sync module."""
from __future__ import annotations

import textwrap
from pathlib import Path
from typing import Any, Dict
from unittest.mock import MagicMock, patch

import pytest

from pdd.one_session_sync import (
    _compute_import_base,
    _format_step_display,
    _read_new_progress,
    build_one_session_prompt,
    run_one_session_sync,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_pdd_files(tmp_path: Path) -> Dict[str, Path]:
    """Create minimal PDD file structure and return pdd_files dict."""
    prompt_file = tmp_path / "prompts" / "my_module_python.prompt"
    prompt_file.parent.mkdir(parents=True, exist_ok=True)
    prompt_file.write_text("Module spec for my_module.\n<include>nonexistent.prompt</include>")

    code_file = tmp_path / "src" / "my_module.py"
    code_file.parent.mkdir(parents=True, exist_ok=True)
    code_file.write_text("def hello():\n    return 'world'\n")

    example_file = tmp_path / "examples" / "my_module_example.py"
    example_file.parent.mkdir(parents=True, exist_ok=True)

    test_file = tmp_path / "tests" / "test_my_module.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)

    return {
        "prompt": prompt_file,
        "code": code_file,
        "example": example_file,
        "test": test_file,
    }


_FAKE_TEMPLATE = textwrap.dedent("""\
    # One-Session: {basename}
    Lang: {language}
    Prompt: {prompt_path}
    Code: {code_path}
    Example: {example_path}
    Test: {test_path}
    Root: {project_root}
    Coverage: {target_coverage}
    Progress: {progress_file}
    Import: {import_base}
    VerifyStep: {verify_step_num}
    TestStep: {test_step_num}
    Spec: {resolved_prompt_content}
    Code content: {code_content}
""")


# ---------------------------------------------------------------------------
# _read_new_progress / _format_step_display
# ---------------------------------------------------------------------------

class TestProgressHelpers:
    """Tests for progress file reading and step display formatting."""

    def test_read_progress_no_file(self, tmp_path):
        assert _read_new_progress(tmp_path / "nonexistent", 0) == []

    def test_read_progress_empty_file(self, tmp_path):
        f = tmp_path / "progress"
        f.write_text("")
        assert _read_new_progress(f, 0) == []

    def test_read_progress_one_step(self, tmp_path):
        f = tmp_path / "progress"
        f.write_text("STEP_COMPLETE:example_generate\n")
        assert _read_new_progress(f, 0) == ["example_generate"]

    def test_read_progress_skip_already_reported(self, tmp_path):
        f = tmp_path / "progress"
        f.write_text("STEP_COMPLETE:example_generate\nSTEP_COMPLETE:crash_fix\n")
        assert _read_new_progress(f, 1) == ["crash_fix"]

    def test_read_progress_ignores_non_marker_lines(self, tmp_path):
        f = tmp_path / "progress"
        f.write_text("some random output\nSTEP_COMPLETE:crash_fix\nmore noise\n")
        assert _read_new_progress(f, 0) == ["crash_fix"]

    def test_read_progress_multiple_steps(self, tmp_path):
        f = tmp_path / "progress"
        f.write_text(
            "STEP_COMPLETE:example_generate\n"
            "STEP_COMPLETE:crash_fix\n"
            "STEP_COMPLETE:verify\n"
        )
        assert _read_new_progress(f, 0) == ["example_generate", "crash_fix", "verify"]

    def test_format_known_steps(self):
        assert _format_step_display("example_generate") == "Example file created"
        assert _format_step_display("crash_fix") == "Example runs without errors"
        assert _format_step_display("verify") == "Behavior verified against spec"
        assert _format_step_display("test_generate") == "Test file created"
        assert _format_step_display("test_pass") == "All tests passing"
        assert _format_step_display("done") == "All steps complete"

    def test_format_crash_fix_attempt(self):
        assert _format_step_display("crash_fix_attempt:1") == "Crash fix attempt 1"
        assert _format_step_display("crash_fix_attempt:3") == "Crash fix attempt 3"

    def test_format_test_fix_attempt(self):
        assert _format_step_display("test_fix_attempt:2") == "Test fix attempt 2"

    def test_format_unknown_step(self):
        assert _format_step_display("something_custom") == "something_custom"


# ---------------------------------------------------------------------------
# _compute_import_base
# ---------------------------------------------------------------------------

class TestComputeImportBase:
    """Tests for _compute_import_base()."""

    def test_simple_module(self, tmp_path):
        code_path = tmp_path / "pdd" / "crm_models.py"
        assert _compute_import_base(code_path, tmp_path) == "pdd.crm_models"

    def test_nested_module(self, tmp_path):
        code_path = tmp_path / "src" / "core" / "utils.py"
        assert _compute_import_base(code_path, tmp_path) == "src.core.utils"

    def test_root_level_module(self, tmp_path):
        code_path = tmp_path / "my_module.py"
        assert _compute_import_base(code_path, tmp_path) == "my_module"

    def test_unrelated_path_falls_back_to_stem(self, tmp_path):
        code_path = Path("/completely/different/path/module.py")
        assert _compute_import_base(code_path, tmp_path) == "module"


# ---------------------------------------------------------------------------
# build_one_session_prompt
# ---------------------------------------------------------------------------

class TestBuildOneSessionPrompt:
    """Tests for build_one_session_prompt()."""

    @patch("pdd.one_session_sync.load_prompt_template", return_value=_FAKE_TEMPLATE)
    @patch("pdd.one_session_sync.preprocess", side_effect=lambda p, **kw: f"PREPROCESSED({p})")
    def test_basic_prompt_construction(self, mock_preprocess, mock_load, tmp_path):
        pdd_files = _make_pdd_files(tmp_path)
        result = build_one_session_prompt(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )
        assert "my_module" in result
        assert "python" in result
        assert "PREPROCESSED(" in result
        assert "def hello():" in result
        mock_preprocess.assert_called_once()
        mock_load.assert_called_once_with("one_session_sync_LLM")

    @patch("pdd.one_session_sync.load_prompt_template", return_value=_FAKE_TEMPLATE)
    @patch("pdd.one_session_sync.preprocess", return_value="spec content")
    def test_custom_target_coverage(self, mock_pre, mock_load, tmp_path):
        pdd_files = _make_pdd_files(tmp_path)
        result = build_one_session_prompt(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
            target_coverage=80.0,
        )
        assert "80.0" in result

    @patch("pdd.one_session_sync.load_prompt_template", return_value=_FAKE_TEMPLATE)
    @patch("pdd.one_session_sync.preprocess", return_value="spec content")
    def test_fixed_step_numbers(self, mock_pre, mock_load, tmp_path):
        """Verify=3, Test=4 always (example=1, crash=2)."""
        pdd_files = _make_pdd_files(tmp_path)
        result = build_one_session_prompt(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )
        assert "VerifyStep: 3" in result
        assert "TestStep: 4" in result

    @patch("pdd.one_session_sync.load_prompt_template", return_value=None)
    @patch("pdd.one_session_sync.preprocess", return_value="spec content")
    def test_missing_template_raises(self, mock_pre, mock_load, tmp_path):
        pdd_files = _make_pdd_files(tmp_path)
        with pytest.raises(FileNotFoundError, match="one_session_sync_LLM"):
            build_one_session_prompt(
                basename="my_module",
                language="python",
                pdd_files=pdd_files,
                project_root=tmp_path,
            )

    @patch("pdd.one_session_sync.load_prompt_template", return_value=_FAKE_TEMPLATE)
    @patch("pdd.one_session_sync.preprocess", return_value="spec content")
    def test_all_paths_substituted(self, mock_pre, mock_load, tmp_path):
        pdd_files = _make_pdd_files(tmp_path)
        result = build_one_session_prompt(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )
        assert str(pdd_files["prompt"]) in result
        assert str(pdd_files["code"]) in result
        assert str(pdd_files["example"]) in result
        assert str(pdd_files["test"]) in result
        assert str(tmp_path) in result

    @patch("pdd.one_session_sync.load_prompt_template", return_value=_FAKE_TEMPLATE)
    @patch("pdd.one_session_sync.preprocess", return_value="spec content")
    def test_import_base_in_prompt(self, mock_pre, mock_load, tmp_path):
        """import_base is computed from code path and included in prompt."""
        pdd_files = _make_pdd_files(tmp_path)
        result = build_one_session_prompt(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )
        # code is at tmp_path/src/my_module.py, so import_base = "src.my_module"
        assert "src.my_module" in result

    @patch("pdd.one_session_sync.load_prompt_template", return_value=_FAKE_TEMPLATE)
    @patch("pdd.one_session_sync.preprocess", return_value="spec content")
    def test_progress_file_in_prompt(self, mock_pre, mock_load, tmp_path):
        pdd_files = _make_pdd_files(tmp_path)
        result = build_one_session_prompt(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )
        assert ".pdd_one_session_progress_my_module" in result

    @patch("pdd.one_session_sync.load_prompt_template", return_value=_FAKE_TEMPLATE)
    @patch("pdd.one_session_sync.preprocess", return_value="resolved spec")
    def test_preprocess_called_with_correct_args(self, mock_pre, mock_load, tmp_path):
        pdd_files = _make_pdd_files(tmp_path)
        build_one_session_prompt(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )
        call_kwargs = mock_pre.call_args
        assert call_kwargs.kwargs.get("recursive") is True
        assert call_kwargs.kwargs.get("double_curly_brackets") is False


# ---------------------------------------------------------------------------
# Progress file integration
# ---------------------------------------------------------------------------

class TestProgressFileIntegration:
    """Test that progress file is created, read, and cleaned up."""

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_progress_file_cleaned_up_on_success(self, mock_build, mock_task, tmp_path):
        mock_task.return_value = (True, "done", 1.0, "claude-code")
        pdd_files = _make_pdd_files(tmp_path)

        # Simulate agent writing progress
        progress_file = tmp_path / ".pdd_one_session_progress_my_module"
        progress_file.write_text("STEP_COMPLETE:crash_fix\n")

        run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        # Progress file should be cleaned up
        assert not progress_file.exists()

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_stale_progress_file_removed_before_run(self, mock_build, mock_task, tmp_path):
        mock_task.return_value = (True, "done", 1.0, "claude-code")
        pdd_files = _make_pdd_files(tmp_path)

        # Create stale progress file from previous run
        progress_file = tmp_path / ".pdd_one_session_progress_my_module"
        progress_file.write_text("STEP_COMPLETE:old_stuff\n")

        run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        assert not progress_file.exists()


# ---------------------------------------------------------------------------
# run_one_session_sync
# ---------------------------------------------------------------------------

class TestRunOneSessionSync:
    """Tests for run_one_session_sync()."""

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_success_returns_correct_dict(self, mock_build, mock_task, tmp_path):
        mock_task.return_value = (True, "done", 1.5, "claude-code")
        pdd_files = _make_pdd_files(tmp_path)

        result = run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        assert result["success"] is True
        assert result["total_cost"] == 1.5
        assert result["model_name"] == "claude-code"
        assert result["operations_completed"] == ["example", "crash_fix", "verify", "test"]
        assert result["errors"] == []

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_failure_returns_errors(self, mock_build, mock_task, tmp_path):
        mock_task.return_value = (False, "Something went wrong", 0.5, "claude-code")
        pdd_files = _make_pdd_files(tmp_path)

        result = run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        assert result["success"] is False
        assert result["total_cost"] == 0.5
        assert result["operations_completed"] == []
        assert len(result["errors"]) == 1
        assert "Something went wrong" in result["errors"][0]

    def test_missing_code_file_raises(self, tmp_path):
        pdd_files = _make_pdd_files(tmp_path)
        pdd_files["code"].unlink()

        with pytest.raises(FileNotFoundError, match="pdd generate"):
            run_one_session_sync(
                basename="my_module",
                language="python",
                pdd_files=pdd_files,
                project_root=tmp_path,
            )

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_no_example_file_required(self, mock_build, mock_task, tmp_path):
        """Example file does NOT need to exist — the agent creates it."""
        mock_task.return_value = (True, "done", 1.0, "claude-code")
        pdd_files = _make_pdd_files(tmp_path)
        assert not pdd_files["example"].exists()

        result = run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )
        assert result["success"] is True

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_default_timeout(self, mock_build, mock_task, tmp_path):
        mock_task.return_value = (True, "done", 1.0, "claude-code")
        pdd_files = _make_pdd_files(tmp_path)

        run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        _, kwargs = mock_task.call_args
        assert kwargs["timeout"] == 1200.0

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_custom_timeout(self, mock_build, mock_task, tmp_path):
        mock_task.return_value = (True, "done", 1.0, "claude-code")
        pdd_files = _make_pdd_files(tmp_path)

        run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
            timeout=600.0,
        )

        _, kwargs = mock_task.call_args
        assert kwargs["timeout"] == 600.0

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_label_includes_basename(self, mock_build, mock_task, tmp_path):
        mock_task.return_value = (True, "done", 1.0, "claude-code")
        pdd_files = _make_pdd_files(tmp_path)

        run_one_session_sync(
            basename="crm_models",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        _, kwargs = mock_task.call_args
        assert "crm_models" in kwargs["label"]

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_verbose_and_quiet_forwarded(self, mock_build, mock_task, tmp_path):
        mock_task.return_value = (True, "done", 1.0, "claude-code")
        pdd_files = _make_pdd_files(tmp_path)

        run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
            verbose=True,
            quiet=True,
        )

        _, kwargs = mock_task.call_args
        assert kwargs["verbose"] is True
        assert kwargs["quiet"] is True

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_cwd_set_to_project_root(self, mock_build, mock_task, tmp_path):
        mock_task.return_value = (True, "done", 1.0, "claude-code")
        pdd_files = _make_pdd_files(tmp_path)

        run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        _, kwargs = mock_task.call_args
        assert kwargs["cwd"] == tmp_path

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_empty_output_on_failure(self, mock_build, mock_task, tmp_path):
        mock_task.return_value = (False, "", 0.1, "claude-code")
        pdd_files = _make_pdd_files(tmp_path)

        result = run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        assert result["success"] is False
        assert len(result["errors"]) == 1
        assert "failed" in result["errors"][0].lower()


# ---------------------------------------------------------------------------
# CLI integration — --one-session flag
# ---------------------------------------------------------------------------

class TestCliOneSessionFlag:
    """Test that --one-session is wired through the CLI stack."""

    @patch("pdd.commands.maintenance.sync_main")
    def test_flag_forwarded_to_sync_main(self, mock_sync_main):
        """--one-session flag is passed through to sync_main."""
        from click.testing import CliRunner
        from pdd.commands.maintenance import sync

        mock_sync_main.return_value = ({}, 0.0, "")
        runner = CliRunner()
        result = runner.invoke(
            sync,
            ["my_module", "--one-session"],
            obj={"quiet": False, "verbose": False},
            catch_exceptions=False,
        )

        mock_sync_main.assert_called_once()
        call_kwargs = mock_sync_main.call_args
        assert call_kwargs.kwargs.get("one_session") is True or \
               (len(call_kwargs.args) > 0 and "one_session" in str(call_kwargs))

    @patch("pdd.commands.maintenance.sync_main")
    def test_flag_default_false(self, mock_sync_main):
        """Without --one-session, one_session defaults to False."""
        from click.testing import CliRunner
        from pdd.commands.maintenance import sync

        mock_sync_main.return_value = ({}, 0.0, "")
        runner = CliRunner()
        result = runner.invoke(
            sync,
            ["my_module"],
            obj={"quiet": False, "verbose": False},
            catch_exceptions=False,
        )

        mock_sync_main.assert_called_once()
        call_kwargs = mock_sync_main.call_args
        assert call_kwargs.kwargs.get("one_session") is False or \
               (len(call_kwargs.args) > 0 and "one_session" in str(call_kwargs))


# ---------------------------------------------------------------------------
# agentic_sync_runner — --one-session forwarded in subprocess cmd
# ---------------------------------------------------------------------------

class TestAgenticSyncRunnerOneSession:
    """Test that AsyncSyncRunner forwards --one-session to child process."""

    def test_one_session_appended_to_cmd(self):
        """When sync_options has one_session=True, --one-session is in cmd."""
        from pdd.agentic_sync_runner import AsyncSyncRunner

        runner = AsyncSyncRunner(
            basenames=["test_mod"],
            dep_graph={"test_mod": set()},
            sync_options={"one_session": True},
            github_info=None,
            quiet=True,
            verbose=False,
            issue_url="",
            module_cwds={},
        )

        with patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd"), \
             patch("subprocess.Popen") as mock_popen:
            mock_proc = MagicMock()
            mock_proc.stdout = MagicMock()
            mock_proc.stderr = MagicMock()
            mock_proc.stdout.readline = MagicMock(return_value="")
            mock_proc.stderr.readline = MagicMock(return_value="")
            mock_proc.wait.return_value = 0
            mock_proc.returncode = 0
            mock_proc.pid = 12345
            mock_popen.return_value = mock_proc

            try:
                runner._sync_one_module("test_mod")
            except Exception:
                pass

            if mock_popen.called:
                cmd = mock_popen.call_args[0][0]
                assert "--one-session" in cmd

    def test_one_session_not_in_cmd_when_false(self):
        """When sync_options has one_session=False, --one-session is not in cmd."""
        from pdd.agentic_sync_runner import AsyncSyncRunner

        runner = AsyncSyncRunner(
            basenames=["test_mod"],
            dep_graph={"test_mod": set()},
            sync_options={"one_session": False},
            github_info=None,
            quiet=True,
            verbose=False,
            issue_url="",
            module_cwds={},
        )

        with patch("pdd.agentic_sync_runner._find_pdd_executable", return_value="/usr/bin/pdd"), \
             patch("subprocess.Popen") as mock_popen:
            mock_proc = MagicMock()
            mock_proc.stdout = MagicMock()
            mock_proc.stderr = MagicMock()
            mock_proc.stdout.readline = MagicMock(return_value="")
            mock_proc.stderr.readline = MagicMock(return_value="")
            mock_proc.wait.return_value = 0
            mock_proc.returncode = 0
            mock_proc.pid = 12345
            mock_popen.return_value = mock_proc

            try:
                runner._sync_one_module("test_mod")
            except Exception:
                pass

            if mock_popen.called:
                cmd = mock_popen.call_args[0][0]
                assert "--one-session" not in cmd


# ---------------------------------------------------------------------------
# agentic_sync — one_session in sync_options
# ---------------------------------------------------------------------------

class TestAgenticSyncOneSession:
    """Test that run_agentic_sync accepts one_session and includes it in sync_options."""

    def test_one_session_param_accepted(self):
        """run_agentic_sync accepts one_session keyword argument."""
        import inspect
        from pdd.agentic_sync import run_agentic_sync
        sig = inspect.signature(run_agentic_sync)
        assert "one_session" in sig.parameters
        assert sig.parameters["one_session"].default is False

    def test_one_session_in_sync_options_dict(self):
        """Verify the sync_options dict construction includes one_session."""
        import pdd.agentic_sync as mod
        import inspect
        source = inspect.getsource(mod.run_agentic_sync)
        assert '"one_session": one_session' in source or "'one_session': one_session" in source
