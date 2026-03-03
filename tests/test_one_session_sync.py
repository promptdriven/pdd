"""Tests for pdd.one_session_sync module."""
from __future__ import annotations

import textwrap
from pathlib import Path
from typing import Any, Dict
from unittest.mock import MagicMock, patch

import click
import pytest

from pdd.one_session_sync import (
    _STEP_TO_PHASE,
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
# _STEP_TO_PHASE mapping
# ---------------------------------------------------------------------------

class TestStepToPhase:
    """Tests for _STEP_TO_PHASE mapping dict."""

    def test_known_phase_mappings(self):
        assert _STEP_TO_PHASE["example_generate"] == "example"
        assert _STEP_TO_PHASE["crash_fix"] == "crash"
        assert _STEP_TO_PHASE["verify"] == "verify"
        assert _STEP_TO_PHASE["test_generate"] == "test"
        assert _STEP_TO_PHASE["done"] == "synced"

    def test_intermediate_steps_not_mapped(self):
        """crash_fix_attempt, test_fix_attempt, test_pass have no phase mapping."""
        assert "crash_fix_attempt:1" not in _STEP_TO_PHASE
        assert "test_fix_attempt:1" not in _STEP_TO_PHASE
        assert "test_pass" not in _STEP_TO_PHASE


# ---------------------------------------------------------------------------
# PDD_PHASE marker emission
# ---------------------------------------------------------------------------

class TestPhaseMarkerEmission:
    """Tests that PDD_PHASE: markers are printed to stdout."""

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_heartbeat_emits_phase_markers(self, mock_build, mock_task, tmp_path, capsys):
        """Heartbeat should print PDD_PHASE: markers when steps complete."""
        pdd_files = _make_pdd_files(tmp_path)
        progress_file = tmp_path / ".pdd_one_session_progress_my_module"

        def fake_task(**kwargs):
            # Simulate agent writing progress during task
            progress_file.write_text(
                "STEP_COMPLETE:example_generate\n"
                "STEP_COMPLETE:crash_fix\n"
                "STEP_COMPLETE:verify\n"
            )
            # Give heartbeat time to read (heartbeat runs every 10s, but we
            # want the remaining-progress path to pick these up)
            return (True, "done", 1.0, "claude-code")

        mock_task.side_effect = fake_task

        run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        captured = capsys.readouterr()
        # Phase markers should appear in stdout (from heartbeat or remaining progress)
        assert "PDD_PHASE: example" in captured.out
        assert "PDD_PHASE: crash" in captured.out
        assert "PDD_PHASE: verify" in captured.out

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_success_emits_synced_phase(self, mock_build, mock_task, tmp_path, capsys):
        """On success, final PDD_PHASE: synced is emitted."""
        mock_task.return_value = (True, "done", 1.0, "claude-code")
        pdd_files = _make_pdd_files(tmp_path)

        run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        captured = capsys.readouterr()
        assert "PDD_PHASE: synced" in captured.out

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_failure_emits_conflict_phase(self, mock_build, mock_task, tmp_path, capsys):
        """On failure, PDD_PHASE: conflict is emitted."""
        mock_task.return_value = (False, "error", 0.5, "claude-code")
        pdd_files = _make_pdd_files(tmp_path)

        run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        captured = capsys.readouterr()
        assert "PDD_PHASE: conflict" in captured.out

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_intermediate_steps_do_not_emit_phase(self, mock_build, mock_task, tmp_path, capsys):
        """Steps like crash_fix_attempt and test_pass should NOT emit PDD_PHASE."""
        pdd_files = _make_pdd_files(tmp_path)
        progress_file = tmp_path / ".pdd_one_session_progress_my_module"

        def fake_task(**kwargs):
            progress_file.write_text(
                "STEP_COMPLETE:crash_fix_attempt:1\n"
                "STEP_COMPLETE:test_pass\n"
                "STEP_COMPLETE:test_fix_attempt:2\n"
            )
            return (True, "done", 1.0, "claude-code")

        mock_task.side_effect = fake_task

        run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        captured = capsys.readouterr()
        # These intermediate steps should not produce PDD_PHASE markers
        lines = [l for l in captured.out.splitlines() if l.startswith("PDD_PHASE:")]
        # Only the final "synced" should be there
        assert lines == ["PDD_PHASE: synced"]

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_phase_markers_emitted_even_when_quiet(self, mock_build, mock_task, tmp_path, capsys):
        """PDD_PHASE: synced/conflict are always emitted regardless of quiet flag."""
        mock_task.return_value = (True, "done", 1.0, "claude-code")
        pdd_files = _make_pdd_files(tmp_path)

        run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
            quiet=True,
        )

        captured = capsys.readouterr()
        assert "PDD_PHASE: synced" in captured.out


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
        mock_load.assert_called_once_with("one_session_agent_LLM")

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
        with pytest.raises(FileNotFoundError, match="one_session_agent_LLM"):
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
        assert call_kwargs.kwargs.get("one_session") is True

    @patch("pdd.commands.maintenance.sync_main")
    def test_single_module_default_false(self, mock_sync_main):
        """Single-module sync defaults to one_session=False."""
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
        assert call_kwargs.kwargs.get("one_session") is False

    @patch("pdd.commands.maintenance.sync_main")
    def test_no_one_session_flag(self, mock_sync_main):
        """--no-one-session explicitly disables one_session."""
        from click.testing import CliRunner
        from pdd.commands.maintenance import sync

        mock_sync_main.return_value = ({}, 0.0, "")
        runner = CliRunner()
        result = runner.invoke(
            sync,
            ["my_module", "--no-one-session"],
            obj={"quiet": False, "verbose": False},
            catch_exceptions=False,
        )

        mock_sync_main.assert_called_once()
        call_kwargs = mock_sync_main.call_args
        assert call_kwargs.kwargs.get("one_session") is False

    @patch("pdd.commands.maintenance.run_agentic_sync")
    @patch("pdd.commands.maintenance._is_github_issue_url", return_value=True)
    def test_agentic_sync_default_true(self, mock_is_url, mock_agentic):
        """Agentic sync (issue URL) defaults to one_session=True."""
        from click.testing import CliRunner
        from pdd.commands.maintenance import sync

        mock_agentic.return_value = (True, "ok", 1.0, "claude")
        runner = CliRunner()
        result = runner.invoke(
            sync,
            ["https://github.com/org/repo/issues/1"],
            obj={"quiet": False, "verbose": False},
            catch_exceptions=False,
        )

        mock_agentic.assert_called_once()
        call_kwargs = mock_agentic.call_args
        assert call_kwargs.kwargs.get("one_session") is True

    @patch("pdd.commands.maintenance.run_agentic_sync")
    @patch("pdd.commands.maintenance._is_github_issue_url", return_value=True)
    def test_agentic_sync_no_one_session(self, mock_is_url, mock_agentic):
        """--no-one-session disables one_session even for agentic sync."""
        from click.testing import CliRunner
        from pdd.commands.maintenance import sync

        mock_agentic.return_value = (True, "ok", 1.0, "claude")
        runner = CliRunner()
        result = runner.invoke(
            sync,
            ["https://github.com/org/repo/issues/1", "--no-one-session"],
            obj={"quiet": False, "verbose": False},
            catch_exceptions=False,
        )

        mock_agentic.assert_called_once()
        call_kwargs = mock_agentic.call_args
        assert call_kwargs.kwargs.get("one_session") is False


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

            assert mock_popen.called, "Popen was never invoked"
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

            assert mock_popen.called, "Popen was never invoked"
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


# ---------------------------------------------------------------------------
# Post-sync: fingerprint saving and auto-submit
# ---------------------------------------------------------------------------

class TestPostSyncFingerprintAndAutoSubmit:
    """Tests for fingerprint saving and auto-submit after one-session sync."""

    _PATCHES = [
        "pdd.sync_main._auto_submit_example",
        "pdd.operation_log.save_fingerprint",
        "pdd.one_session_sync.run_one_session_sync",
        "pdd.sync_determine_operation.get_pdd_file_paths",
        "pdd.sync_main.construct_paths",
        "pdd.sync_main._find_prompt_in_contexts",
        "pdd.sync_main._detect_languages_with_context",
    ]

    def _make_ctx(self, quiet: bool = False, local: bool = False) -> MagicMock:
        """Create a mock Click context with obj dict."""
        ctx = MagicMock(spec=click.Context)
        ctx.obj = {"quiet": quiet, "local": local}
        return ctx

    def _setup_mocks(self, mocks, pdd_files, success=True, local=False):
        """Configure standard mock return values.

        Args:
            mocks: dict of name -> mock (keys: detect_langs, find_prompt,
                   construct, get_paths, run, save_fp, submit)
            pdd_files: pdd_files dict from _make_pdd_files
            success: whether run_one_session_sync should return success
            local: whether ctx should use local=True
        """
        prompt_file = pdd_files["prompt"]
        # _find_prompt_in_contexts returns None (fall through to construct_paths discovery)
        mocks["find_prompt"].return_value = None
        # First construct_paths call (discovery) returns config with prompts_dir
        discovery_config = {"prompts_dir": str(prompt_file.parent)}
        # Second construct_paths call (per-language) returns full config
        lang_config = {
            "code_dir": str(pdd_files["code"].parent),
            "tests_dir": str(pdd_files["test"].parent),
            "examples_dir": str(pdd_files["example"].parent),
        }
        mocks["construct"].side_effect = [
            (discovery_config, {}, {}, None),
            (lang_config, {}, {}, "python"),
        ]
        # _detect_languages_with_context returns single language
        mocks["detect_langs"].return_value = {"python": prompt_file}
        # get_pdd_file_paths returns our pdd_files
        mocks["get_paths"].return_value = pdd_files
        # run_one_session_sync
        if success:
            mocks["run"].return_value = {
                "success": True,
                "total_cost": 1.5,
                "model_name": "claude-code",
                "operations_completed": ["example", "crash_fix", "verify", "test"],
                "errors": [],
            }
        else:
            mocks["run"].return_value = {
                "success": False,
                "total_cost": 0.5,
                "model_name": "claude-code",
                "operations_completed": [],
                "errors": ["Something failed"],
            }

    @patch("pdd.sync_main._detect_languages_with_context")
    @patch("pdd.sync_main._find_prompt_in_contexts")
    @patch("pdd.sync_main._auto_submit_example")
    @patch("pdd.operation_log.save_fingerprint")
    @patch("pdd.one_session_sync.run_one_session_sync")
    @patch("pdd.sync_determine_operation.get_pdd_file_paths")
    @patch("pdd.sync_main.construct_paths")
    def test_fingerprint_saved_on_success(
        self, mock_construct, mock_get_paths, mock_run, mock_save_fp,
        mock_submit, mock_find_prompt, mock_detect_langs, tmp_path
    ):
        """save_fingerprint is called when one-session sync succeeds."""
        from pdd.sync_main import sync_main

        pdd_files = _make_pdd_files(tmp_path)
        mocks = {
            "construct": mock_construct, "get_paths": mock_get_paths,
            "run": mock_run, "save_fp": mock_save_fp, "submit": mock_submit,
            "find_prompt": mock_find_prompt, "detect_langs": mock_detect_langs,
        }
        self._setup_mocks(mocks, pdd_files, success=True, local=True)

        ctx = self._make_ctx(local=True)
        sync_main(
            ctx=ctx, basename="my_module", max_attempts=3, budget=20.0,
            skip_verify=False, skip_tests=False, target_coverage=80.0,
            dry_run=False, one_session=True,
        )

        mock_save_fp.assert_called_once_with(
            "my_module", "python", "fix",
            pdd_files, 1.5, "claude-code",
        )

    @patch("pdd.sync_main._detect_languages_with_context")
    @patch("pdd.sync_main._find_prompt_in_contexts")
    @patch("pdd.sync_main._auto_submit_example")
    @patch("pdd.operation_log.save_fingerprint")
    @patch("pdd.one_session_sync.run_one_session_sync")
    @patch("pdd.sync_determine_operation.get_pdd_file_paths")
    @patch("pdd.sync_main.construct_paths")
    def test_fingerprint_not_saved_on_failure(
        self, mock_construct, mock_get_paths, mock_run, mock_save_fp,
        mock_submit, mock_find_prompt, mock_detect_langs, tmp_path
    ):
        """save_fingerprint is NOT called when one-session sync fails."""
        from pdd.sync_main import sync_main

        pdd_files = _make_pdd_files(tmp_path)
        mocks = {
            "construct": mock_construct, "get_paths": mock_get_paths,
            "run": mock_run, "save_fp": mock_save_fp, "submit": mock_submit,
            "find_prompt": mock_find_prompt, "detect_langs": mock_detect_langs,
        }
        self._setup_mocks(mocks, pdd_files, success=False)

        ctx = self._make_ctx()
        sync_main(
            ctx=ctx, basename="my_module", max_attempts=3, budget=20.0,
            skip_verify=False, skip_tests=False, target_coverage=80.0,
            dry_run=False, one_session=True,
        )

        mock_save_fp.assert_not_called()

    @patch("pdd.sync_main._detect_languages_with_context")
    @patch("pdd.sync_main._find_prompt_in_contexts")
    @patch("pdd.sync_main._auto_submit_example")
    @patch("pdd.operation_log.save_fingerprint")
    @patch("pdd.one_session_sync.run_one_session_sync")
    @patch("pdd.sync_determine_operation.get_pdd_file_paths")
    @patch("pdd.sync_main.construct_paths")
    def test_auto_submit_on_success(
        self, mock_construct, mock_get_paths, mock_run, mock_save_fp,
        mock_submit, mock_find_prompt, mock_detect_langs, tmp_path
    ):
        """_auto_submit_example is called on success when not local."""
        from pdd.sync_main import sync_main

        pdd_files = _make_pdd_files(tmp_path)
        mocks = {
            "construct": mock_construct, "get_paths": mock_get_paths,
            "run": mock_run, "save_fp": mock_save_fp, "submit": mock_submit,
            "find_prompt": mock_find_prompt, "detect_langs": mock_detect_langs,
        }
        self._setup_mocks(mocks, pdd_files, success=True, local=False)

        ctx = self._make_ctx(local=False)
        sync_main(
            ctx=ctx, basename="my_module", max_attempts=3, budget=20.0,
            skip_verify=False, skip_tests=False, target_coverage=80.0,
            dry_run=False, one_session=True,
        )

        mock_submit.assert_called_once_with("my_module", "python", pdd_files, ctx)

    @patch("pdd.sync_main._detect_languages_with_context")
    @patch("pdd.sync_main._find_prompt_in_contexts")
    @patch("pdd.sync_main._auto_submit_example")
    @patch("pdd.operation_log.save_fingerprint")
    @patch("pdd.one_session_sync.run_one_session_sync")
    @patch("pdd.sync_determine_operation.get_pdd_file_paths")
    @patch("pdd.sync_main.construct_paths")
    def test_auto_submit_skipped_when_local(
        self, mock_construct, mock_get_paths, mock_run, mock_save_fp,
        mock_submit, mock_find_prompt, mock_detect_langs, tmp_path
    ):
        """_auto_submit_example is NOT called when local=True."""
        from pdd.sync_main import sync_main

        pdd_files = _make_pdd_files(tmp_path)
        mocks = {
            "construct": mock_construct, "get_paths": mock_get_paths,
            "run": mock_run, "save_fp": mock_save_fp, "submit": mock_submit,
            "find_prompt": mock_find_prompt, "detect_langs": mock_detect_langs,
        }
        self._setup_mocks(mocks, pdd_files, success=True, local=True)

        ctx = self._make_ctx(local=True)
        sync_main(
            ctx=ctx, basename="my_module", max_attempts=3, budget=20.0,
            skip_verify=False, skip_tests=False, target_coverage=80.0,
            dry_run=False, one_session=True,
        )

        mock_submit.assert_not_called()

    @patch("pdd.sync_main._detect_languages_with_context")
    @patch("pdd.sync_main._find_prompt_in_contexts")
    @patch("pdd.sync_main._auto_submit_example")
    @patch("pdd.operation_log.save_fingerprint")
    @patch("pdd.one_session_sync.run_one_session_sync")
    @patch("pdd.sync_determine_operation.get_pdd_file_paths")
    @patch("pdd.sync_main.construct_paths")
    def test_auto_submit_skipped_on_failure(
        self, mock_construct, mock_get_paths, mock_run, mock_save_fp,
        mock_submit, mock_find_prompt, mock_detect_langs, tmp_path
    ):
        """_auto_submit_example is NOT called when sync fails."""
        from pdd.sync_main import sync_main

        pdd_files = _make_pdd_files(tmp_path)
        mocks = {
            "construct": mock_construct, "get_paths": mock_get_paths,
            "run": mock_run, "save_fp": mock_save_fp, "submit": mock_submit,
            "find_prompt": mock_find_prompt, "detect_langs": mock_detect_langs,
        }
        self._setup_mocks(mocks, pdd_files, success=False)

        ctx = self._make_ctx(local=False)
        sync_main(
            ctx=ctx, basename="my_module", max_attempts=3, budget=20.0,
            skip_verify=False, skip_tests=False, target_coverage=80.0,
            dry_run=False, one_session=True,
        )

        mock_submit.assert_not_called()
