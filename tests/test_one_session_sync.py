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

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_success_rejects_broad_test_rewrite_and_restores_file(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        from pdd.code_generator_main import TestChurnError

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        mock_task.return_value = (True, "done", 1.0, "claude-code")
        pdd_files = _make_pdd_files(tmp_path)
        original_tests = (
            "def test_a(): pass\n"
            "def test_b(): pass\n"
            "def test_c(): pass\n"
        )
        rewritten_tests = (
            "def test_new_a(): pass\n"
            "def test_new_b(): pass\n"
            "def test_new_c(): pass\n"
        )
        pdd_files["test"].write_text(original_tests, encoding="utf-8")

        def rewrite_tests(*args, **kwargs):
            pdd_files["test"].write_text(rewritten_tests, encoding="utf-8")
            return True, "done", 1.0, "claude-code"

        mock_task.side_effect = rewrite_tests

        with pytest.raises(TestChurnError):
            run_one_session_sync(
                basename="my_module",
                language="python",
                pdd_files=pdd_files,
                project_root=tmp_path,
            )

        assert pdd_files["test"].read_text(encoding="utf-8") == original_tests

    # -----------------------------------------------------------------
    # Codex review (#1015) Finding 2 (iter-2): the one-session test
    # churn path must route through the PDD_REPAIR_DIRECTIVE retry loop
    # rather than fail immediately. Mirror the `_run_test_op_with_churn_retry`
    # contract in `sync_orchestration.py`: retry once, surface the
    # structured hard-failure block on exhaustion, and restore the
    # previous `PDD_REPAIR_DIRECTIVE` value in `finally`.
    # -----------------------------------------------------------------
    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_test_churn_round_trips_repair_directive_and_retries_once(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """One-session test churn must set `PDD_REPAIR_DIRECTIVE` from the
        exception and rerun the agentic session once. On the retry the env
        var MUST be visible. After the loop the prior env value MUST be
        restored. Codex review #1015 Finding 2 (iter-2)."""
        import os
        from pdd.code_generator_main import TestChurnError

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        # Seed a pre-existing repair directive so we can verify the restore
        # semantics: after the loop ends the prior value MUST be back.
        monkeypatch.setenv("PDD_REPAIR_DIRECTIVE", "pre-existing-directive")

        pdd_files = _make_pdd_files(tmp_path)
        original_tests = (
            "def test_a(): pass\n"
            "def test_b(): pass\n"
            "def test_c(): pass\n"
        )
        rewritten_tests = (
            "def test_new_a(): pass\n"
            "def test_new_b(): pass\n"
            "def test_new_c(): pass\n"
        )
        # An additive growth that does NOT trip the churn gate, so the
        # retry attempt's churn check passes and the loop exits cleanly.
        additive_tests = original_tests + "def test_d(): pass\n"
        pdd_files["test"].write_text(original_tests, encoding="utf-8")

        captured_env = {"first_directive": None, "second_directive": None}

        def fake_task(*args, **kwargs):
            call_count = mock_task.call_count  # already incremented for THIS call
            current_directive = os.environ.get("PDD_REPAIR_DIRECTIVE")
            if call_count == 1:
                captured_env["first_directive"] = current_directive
                # First session: rewrite tests heavily — trips the churn gate.
                pdd_files["test"].write_text(rewritten_tests, encoding="utf-8")
                return True, "done", 1.0, "claude-code"
            captured_env["second_directive"] = current_directive
            # Second session: additive growth — passes the churn gate.
            pdd_files["test"].write_text(additive_tests, encoding="utf-8")
            return True, "done", 0.5, "claude-code"

        mock_task.side_effect = fake_task

        result = run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        # Two attempts: original + one retry.
        assert mock_task.call_count == 2
        # First attempt: the stale outer directive was POPPED before the
        # loop (#1012, F-I), so the subprocess sees a CLEAN env. This
        # protects nested PDD CLI invocations the agent might launch
        # from inheriting the stale outer value.
        assert captured_env["first_directive"] is None
        # Second attempt saw the test-churn repair directive (set by the loop).
        assert captured_env["second_directive"] is not None
        assert "Test churn" in captured_env["second_directive"]
        # After the loop, the prior env value is restored.
        assert os.environ.get("PDD_REPAIR_DIRECTIVE") == "pre-existing-directive"
        # The retry succeeded — the result reflects success and accumulated cost.
        assert result["success"] is True
        assert result["total_cost"] == pytest.approx(1.5)

    # -----------------------------------------------------------------
    # Codex review (#1015) F-E (iter-8): the test-churn retry must
    # actually deliver the repair directive to the agent prompt, not
    # just set PDD_REPAIR_DIRECTIVE in the environment. The previous
    # implementation called `run_agentic_task(instruction=prompt, ...)`
    # with the SAME static `prompt` on every iteration; `run_agentic_task`
    # does NOT read `PDD_REPAIR_DIRECTIVE`. So although the env var was
    # set between attempts, the agent received the IDENTICAL instruction
    # and the repair loop could not actually repair.
    # -----------------------------------------------------------------
    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_test_churn_retry_injects_repair_directive_into_instruction(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """The retry attempt MUST receive an instruction that contains
        a `<test_repair_directive>` block carrying the prior churn
        error's repair_directive. The first attempt sees the unmodified
        base prompt."""
        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        original_tests = (
            "def test_a(): pass\n"
            "def test_b(): pass\n"
            "def test_c(): pass\n"
        )
        rewritten_tests = (
            "def test_new_a(): pass\n"
            "def test_new_b(): pass\n"
            "def test_new_c(): pass\n"
        )
        additive_tests = original_tests + "def test_d(): pass\n"
        pdd_files["test"].write_text(original_tests, encoding="utf-8")

        captured_instructions = []

        def fake_task(*args, **kwargs):
            captured_instructions.append(kwargs.get("instruction"))
            if mock_task.call_count == 1:
                # First session: rewrite tests heavily — trips the churn gate.
                pdd_files["test"].write_text(rewritten_tests, encoding="utf-8")
                return True, "done", 1.0, "claude-code"
            # Second session: additive growth — passes the churn gate.
            pdd_files["test"].write_text(additive_tests, encoding="utf-8")
            return True, "done", 0.5, "claude-code"

        mock_task.side_effect = fake_task

        run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        assert len(captured_instructions) == 2
        # First attempt: instruction is exactly the base prompt — no
        # repair directive was set yet.
        assert captured_instructions[0] == "mega prompt"
        assert "<test_repair_directive>" not in captured_instructions[0]
        # Second attempt: the instruction contains the directive block
        # carrying the prior churn error's repair_directive text.
        assert "<test_repair_directive>" in captured_instructions[1]
        assert "</test_repair_directive>" in captured_instructions[1]
        # The base prompt is still preserved in the retry instruction
        # (we append to it, we don't replace it).
        assert "mega prompt" in captured_instructions[1]
        # The TestChurnError.repair_directive default starts with
        # "Test churn repair required." — verify that text reached the
        # agent prompt rather than just the environment.
        assert "Test churn repair required" in captured_instructions[1]

    # -----------------------------------------------------------------
    # Codex review (#1015) F-E follow-up (iter-9): the instruction
    # rewrite MUST NOT read `PDD_REPAIR_DIRECTIVE` from the environment.
    # A stale outer value (set by the caller's shell, a parent
    # orchestration layer, or a prior PDD command) would otherwise
    # contaminate attempt 1's instruction with a `<test_repair_directive>`
    # block even though no one-session churn failure has occurred yet.
    # The retry contract is: directive appears on attempt 2+ only,
    # populated by THIS loop's TestChurnError.repair_directive.
    # -----------------------------------------------------------------
    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_first_attempt_instruction_ignores_stale_outer_env_directive(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """When `PDD_REPAIR_DIRECTIVE` is seeded by the caller before
        `run_one_session_sync` is invoked, attempt 1's instruction MUST
        equal the base prompt EXACTLY — no `<test_repair_directive>`
        block, no leaked stale text. Only failures raised inside this
        loop's churn-retry path populate the per-attempt directive."""
        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        monkeypatch.setenv("PDD_REPAIR_DIRECTIVE", "STALE-OUTER-DIRECTIVE")

        pdd_files = _make_pdd_files(tmp_path)
        # No pre-existing test file → churn gate does not run; we get a
        # single clean attempt and can inspect its instruction.
        captured_instructions = []

        def fake_task(*args, **kwargs):
            captured_instructions.append(kwargs.get("instruction"))
            return True, "done", 0.5, "claude-code"

        mock_task.side_effect = fake_task

        run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        assert len(captured_instructions) == 1
        # The stale outer directive must NOT contaminate attempt 1.
        assert captured_instructions[0] == "mega prompt"
        assert "<test_repair_directive>" not in captured_instructions[0]
        assert "STALE-OUTER-DIRECTIVE" not in captured_instructions[0]

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_first_attempt_with_existing_file_ignores_stale_outer_env_directive(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """Same guarantee even when a pre-existing test file exists and
        the churn gate is active: attempt 1 sees the base prompt only.
        Only the SECOND attempt (after a TestChurnError raised inside
        this loop) carries a `<test_repair_directive>` block, and that
        block contains THIS loop's churn-repair text — never the stale
        outer value."""
        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        monkeypatch.setenv("PDD_REPAIR_DIRECTIVE", "STALE-OUTER-DIRECTIVE")

        pdd_files = _make_pdd_files(tmp_path)
        original_tests = (
            "def test_a(): pass\n"
            "def test_b(): pass\n"
            "def test_c(): pass\n"
        )
        rewritten_tests = (
            "def test_new_a(): pass\n"
            "def test_new_b(): pass\n"
            "def test_new_c(): pass\n"
        )
        additive_tests = original_tests + "def test_d(): pass\n"
        pdd_files["test"].write_text(original_tests, encoding="utf-8")

        captured_instructions = []

        def fake_task(*args, **kwargs):
            captured_instructions.append(kwargs.get("instruction"))
            if mock_task.call_count == 1:
                pdd_files["test"].write_text(rewritten_tests, encoding="utf-8")
                return True, "done", 1.0, "claude-code"
            pdd_files["test"].write_text(additive_tests, encoding="utf-8")
            return True, "done", 0.5, "claude-code"

        mock_task.side_effect = fake_task

        run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        assert len(captured_instructions) == 2
        # Attempt 1: base prompt only — no stale-outer leak.
        assert captured_instructions[0] == "mega prompt"
        assert "STALE-OUTER-DIRECTIVE" not in captured_instructions[0]
        # Attempt 2: carries THIS loop's churn repair directive, NOT
        # the stale outer value.
        assert "<test_repair_directive>" in captured_instructions[1]
        assert "Test churn repair required" in captured_instructions[1]
        assert "STALE-OUTER-DIRECTIVE" not in captured_instructions[1]

    # -----------------------------------------------------------------
    # Codex review (#1015) F-I (iter-11): the one-session helper MUST
    # also pop `PDD_REPAIR_DIRECTIVE` from `os.environ` BEFORE attempt 1
    # so the subprocess spawned by `run_agentic_task` AND any
    # re-entrant PDD CLI process the agent launches inherit a CLEAN
    # env. Without this, the env-var-via-subprocess inheritance path
    # leaks a stale outer directive into nested `pdd test` / `pdd
    # generate` calls even though the in-process instruction is clean.
    # The prior outer env value MUST still be restored in `finally`.
    # -----------------------------------------------------------------
    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_first_attempt_pops_stale_env_for_subprocess_inheritance(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """When `PDD_REPAIR_DIRECTIVE` is seeded by the caller, attempt 1
        MUST run with the env var POPPED — so the subprocess spawned by
        `run_agentic_task` (and any nested PDD CLI invocations the
        agent launches) sees no stale value. The prior outer env value
        is restored in `finally` after the helper returns."""
        import os
        monkeypatch.setenv("PDD_REPAIR_DIRECTIVE", "STALE-OUTER")

        pdd_files = _make_pdd_files(tmp_path)
        # No pre-existing test file → single clean attempt; we can
        # inspect the env state the subprocess would have inherited.
        captured_env_during_call = {"value": "sentinel"}

        def fake_task(*args, **kwargs):
            captured_env_during_call["value"] = os.environ.get(
                "PDD_REPAIR_DIRECTIVE"
            )
            return True, "done", 0.5, "claude-code"

        mock_task.side_effect = fake_task

        run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        # During attempt 1 the env was clean — subprocess inheritance
        # cannot leak the stale outer value.
        assert captured_env_during_call["value"] is None
        # After the helper returns, the prior outer value is restored
        # exactly so we don't leak across operations.
        assert os.environ.get("PDD_REPAIR_DIRECTIVE") == "STALE-OUTER"

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_second_attempt_env_carries_in_loop_directive_not_stale(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """Attempt 2 MUST have the env var set to THIS loop's
        TestChurnError.repair_directive (NOT the stale outer value), so
        any nested PDD CLI subprocess inherits the correct directive."""
        import os
        monkeypatch.setenv("PDD_REPAIR_DIRECTIVE", "STALE-OUTER")
        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")

        pdd_files = _make_pdd_files(tmp_path)
        original_tests = (
            "def test_a(): pass\n"
            "def test_b(): pass\n"
            "def test_c(): pass\n"
        )
        rewritten_tests = (
            "def test_new_a(): pass\n"
            "def test_new_b(): pass\n"
            "def test_new_c(): pass\n"
        )
        additive_tests = original_tests + "def test_d(): pass\n"
        pdd_files["test"].write_text(original_tests, encoding="utf-8")

        captured_envs = []

        def fake_task(*args, **kwargs):
            captured_envs.append(os.environ.get("PDD_REPAIR_DIRECTIVE"))
            if mock_task.call_count == 1:
                pdd_files["test"].write_text(rewritten_tests, encoding="utf-8")
                return True, "done", 1.0, "claude-code"
            pdd_files["test"].write_text(additive_tests, encoding="utf-8")
            return True, "done", 0.5, "claude-code"

        mock_task.side_effect = fake_task

        run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        assert len(captured_envs) == 2
        # Attempt 1: env was popped — clean.
        assert captured_envs[0] is None
        # Attempt 2: env carries THIS loop's churn-repair directive,
        # not the stale outer value (so nested subprocesses inherit
        # the correct directive).
        assert captured_envs[1] is not None
        assert "STALE-OUTER" not in captured_envs[1]
        assert "Test churn repair required" in captured_envs[1]
        # After the helper returns, the prior outer value is restored.
        assert os.environ.get("PDD_REPAIR_DIRECTIVE") == "STALE-OUTER"

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_test_churn_exhaustion_emits_structured_block_once(
        self, mock_build, mock_task, tmp_path, monkeypatch, capsys
    ):
        """When the retry attempt ALSO trips the churn gate, the one-session
        path MUST emit the `=== test churn threshold exceeded ===` block
        exactly once and re-raise. Codex review #1015 Finding 2 (iter-2)."""
        from pdd.code_generator_main import TestChurnError

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        # Ensure no seeded directive remains afterwards.
        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        original_tests = (
            "def test_a(): pass\n"
            "def test_b(): pass\n"
            "def test_c(): pass\n"
        )
        # Two different rewrites so the churn-signature short-circuit does
        # NOT fire — we want to verify the loop actually retries once and
        # then surfaces the hard-failure block on exhaustion.
        rewrite_one = (
            "def test_one(): pass\n"
            "def test_two(): pass\n"
            "def test_three(): pass\n"
        )
        rewrite_two = (
            "def test_alpha(): pass\n"
            "def test_beta(): pass\n"
            "def test_gamma(): pass\n"
            "def test_delta(): pass\n"
        )
        pdd_files["test"].write_text(original_tests, encoding="utf-8")

        def fake_task(*args, **kwargs):
            call_count = mock_task.call_count
            if call_count == 1:
                pdd_files["test"].write_text(rewrite_one, encoding="utf-8")
                return True, "done", 1.0, "claude-code"
            pdd_files["test"].write_text(rewrite_two, encoding="utf-8")
            return True, "done", 0.5, "claude-code"

        mock_task.side_effect = fake_task

        with pytest.raises(TestChurnError) as excinfo:
            run_one_session_sync(
                basename="my_module",
                language="python",
                pdd_files=pdd_files,
                project_root=tmp_path,
            )

        captured = capsys.readouterr()

        # Retry happened (single retry per the documented semantics).
        assert mock_task.call_count == 2
        # Hard-failure diagnostic appears exactly once in stderr.
        assert captured.err.count("=== test churn threshold exceeded ===") == 1
        assert "Reproduce locally: pdd sync my_module" in captured.err
        # The pre-existing test file is restored (no high-churn rewrite left
        # on disk).
        assert pdd_files["test"].read_text(encoding="utf-8") == original_tests
        # Cost is accumulated across both failed attempts.
        assert excinfo.value.total_cost == pytest.approx(1.5)
        # PDD_REPAIR_DIRECTIVE is popped (it was unset originally).
        import os
        assert "PDD_REPAIR_DIRECTIVE" not in os.environ

    # -----------------------------------------------------------------
    # Codex review (#1015) Medium 1 (iter-3): the one-session helper
    # MUST short-circuit when the retry attempt produces the identical
    # ``(churn_ratio, pre_line_count)`` signature — no progress is
    # being made and an extra session would just burn cost. After the
    # short-circuit fires, the helper still has to restore the
    # original test file, restore the prior ``PDD_REPAIR_DIRECTIVE``,
    # raise ``TestChurnError`` with accumulated cost, and emit the
    # structured hard-failure block exactly once.
    # -----------------------------------------------------------------
    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_test_churn_short_circuits_on_identical_signature(
        self, mock_build, mock_task, tmp_path, monkeypatch, capsys
    ):
        """Identical ``(churn_ratio, pre_line_count)`` on the retry MUST trip
        the short-circuit branch — i.e. the helper stops at exactly 2
        attempts even when the configured cap allows many more.

        To make the short-circuit observably distinct from the natural
        max-attempt exhaustion path (where ``min(MAX_CONFORMANCE_ATTEMPTS,
        _MAX_TEST_CHURN_ATTEMPTS) == 2``), we lift BOTH constants to 5
        and feed the helper five consecutive identical-signature churn
        failures. With the short-circuit alive: 2 calls. Without the
        short-circuit (i.e. if the branch were deleted): 5 calls. The
        helper must still restore the test file, restore the prior
        ``PDD_REPAIR_DIRECTIVE``, accumulate cost across attempts, and
        emit the structured hard-failure block exactly once.
        """
        import os
        from pdd.code_generator_main import TestChurnError

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        # Seed a prior repair directive so we can verify restore behavior
        # under the short-circuit branch (separate from the natural
        # exhaustion exit path covered above).
        monkeypatch.setenv("PDD_REPAIR_DIRECTIVE", "pre-existing-directive")

        # Lift BOTH retry caps so natural exhaustion would yield 5 calls.
        # The short-circuit, if alive, still trips at 2 — which is what
        # the call-count assertion below verifies. ``MAX_CONFORMANCE_ATTEMPTS``
        # is imported inside the function from ``agentic_sync_runner``, so we
        # patch the canonical module-level binding.
        monkeypatch.setattr(
            "pdd.agentic_sync_runner.MAX_CONFORMANCE_ATTEMPTS", 5
        )
        monkeypatch.setattr(
            "pdd.one_session_sync._MAX_TEST_CHURN_ATTEMPTS", 5
        )

        pdd_files = _make_pdd_files(tmp_path)
        original_tests = (
            "def test_a(): pass\n"
            "def test_b(): pass\n"
            "def test_c(): pass\n"
        )
        # Five DIFFERENT rewrites of the SAME total line count. Because
        # `_compute_test_churn_ratio` keys on `max(added, removed) /
        # max(len(before_lines), 1)`, same-size complete rewrites
        # against the same `original_tests` yield identical churn
        # ratios — which, paired with the unchanged `pre_line_count`,
        # produces the identical signature the helper short-circuits on.
        rewrites = [
            "def test_one(): pass\ndef test_two(): pass\ndef test_three(): pass\n",
            "def test_alpha(): pass\ndef test_beta(): pass\ndef test_gamma(): pass\n",
            "def test_x(): pass\ndef test_y(): pass\ndef test_z(): pass\n",
            "def test_p(): pass\ndef test_q(): pass\ndef test_r(): pass\n",
            "def test_m(): pass\ndef test_n(): pass\ndef test_o(): pass\n",
        ]
        # Each attempt charges a distinct cost so the accumulated total
        # uniquely identifies how many attempts actually ran.
        costs = [1.0, 0.5, 0.25, 0.125, 0.0625]
        pdd_files["test"].write_text(original_tests, encoding="utf-8")

        def fake_task(*args, **kwargs):
            # mock_task.call_count is 1-indexed for the in-progress call.
            idx = mock_task.call_count - 1
            pdd_files["test"].write_text(rewrites[idx], encoding="utf-8")
            return True, "done", costs[idx], "claude-code"

        mock_task.side_effect = fake_task

        with pytest.raises(TestChurnError) as excinfo:
            run_one_session_sync(
                basename="my_module",
                language="python",
                pdd_files=pdd_files,
                project_root=tmp_path,
            )

        captured = capsys.readouterr()

        # Sanity: rewrites have the same line count vs the same
        # pre-existing file, so their churn signatures match.
        assert excinfo.value.pre_line_count == len(original_tests.splitlines())

        # The crux of the test: with the retry cap lifted to 5, only the
        # identical-signature short-circuit can stop the loop at 2. If the
        # short-circuit branch were removed, this assertion would observe 5.
        assert mock_task.call_count == 2
        # Hard-failure block emitted exactly once.
        assert captured.err.count("=== test churn threshold exceeded ===") == 1
        assert "Reproduce locally: pdd sync my_module" in captured.err
        # Original test file is restored — no high-churn rewrite is
        # left on disk.
        assert pdd_files["test"].read_text(encoding="utf-8") == original_tests
        # Cost from BOTH failed attempts is folded onto the raised
        # exception (1.0 + 0.5 = 1.5). If the short-circuit were absent
        # and all 5 attempts ran, this would be 1.9375.
        assert excinfo.value.total_cost == pytest.approx(1.5)
        # Prior PDD_REPAIR_DIRECTIVE is restored exactly to its seeded
        # value — the helper neither leaks the test-churn directive nor
        # drops the original.
        assert os.environ.get("PDD_REPAIR_DIRECTIVE") == "pre-existing-directive"

    # -----------------------------------------------------------------
    # Codex review (#1015) High 2 (iter-4): when the agent DELETES the
    # pre-existing test file mid-session, the churn gate must NOT
    # silently accept the deletion as a no-op. Deletion is the most
    # extreme form of coverage loss — treat it as maximal churn so the
    # repair-loop retry that handles wholesale rewrites also handles
    # deletions: restore the pre-existing file, set PDD_REPAIR_DIRECTIVE
    # from the deletion-specific directive, and rerun. On exhaustion
    # surface the structured hard-failure block exactly once.
    # -----------------------------------------------------------------
    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_test_file_deletion_treated_as_maximal_churn(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """If the agent deletes the pre-existing test file, the churn gate
        must restore the file and route through the same repair-loop retry
        that high-churn rewrites use. Codex review #1015 High 2 (iter-4)."""
        import os
        from pdd.code_generator_main import TestChurnError

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        original_tests = (
            "def test_a(): pass\n"
            "def test_b(): pass\n"
            "def test_c(): pass\n"
        )
        # An additive growth that does NOT trip the churn gate on retry,
        # so the loop exits cleanly after the deletion-driven retry runs.
        additive_tests = original_tests + "def test_d(): pass\n"
        pdd_files["test"].write_text(original_tests, encoding="utf-8")

        captured_env = {"first_directive": None, "second_directive": None}

        def fake_task(*args, **kwargs):
            call_count = mock_task.call_count
            captured_env_key = f"{'first' if call_count == 1 else 'second'}_directive"
            captured_env[captured_env_key] = os.environ.get("PDD_REPAIR_DIRECTIVE")
            if call_count == 1:
                # First session: DELETE the pre-existing test file.
                pdd_files["test"].unlink()
                return True, "done", 1.0, "claude-code"
            # Second session: additive growth — passes the churn gate.
            pdd_files["test"].write_text(additive_tests, encoding="utf-8")
            return True, "done", 0.5, "claude-code"

        mock_task.side_effect = fake_task

        result = run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        # Two attempts: deletion-detected + repair retry that succeeded.
        assert mock_task.call_count == 2
        # First attempt saw no directive (no churn signaled yet).
        assert captured_env["first_directive"] is None
        # Second attempt saw the deletion-specific repair directive.
        assert captured_env["second_directive"] is not None
        assert "DELETED" in captured_env["second_directive"]
        # After deletion was detected, the file was restored before retry.
        # The retry's additive write then sticks, so the final on-disk
        # content reflects the successful retry.
        assert pdd_files["test"].read_text(encoding="utf-8") == additive_tests
        # Retry succeeded — result reflects success and accumulated cost.
        assert result["success"] is True
        assert result["total_cost"] == pytest.approx(1.5)
        # PDD_REPAIR_DIRECTIVE was unset originally; should be popped.
        assert "PDD_REPAIR_DIRECTIVE" not in os.environ

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_test_file_deletion_exhausts_to_hard_failure(
        self, mock_build, mock_task, tmp_path, monkeypatch, capsys
    ):
        """If the agent keeps deleting the test file across attempts, the
        loop must exhaust to the structured hard-failure block (emitted
        once) and the pre-existing test file must be restored on disk."""
        import os
        from pdd.code_generator_main import TestChurnError

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        original_tests = (
            "def test_a(): pass\n"
            "def test_b(): pass\n"
            "def test_c(): pass\n"
        )
        pdd_files["test"].write_text(original_tests, encoding="utf-8")

        def fake_task(*args, **kwargs):
            # Both sessions: delete the pre-existing test file. The first
            # deletion produces signature (1.00, 3); the second deletion
            # after the restore produces the SAME signature, which trips
            # the identical-signature short-circuit at exactly 2 attempts.
            if pdd_files["test"].exists():
                pdd_files["test"].unlink()
            return True, "done", 1.0, "claude-code"

        mock_task.side_effect = fake_task

        with pytest.raises(TestChurnError) as excinfo:
            run_one_session_sync(
                basename="my_module",
                language="python",
                pdd_files=pdd_files,
                project_root=tmp_path,
            )

        captured = capsys.readouterr()

        # Two attempts (identical signature short-circuit fires).
        assert mock_task.call_count == 2
        # The raised exception reports maximal churn.
        assert excinfo.value.churn_ratio == pytest.approx(1.0)
        assert excinfo.value.pre_line_count == len(original_tests.splitlines())
        # Structured hard-failure diagnostic emitted exactly once.
        assert captured.err.count("=== test churn threshold exceeded ===") == 1
        # The pre-existing test file is restored — deletion is not allowed
        # to persist on disk.
        assert pdd_files["test"].read_text(encoding="utf-8") == original_tests
        # PDD_REPAIR_DIRECTIVE was unset originally; should be popped.
        assert "PDD_REPAIR_DIRECTIVE" not in os.environ

    # -----------------------------------------------------------------
    # Codex review (#1015) P1.A (iter-13): `pdd sync --one-session`
    # bypasses the public-surface gate because sync_main skips
    # `code_generator_main` when the code file already exists, then
    # hands off to `run_one_session_sync` which previously only
    # verified test churn. Add the same gate to run_one_session_sync
    # so a mature module's API surface is protected through the
    # one-session path too.
    # -----------------------------------------------------------------
    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_one_session_catches_public_surface_regression_in_code(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """When the one-session agent rewrites the code file removing a
        top-level public function, run_one_session_sync MUST raise
        `PublicSurfaceRegressionError`, restore the pre-session code
        file, and emit the structured hard-failure block."""
        from pdd.code_generator_main import PublicSurfaceRegressionError

        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        original_code = (
            "def public_one():\n    return 1\n"
            "def public_two():\n    return 2\n"
        )
        # Two different rewrites so the identical-signature short-circuit
        # fires at exactly 2 attempts (each rewrite removes a different
        # subset of the original symbols).
        rewrite_one = "def public_one():\n    return 1\n"
        rewrite_two = "def public_two():\n    return 2\n"
        pdd_files["code"].write_text(original_code, encoding="utf-8")

        def fake_task(*args, **kwargs):
            if mock_task.call_count == 1:
                pdd_files["code"].write_text(rewrite_one, encoding="utf-8")
            else:
                pdd_files["code"].write_text(rewrite_two, encoding="utf-8")
            return True, "done", 1.0, "claude-code"

        mock_task.side_effect = fake_task

        with pytest.raises(PublicSurfaceRegressionError) as excinfo:
            run_one_session_sync(
                basename="my_module",
                language="python",
                pdd_files=pdd_files,
                project_root=tmp_path,
            )

        # The pre-session code file is restored — broken code does not
        # persist on disk.
        assert pdd_files["code"].read_text(encoding="utf-8") == original_code
        # A removed symbol surfaces in the exception. The raised
        # exception is the LAST attempt's, so it reflects what the
        # final rewrite dropped (in this test, attempt 2's rewrite
        # keeps `public_two` but drops `public_one`).
        assert "public_one" in excinfo.value.removed_symbols

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_one_session_surface_regression_emits_structured_block(
        self, mock_build, mock_task, tmp_path, monkeypatch, capsys
    ):
        """On exhaustion the public-surface hard-failure block is
        emitted to stderr exactly once."""
        from pdd.code_generator_main import PublicSurfaceRegressionError

        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        original_code = (
            "def public_one():\n    return 1\n"
            "def public_two():\n    return 2\n"
        )
        rewrite_one = "def public_one():\n    return 1\n"
        rewrite_two = "def public_two():\n    return 2\n"
        pdd_files["code"].write_text(original_code, encoding="utf-8")

        def fake_task(*args, **kwargs):
            if mock_task.call_count == 1:
                pdd_files["code"].write_text(rewrite_one, encoding="utf-8")
            else:
                pdd_files["code"].write_text(rewrite_two, encoding="utf-8")
            return True, "done", 1.0, "claude-code"

        mock_task.side_effect = fake_task

        with pytest.raises(PublicSurfaceRegressionError):
            run_one_session_sync(
                basename="my_module",
                language="python",
                pdd_files=pdd_files,
                project_root=tmp_path,
            )

        captured = capsys.readouterr()
        # The public-surface hard-failure block is emitted exactly once.
        assert captured.err.count("=== public surface regression ===") == 1
        # And the test-churn block is NOT emitted (the surface gate
        # short-circuits before the churn gate runs).
        assert "=== test churn threshold exceeded ===" not in captured.err

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_one_session_surface_regression_retries_with_directive(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """When attempt 1 trips the public-surface gate but attempt 2
        produces a valid surface, the loop succeeds. Attempt 2's
        instruction must contain `<test_repair_directive>` carrying
        the prior PublicSurfaceRegressionError's repair_directive."""
        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        original_code = (
            "def public_one():\n    return 1\n"
            "def public_two():\n    return 2\n"
        )
        # Attempt 1: drops `public_two`. Attempt 2: restores the full
        # surface (no churn either since the test file isn't touched).
        rewrite_bad = "def public_one():\n    return 1\n"
        rewrite_good = original_code  # restores public_two
        pdd_files["code"].write_text(original_code, encoding="utf-8")

        captured_instructions = []

        def fake_task(*args, **kwargs):
            captured_instructions.append(kwargs.get("instruction"))
            if mock_task.call_count == 1:
                pdd_files["code"].write_text(rewrite_bad, encoding="utf-8")
            else:
                pdd_files["code"].write_text(rewrite_good, encoding="utf-8")
            return True, "done", 0.5, "claude-code"

        mock_task.side_effect = fake_task

        result = run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        # Two attempts: first failed surface gate, second restored
        # the full surface and succeeded.
        assert mock_task.call_count == 2
        # Attempt 1: base prompt (no directive).
        assert captured_instructions[0] == "mega prompt"
        assert "<test_repair_directive>" not in captured_instructions[0]
        # Attempt 2: carries the public-surface repair directive.
        assert "<test_repair_directive>" in captured_instructions[1]
        assert "Public surface regression repair required" in captured_instructions[1]
        assert "public_two" in captured_instructions[1]
        # Result reflects success and accumulated cost across attempts.
        assert result["success"] is True
        assert result["total_cost"] == pytest.approx(1.0)
        # Final on-disk code matches the good rewrite.
        assert pdd_files["code"].read_text(encoding="utf-8") == rewrite_good

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_one_session_surface_regression_allowed_by_breaking_change(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """An anchored `BREAKING-CHANGE: remove public_two` directive in
        the prompt opts the removal out — no PublicSurfaceRegressionError
        is raised."""
        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        # Append BREAKING-CHANGE to the prompt body so the gate's
        # opt-out parser whitelists `public_two`.
        pdd_files["prompt"].write_text(
            pdd_files["prompt"].read_text(encoding="utf-8")
            + "\n\nBREAKING-CHANGE: remove public_two\n",
            encoding="utf-8",
        )

        original_code = (
            "def public_one():\n    return 1\n"
            "def public_two():\n    return 2\n"
        )
        rewrite = "def public_one():\n    return 1\n"
        pdd_files["code"].write_text(original_code, encoding="utf-8")

        def fake_task(*args, **kwargs):
            pdd_files["code"].write_text(rewrite, encoding="utf-8")
            return True, "done", 0.5, "claude-code"

        mock_task.side_effect = fake_task

        # Must NOT raise — BREAKING-CHANGE opt-out is honored.
        result = run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        assert result["success"] is True
        # The agent's rewrite is preserved on disk (not restored).
        assert pdd_files["code"].read_text(encoding="utf-8") == rewrite

    # Codex review (#1015) F-K (iter-16): `PDD_SKIP_CONFORMANCE=1`
    # must disable BOTH the surface gate AND the test-churn gate
    # inside `run_one_session_sync`. Test each independently below.
    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_one_session_surface_gate_honors_skip_conformance(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """`PDD_SKIP_CONFORMANCE=1` MUST disable the public-surface gate
        in `run_one_session_sync` — the agent may drop a public symbol
        without raising."""
        monkeypatch.setenv("PDD_SKIP_CONFORMANCE", "1")
        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        original_code = (
            "def public_one():\n    return 1\n"
            "def public_two():\n    return 2\n"
        )
        rewrite = "def public_one():\n    return 1\n"  # drops public_two
        pdd_files["code"].write_text(original_code, encoding="utf-8")

        def fake_task(*args, **kwargs):
            pdd_files["code"].write_text(rewrite, encoding="utf-8")
            return True, "done", 0.5, "claude-code"

        mock_task.side_effect = fake_task

        # Must NOT raise — umbrella flag disables the gate.
        result = run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        assert result["success"] is True
        # Agent's rewrite is preserved on disk (not restored).
        assert pdd_files["code"].read_text(encoding="utf-8") == rewrite

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_one_session_churn_gate_honors_skip_conformance(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """`PDD_SKIP_CONFORMANCE=1` MUST disable the test-churn gate
        in `run_one_session_sync` — covers both the wholesale-rewrite
        path (via `_verify_test_churn`) AND the deletion-as-churn
        shortcut that raises `TestChurnError` directly. Use a high-
        churn rewrite so without the flag the gate would fire."""
        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        monkeypatch.setenv("PDD_SKIP_CONFORMANCE", "1")
        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        original_tests = (
            "def test_a(): pass\n"
            "def test_b(): pass\n"
            "def test_c(): pass\n"
        )
        rewritten_tests = (
            "def test_new_a(): pass\n"
            "def test_new_b(): pass\n"
            "def test_new_c(): pass\n"
        )
        pdd_files["test"].write_text(original_tests, encoding="utf-8")

        def fake_task(*args, **kwargs):
            pdd_files["test"].write_text(rewritten_tests, encoding="utf-8")
            return True, "done", 0.5, "claude-code"

        mock_task.side_effect = fake_task

        # Without the umbrella flag this would raise TestChurnError;
        # with the flag, the call must complete successfully.
        result = run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        assert result["success"] is True
        # Test file holds the agent's rewrite (NOT restored).
        assert pdd_files["test"].read_text(encoding="utf-8") == rewritten_tests

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_one_session_deletion_gate_honors_skip_conformance(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """`PDD_SKIP_CONFORMANCE=1` MUST also disable the deletion-as-
        churn shortcut (the direct `raise TestChurnError` path that
        bypasses `_verify_test_churn`)."""
        monkeypatch.setenv("PDD_SKIP_CONFORMANCE", "1")
        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        original_tests = (
            "def test_a(): pass\n"
            "def test_b(): pass\n"
        )
        pdd_files["test"].write_text(original_tests, encoding="utf-8")

        def fake_task(*args, **kwargs):
            # Simulate agent deleting the test file mid-session.
            if pdd_files["test"].exists():
                pdd_files["test"].unlink()
            return True, "done", 0.5, "claude-code"

        mock_task.side_effect = fake_task

        # Without the umbrella flag this would raise TestChurnError
        # with ratio=1.0; with the flag, the call must complete
        # successfully and the deletion is accepted.
        result = run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        assert result["success"] is True
        # Test file remains deleted (NOT restored — umbrella flag
        # opted out of the gate entirely).
        assert not pdd_files["test"].exists()

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_one_session_deletion_gate_honors_prompt_breaking_change(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """An anchored ``BREAKING-CHANGE: rewrite tests`` directive in
        the prompt MUST disable the deletion-as-churn shortcut, so the
        deletion path is symmetric with the wholesale-rewrite path
        (which already honors the prompt opt-out via
        ``_verify_test_churn`` → ``_prompt_allows_test_churn``). Without
        this symmetry, the prompt-based opt-out works when the agent
        rewrites the test file but silently fails when the agent
        empties/deletes it."""
        monkeypatch.delenv("PDD_SKIP_TEST_CHURN_GATE", raising=False)
        monkeypatch.delenv("PDD_SKIP_CONFORMANCE", raising=False)
        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        pdd_files["prompt"].write_text(
            "Module spec for my_module.\n"
            "BREAKING-CHANGE: rewrite tests for the new helper API\n",
            encoding="utf-8",
        )
        original_tests = (
            "def test_a(): pass\n"
            "def test_b(): pass\n"
        )
        pdd_files["test"].write_text(original_tests, encoding="utf-8")

        def fake_task(*args, **kwargs):
            if pdd_files["test"].exists():
                pdd_files["test"].unlink()
            return True, "done", 0.5, "claude-code"

        mock_task.side_effect = fake_task

        result = run_one_session_sync(
            basename="my_module",
            language="python",
            pdd_files=pdd_files,
            project_root=tmp_path,
        )

        assert result["success"] is True
        # Deletion accepted (NOT restored) because the prompt explicitly
        # opted out of the test-churn gate.
        assert not pdd_files["test"].exists()

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_one_session_surface_gate_runs_before_churn_gate(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """If BOTH gates would fire (code surface broken AND test file
        heavily churned), the surface gate wins because the surface
        check runs FIRST inside the try block. The churn check is
        skipped via `continue` so the agent's broken state is restored
        for the retry."""
        from pdd.code_generator_main import PublicSurfaceRegressionError

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        original_code = (
            "def public_one():\n    return 1\n"
            "def public_two():\n    return 2\n"
        )
        original_tests = (
            "def test_a(): pass\n"
            "def test_b(): pass\n"
            "def test_c(): pass\n"
        )
        # Both rewrites: drop a code symbol AND rewrite the test file
        # heavily. Two different rewrites so the surface short-circuit
        # fires at exactly 2 attempts.
        code_rewrite_one = "def public_one():\n    return 1\n"
        code_rewrite_two = "def public_two():\n    return 2\n"
        test_rewrite = (
            "def test_new_a(): pass\n"
            "def test_new_b(): pass\n"
            "def test_new_c(): pass\n"
        )
        pdd_files["code"].write_text(original_code, encoding="utf-8")
        pdd_files["test"].write_text(original_tests, encoding="utf-8")

        def fake_task(*args, **kwargs):
            if mock_task.call_count == 1:
                pdd_files["code"].write_text(code_rewrite_one, encoding="utf-8")
            else:
                pdd_files["code"].write_text(code_rewrite_two, encoding="utf-8")
            pdd_files["test"].write_text(test_rewrite, encoding="utf-8")
            return True, "done", 1.0, "claude-code"

        mock_task.side_effect = fake_task

        # Surface gate wins.
        with pytest.raises(PublicSurfaceRegressionError):
            run_one_session_sync(
                basename="my_module",
                language="python",
                pdd_files=pdd_files,
                project_root=tmp_path,
            )

        # Pre-session code is restored (surface gate's restore).
        assert pdd_files["code"].read_text(encoding="utf-8") == original_code

    # -----------------------------------------------------------------
    # Codex review (#1015) P2.B (iter-14): when the surface gate fires
    # and the agent had ALSO rewritten the test file in the same
    # session, the test file from the failed attempt was left dirty on
    # disk (the surface except-branch `continue`s before the churn
    # gate runs, and the churn gate is the one that normally restores
    # the test file). The surface except branch must ALSO restore the
    # pre-session test file when one exists.
    # -----------------------------------------------------------------
    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_one_session_surface_failure_also_restores_test_file(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """On surface failure with retry exhaustion, BOTH the code file
        AND the test file MUST be restored to their pre-session
        content. Without P2.B, the test file from the failed attempt
        sat on disk."""
        from pdd.code_generator_main import PublicSurfaceRegressionError

        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        original_code = (
            "def public_one():\n    return 1\n"
            "def public_two():\n    return 2\n"
        )
        original_tests = (
            "def test_a(): pass\n"
            "def test_b(): pass\n"
            "def test_c(): pass\n"
        )
        # Two different code rewrites so the identical-signature
        # short-circuit fires at exactly 2 attempts (each drops a
        # different public symbol).
        code_bad_one = "def public_one():\n    return 1\n"  # drops public_two
        code_bad_two = "def public_two():\n    return 2\n"  # drops public_one
        # The agent also rewrites the test file heavily on each attempt.
        test_rewrite = (
            "def test_new_a(): pass\n"
            "def test_new_b(): pass\n"
            "def test_new_c(): pass\n"
        )
        pdd_files["code"].write_text(original_code, encoding="utf-8")
        pdd_files["test"].write_text(original_tests, encoding="utf-8")

        def fake_task(*args, **kwargs):
            if mock_task.call_count == 1:
                pdd_files["code"].write_text(code_bad_one, encoding="utf-8")
            else:
                pdd_files["code"].write_text(code_bad_two, encoding="utf-8")
            pdd_files["test"].write_text(test_rewrite, encoding="utf-8")
            return True, "done", 1.0, "claude-code"

        mock_task.side_effect = fake_task

        with pytest.raises(PublicSurfaceRegressionError):
            run_one_session_sync(
                basename="my_module",
                language="python",
                pdd_files=pdd_files,
                project_root=tmp_path,
            )

        # Both pre-session files must be restored on disk — even though
        # the surface block is what surfaces, the disk state is clean.
        assert pdd_files["code"].read_text(encoding="utf-8") == original_code
        assert pdd_files["test"].read_text(encoding="utf-8") == original_tests

    # -----------------------------------------------------------------
    # Codex review (#1015) P3.B (iter-15): the P2.B restore branch
    # previously used `if existing_test_content:` (truthiness). An
    # empty pre-session test file would be skipped because empty
    # string is falsy. Use `is not None` instead so the empty
    # zero-byte state is also restored when the agent
    # rewrote/deleted the file.
    # -----------------------------------------------------------------
    @patch("pdd.one_session_sync.run_agentic_task")
    @patch("pdd.one_session_sync.build_one_session_prompt", return_value="mega prompt")
    def test_one_session_surface_failure_restores_empty_pre_session_test_file(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """If the pre-session test file exists but is empty, the surface
        gate's restore branch MUST still write the empty content back
        (so the agent's rewrite is removed). Using truthiness instead
        of `is not None` would skip this case."""
        from pdd.code_generator_main import PublicSurfaceRegressionError

        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        original_code = (
            "def public_one():\n    return 1\n"
            "def public_two():\n    return 2\n"
        )
        # Empty pre-session test file (zero bytes).
        pdd_files["code"].write_text(original_code, encoding="utf-8")
        pdd_files["test"].write_text("", encoding="utf-8")

        # Two different bad rewrites so the identical-signature
        # short-circuit fires at 2 attempts (each drops a different
        # public symbol).
        code_bad_one = "def public_one():\n    return 1\n"
        code_bad_two = "def public_two():\n    return 2\n"
        # Agent also fills the empty test file with content on each
        # attempt — restoration should wipe it back to empty.
        agent_test_rewrite = (
            "def test_new_a(): pass\n"
            "def test_new_b(): pass\n"
        )

        def fake_task(*args, **kwargs):
            if mock_task.call_count == 1:
                pdd_files["code"].write_text(code_bad_one, encoding="utf-8")
            else:
                pdd_files["code"].write_text(code_bad_two, encoding="utf-8")
            pdd_files["test"].write_text(agent_test_rewrite, encoding="utf-8")
            return True, "done", 1.0, "claude-code"

        mock_task.side_effect = fake_task

        with pytest.raises(PublicSurfaceRegressionError):
            run_one_session_sync(
                basename="my_module",
                language="python",
                pdd_files=pdd_files,
                project_root=tmp_path,
            )

        # The empty pre-session test file is restored to its empty
        # state — NOT left holding the agent's rewrite.
        assert pdd_files["test"].read_text(encoding="utf-8") == ""


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
    @patch("pdd.sync_main.get_pdd_file_paths")
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
    @patch("pdd.sync_main.get_pdd_file_paths")
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
    @patch("pdd.sync_main.get_pdd_file_paths")
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
    @patch("pdd.sync_main.get_pdd_file_paths")
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
    @patch("pdd.sync_main.get_pdd_file_paths")
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


# ---------------------------------------------------------------------------
# Bug: one-session sync result dict uses "errors" but summary uses "error" (#826)
# ---------------------------------------------------------------------------

class TestOneSessionResultErrorKey:
    """run_one_session_sync returns {"errors": [...]} but sync_main's summary
    table reads result.get("error") — the key mismatch causes all one-session
    errors to display as 'No details.' instead of the actual error message."""

    def test_result_dict_has_error_singular_key_on_failure(self):
        """Failed one-session result must include 'error' (singular) key
        so sync_main's summary table can display the error message."""
        from pdd.one_session_sync import run_one_session_sync
        from unittest.mock import patch, MagicMock
        import tempfile, os

        with tempfile.TemporaryDirectory() as tmp:
            prompt_file = os.path.join(tmp, "test.prompt")
            code_file = os.path.join(tmp, "test.tsx")
            with open(prompt_file, "w") as f:
                f.write("test prompt")

            pdd_files = {
                "prompt": MagicMock(exists=MagicMock(return_value=True)),
                "code": MagicMock(),
                "test": MagicMock(),
                "example": MagicMock(),
            }
            pdd_files["prompt"].__str__ = lambda self: prompt_file
            pdd_files["prompt"].read_text = MagicMock(return_value="test prompt")
            pdd_files["code"].__str__ = lambda self: code_file

            with patch("pdd.one_session_sync.run_agentic_task") as mock_agent:
                mock_agent.return_value = (False, "Agent failed: no providers", 0.0, "")
                from pathlib import Path
                result = run_one_session_sync(
                    basename="test_module",
                    language="typescriptreact",
                    pdd_files=pdd_files,
                    project_root=Path(tmp),
                    verbose=False,
                    quiet=True,
                )

            assert not result["success"]
            assert "error" in result, (
                f"One-session result must have 'error' (singular) key for sync_main summary table. "
                f"Got keys: {list(result.keys())}. The summary table reads result.get('error') "
                f"and falls back to 'No details.' when this key is missing."
            )
            assert result["error"], "Error message should not be empty"


# ---------------------------------------------------------------------------
# Codex review #1015 iter-1, Important 2
# ---------------------------------------------------------------------------
class TestOneSessionSurfaceRetryBudget:
    """Split retry budgets: public-surface repair gets the FULL
    ``MAX_CONFORMANCE_ATTEMPTS`` budget while test-churn keeps its tighter
    ``_MAX_TEST_CHURN_ATTEMPTS`` cap. Before this fix, both gates shared
    ``min(MAX_CONFORMANCE_ATTEMPTS, _MAX_TEST_CHURN_ATTEMPTS)`` so a
    surface failure was capped at 2 attempts even though the generate
    path got the full 3.
    """

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch(
        "pdd.one_session_sync.build_one_session_prompt",
        return_value="mega prompt",
    )
    def test_surface_failures_use_max_conformance_attempts(
        self, mock_build, mock_task, tmp_path, monkeypatch, capsys
    ):
        """Three DISTINCT surface failures (different removed symbol each
        time) must each get an attempt — the surface counter caps at
        ``MAX_CONFORMANCE_ATTEMPTS`` (=3), not ``_MAX_TEST_CHURN_ATTEMPTS`` (=2).
        Distinct signatures defeat the identical-signature short-circuit
        so the loop actually exhausts the surface budget instead of
        bailing on attempt 2.
        """
        from pdd.code_generator_main import PublicSurfaceRegressionError
        from pdd.agentic_sync_runner import MAX_CONFORMANCE_ATTEMPTS

        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        # Pre-session code defines THREE public helpers. Each attempt
        # below drops a different one to keep the surface-error
        # signature unique across attempts (avoiding the
        # identical-signature short-circuit).
        original_code = (
            "def public_one():\n    return 1\n"
            "def public_two():\n    return 2\n"
            "def public_three():\n    return 3\n"
        )
        pdd_files["code"].write_text(original_code, encoding="utf-8")

        # Each attempt drops a different symbol → distinct surface
        # signatures so the identical-signature short-circuit does NOT
        # cut the loop short.
        per_attempt_rewrites = [
            # Attempt 1: drop public_three.
            "def public_one():\n    return 1\n"
            "def public_two():\n    return 2\n",
            # Attempt 2: drop public_two (different signature).
            "def public_one():\n    return 1\n"
            "def public_three():\n    return 3\n",
            # Attempt 3: drop public_one (different signature again).
            "def public_two():\n    return 2\n"
            "def public_three():\n    return 3\n",
        ]

        def fake_task(*args, **kwargs):
            idx = mock_task.call_count - 1
            rewrite = per_attempt_rewrites[idx]
            pdd_files["code"].write_text(rewrite, encoding="utf-8")
            return True, "done", 1.0, "claude-code"

        mock_task.side_effect = fake_task

        with pytest.raises(PublicSurfaceRegressionError):
            run_one_session_sync(
                basename="my_module",
                language="python",
                pdd_files=pdd_files,
                project_root=tmp_path,
            )

        # The full MAX_CONFORMANCE_ATTEMPTS budget was used (NOT capped
        # at 2 by the old shared ``_MAX_TEST_CHURN_ATTEMPTS`` limit).
        # This is the Important-2 regression: pre-fix the loop bailed
        # after 2 attempts even when the surface gate had budget left.
        assert mock_task.call_count == MAX_CONFORMANCE_ATTEMPTS, (
            f"Expected surface repair to use full MAX_CONFORMANCE_ATTEMPTS "
            f"(={MAX_CONFORMANCE_ATTEMPTS}) budget; got {mock_task.call_count}. "
            f"The churn cap (=2) must NOT apply to public-surface repair."
        )

        captured = capsys.readouterr()
        # Hard-failure block emitted once after exhaustion.
        assert captured.err.count("=== public surface regression ===") == 1

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch(
        "pdd.one_session_sync.build_one_session_prompt",
        return_value="mega prompt",
    )
    def test_churn_failures_still_cap_at_two_attempts(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """Test-churn keeps its tighter ``_MAX_TEST_CHURN_ATTEMPTS`` cap.
        Two DISTINCT churn failures (different ratio each time) must NOT
        exceed the churn budget even though the outer loop runs for
        ``MAX_CONFORMANCE_ATTEMPTS`` iterations.
        """
        from pdd.code_generator_main import TestChurnError
        from pdd.one_session_sync import _MAX_TEST_CHURN_ATTEMPTS

        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)
        # Drive the churn threshold low and ensure the churn gate sees
        # rewrites as high-churn. Existing test file is several lines so
        # a wholesale rewrite registers > 0.40 ratio.
        pdd_files = _make_pdd_files(tmp_path)
        # Code stays untouched across attempts so the surface gate
        # never fires; only churn fires.
        pdd_files["code"].write_text(
            "def public_one():\n    return 1\n", encoding="utf-8"
        )
        # Pre-existing test file with several real test cases — a
        # wholesale single-test rewrite trips the > 0.40 churn ratio.
        existing_tests = "\n".join(
            f"def test_case_{i}():\n    assert True" for i in range(40)
        )
        pdd_files["test"].write_text(existing_tests, encoding="utf-8")

        # Each attempt writes a DIFFERENT wholesale rewrite so the churn
        # signature stays distinct (different post-line-count avoids the
        # identical-signature short-circuit).
        per_attempt_test_rewrites = [
            "def test_new_one():\n    assert True\n",
            "def test_new_two():\n    assert True\nx = 1\n",
            "def test_new_three():\n    pass\ny = 2\nz = 3\n",
        ]

        def fake_task(*args, **kwargs):
            idx = mock_task.call_count - 1
            # Always write a high-churn test rewrite for this attempt.
            pdd_files["test"].write_text(
                per_attempt_test_rewrites[
                    min(idx, len(per_attempt_test_rewrites) - 1)
                ],
                encoding="utf-8",
            )
            return True, "done", 1.0, "claude-code"

        mock_task.side_effect = fake_task

        with pytest.raises(TestChurnError):
            run_one_session_sync(
                basename="my_module",
                language="python",
                pdd_files=pdd_files,
                project_root=tmp_path,
            )

        # Churn budget = 2 (pre-fix behavior preserved). The outer loop
        # still has headroom for MAX_CONFORMANCE_ATTEMPTS iterations but
        # the churn-specific counter caps at _MAX_TEST_CHURN_ATTEMPTS.
        assert mock_task.call_count == _MAX_TEST_CHURN_ATTEMPTS, (
            f"Expected churn repair to cap at _MAX_TEST_CHURN_ATTEMPTS "
            f"(={_MAX_TEST_CHURN_ATTEMPTS}); got {mock_task.call_count}. "
            f"The split-budget refactor must NOT widen the churn cap."
        )


class TestOneSessionRollback:
    """External review (PR #1015): the ``except TestChurnError`` handler in
    ``run_one_session_sync`` used to restore only the test file; the code
    file mutated by the same attempt was left on disk. Subsequent
    ``pdd sync`` invocations would then treat the mutated code as the
    baseline. Mirror the ``PublicSurfaceRegressionError`` handler's
    restore-both-files pattern so a rejected attempt leaves disk in the
    pre-attempt state.
    """

    @patch("pdd.one_session_sync.run_agentic_task")
    @patch(
        "pdd.one_session_sync.build_one_session_prompt",
        return_value="mega prompt",
    )
    def test_test_churn_restores_code_and_test(
        self, mock_build, mock_task, tmp_path, monkeypatch
    ):
        """A failed one-session attempt that rewrites BOTH the code file
        and the test file (where the test rewrite trips the churn gate)
        MUST leave both files at their pre-session bytes after the
        ``TestChurnError`` propagates."""
        from pdd.code_generator_main import TestChurnError

        monkeypatch.setenv("PDD_TEST_CHURN_THRESHOLD", "0.40")
        monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

        pdd_files = _make_pdd_files(tmp_path)
        original_code = "def hello():\n    return 'world'\n"
        original_tests = (
            "def test_a(): pass\n"
            "def test_b(): pass\n"
            "def test_c(): pass\n"
        )
        # Mutated bytes for THIS attempt — the rewrite trips the churn gate
        # (wholesale test replacement at >0.40 ratio) AND the code file is
        # silently overwritten. Pre-fix, only the test file was restored;
        # ``code_path`` retained the mutated bytes after rejection.
        mutated_code = "def hello():\n    return 'mutated'\n"
        mutated_tests = (
            "def test_x(): pass\n"
            "def test_y(): pass\n"
            "def test_z(): pass\n"
        )
        # A different distinct rewrite per attempt so the
        # identical-signature short-circuit does NOT cut the loop short
        # before the churn budget is fully exhausted (and we still see
        # the final ``TestChurnError``).
        per_attempt_test_rewrites = [
            mutated_tests,
            "def test_alt(): pass\nx = 1\n",
        ]
        pdd_files["code"].write_text(original_code, encoding="utf-8")
        pdd_files["test"].write_text(original_tests, encoding="utf-8")

        def rewrite_both(*args, **kwargs):
            # Both the code AND the test are mutated by the agentic
            # session. The code mutation by itself is benign (no public
            # surface regression), so only the churn gate fires.
            pdd_files["code"].write_text(mutated_code, encoding="utf-8")
            idx = mock_task.call_count - 1
            pdd_files["test"].write_text(
                per_attempt_test_rewrites[
                    min(idx, len(per_attempt_test_rewrites) - 1)
                ],
                encoding="utf-8",
            )
            return True, "done", 1.0, "claude-code"

        mock_task.side_effect = rewrite_both

        with pytest.raises(TestChurnError):
            run_one_session_sync(
                basename="my_module",
                language="python",
                pdd_files=pdd_files,
                project_root=tmp_path,
            )

        # Both files restored to pre-session bytes. Pre-fix, only the
        # test file would be restored; the code file would retain
        # ``mutated_code``.
        assert (
            pdd_files["code"].read_text(encoding="utf-8") == original_code
        ), "code file must be rolled back when TestChurnError fires"
        assert (
            pdd_files["test"].read_text(encoding="utf-8") == original_tests
        ), "test file must be rolled back when TestChurnError fires"
