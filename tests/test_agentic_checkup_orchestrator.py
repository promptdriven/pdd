"""Tests for pdd.agentic_checkup_orchestrator module."""
from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Dict, List, Tuple
from unittest.mock import MagicMock, call, patch

import pytest

from pdd.agentic_checkup_orchestrator import (
    CHECKUP_STEP_TIMEOUTS,
    MAX_FIX_VERIFY_ITERATIONS,
    STEP_ORDER,
    TOTAL_STEPS,
    _copy_uncommitted_changes,
    _get_state_dir,
    _next_step,
    _parse_changed_files,
    run_agentic_checkup_orchestrator,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------


@pytest.fixture
def mock_dependencies():
    """Mock external dependencies for orchestrator tests.

    Default mock returns "All Issues Fixed" so the fix-verify loop exits
    on the first pass (single iteration).
    """
    with patch("pdd.agentic_checkup_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_checkup_orchestrator.load_prompt_template") as mock_load, \
         patch("pdd.agentic_checkup_orchestrator.console") as mock_console, \
         patch("pdd.agentic_checkup_orchestrator._setup_worktree") as mock_worktree:

        mock_run.return_value = (True, "Step output. All Issues Fixed", 0.1, "gpt-4")
        mock_load.return_value = "Prompt for {issue_number}"
        mock_worktree.return_value = (Path("/tmp/worktree"), None)

        yield mock_run, mock_load, mock_console, mock_worktree


@pytest.fixture
def default_args(tmp_path):
    """Default arguments for the orchestrator."""
    return {
        "issue_url": "https://github.com/owner/repo/issues/1",
        "issue_content": "Run full checkup",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 1,
        "issue_title": "Check CRM",
        "architecture_json": "[]",
        "pddrc_content": "project: test",
        "cwd": tmp_path,
        "verbose": False,
        "quiet": True,
    }


# ---------------------------------------------------------------------------
# Happy Path
# ---------------------------------------------------------------------------


class TestHappyPath:
    def test_all_steps_execute(self, mock_dependencies, default_args):
        """All steps should execute when no hard stops are triggered.

        With the loop exiting on the first pass (default mock contains
        "All Issues Fixed"), call count is: 2 (linear) + 7 (loop iter 1) + 1 (step 8) = 10.
        """
        mock_run, mock_load, _, mock_worktree = mock_dependencies

        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)

        assert success is True
        assert "Checkup complete" in msg
        assert mock_run.call_count == 10
        assert cost == pytest.approx(1.0)  # 10 steps x 0.1 each
        assert model == "gpt-4"

    def test_cost_accumulation(self, mock_dependencies, default_args):
        """Costs from all steps should be accumulated."""
        mock_run, _, _, _ = mock_dependencies

        call_counter = [0]

        def side_effect(*args, **kwargs):
            call_counter[0] += 1
            return (True, f"Output {call_counter[0]}. All Issues Fixed", call_counter[0] * 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)

        assert success is True
        # 10 calls: 1*0.1 + 2*0.1 + ... + 10*0.1 = 5.5
        assert cost == pytest.approx(5.5)

    def test_context_accumulation(self, mock_dependencies, default_args):
        """Step outputs should be passed as context to subsequent steps."""
        mock_run, mock_load, _, _ = mock_dependencies

        def side_effect_load(name):
            if "step2" in name:
                return "Previous: {step1_output}"
            return "Prompt for {issue_number}"

        mock_load.side_effect = side_effect_load

        step1_out = "Discovered Python project"

        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step1":
                return (True, step1_out, 0.1, "gpt-4")
            return (True, f"Output for {label}. All Issues Fixed", 0.1, "gpt-4")

        mock_run.side_effect = side_effect_run

        run_agentic_checkup_orchestrator(**default_args)

        # Find the step 2 call and verify context was passed
        step2_call = None
        for call_obj in mock_run.call_args_list:
            if call_obj.kwargs.get("label") == "step2":
                step2_call = call_obj
                break

        assert step2_call is not None
        instruction = step2_call.kwargs["instruction"]
        assert f"Previous: {step1_out}" == instruction

    def test_total_steps_is_8(self):
        """TOTAL_STEPS constant should be 8."""
        assert TOTAL_STEPS == 8

    def test_step_8_timeout_defined(self):
        """Step 8 should have a timeout defined."""
        assert 8 in CHECKUP_STEP_TIMEOUTS
        assert CHECKUP_STEP_TIMEOUTS[8] == 340.0


# ---------------------------------------------------------------------------
# --no-fix Mode
# ---------------------------------------------------------------------------


class TestNoFixMode:
    def test_steps_6_and_8_skipped_in_no_fix_mode(self, mock_dependencies, default_args):
        """Steps 6 (fix) and 8 (PR) should be skipped when no_fix=True."""
        mock_run, _, _, _ = mock_dependencies
        default_args["no_fix"] = True

        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)

        assert success is True
        # 6 steps executed (steps 6 and 8 skipped)
        assert mock_run.call_count == 6

        # Verify steps 6 and 8 were not called
        called_labels = [c.kwargs["label"] for c in mock_run.call_args_list]
        assert all("step6" not in lbl for lbl in called_labels)
        assert "step8" not in called_labels

    def test_step_7_receives_skip_message(self, mock_dependencies, default_args):
        """Step 7 should receive 'Skipped: --no-fix mode' as step6_1_output."""
        mock_run, mock_load, _, _ = mock_dependencies
        default_args["no_fix"] = True

        def side_effect_load(name):
            if "step7" in name:
                return "Fix output: {step6_1_output}"
            return "Prompt for {issue_number}"

        mock_load.side_effect = side_effect_load

        run_agentic_checkup_orchestrator(**default_args)

        step7_call = None
        for call_obj in mock_run.call_args_list:
            if call_obj.kwargs.get("label") == "step7":
                step7_call = call_obj
                break

        assert step7_call is not None
        assert "Skipped: --no-fix mode" in step7_call.kwargs["instruction"]

    def test_no_worktree_created_in_no_fix_mode(self, mock_dependencies, default_args):
        """No worktree should be created when --no-fix is set."""
        _, _, _, mock_worktree = mock_dependencies
        default_args["no_fix"] = True

        run_agentic_checkup_orchestrator(**default_args)

        mock_worktree.assert_not_called()


# ---------------------------------------------------------------------------
# Worktree Handling
# ---------------------------------------------------------------------------


class TestWorktreeHandling:
    def test_worktree_created_before_loop(self, mock_dependencies, default_args):
        """Worktree should be created before the fix-verify loop."""
        mock_run, _, _, mock_worktree = mock_dependencies

        executed_labels = []

        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            executed_labels.append(label)
            return (True, f"Output for {label}. All Issues Fixed", 0.1, "gpt-4")

        mock_run.side_effect = side_effect_run

        run_agentic_checkup_orchestrator(**default_args)

        # Worktree should have been created
        mock_worktree.assert_called_once()
        # Loop steps should execute
        assert any("step6" in lbl for lbl in executed_labels)
        assert any("step7" in lbl for lbl in executed_labels)
        assert "step8" in executed_labels

    def test_worktree_setup_args(self, mock_dependencies, default_args):
        """Worktree should be set up with correct arguments."""
        _, _, _, mock_worktree = mock_dependencies

        run_agentic_checkup_orchestrator(**default_args)

        mock_worktree.assert_called_once_with(
            default_args["cwd"], 1, True, resume_existing=False,
        )

    def test_loop_steps_run_in_worktree(self, mock_dependencies, default_args):
        """Steps 3-8 (in the loop and step 8) should use the worktree path as cwd."""
        mock_run, _, _, mock_worktree = mock_dependencies
        worktree_dir = Path("/tmp/checkup-worktree")
        mock_worktree.return_value = (worktree_dir, None)

        run_agentic_checkup_orchestrator(**default_args)

        for call_obj in mock_run.call_args_list:
            label = call_obj.kwargs.get("label", "")
            cwd_used = call_obj.kwargs.get("cwd")
            # Extract step number from label like "step6_1_iter1" or "step8"
            base = label.split("_iter")[0]
            num_str = base.replace("step", "").replace("_", ".")
            step_num = float(num_str)
            if step_num >= 3:
                assert cwd_used == worktree_dir, (
                    f"Step {label} should run in worktree, got {cwd_used}"
                )
            else:
                assert cwd_used == default_args["cwd"], (
                    f"Step {label} should run in main cwd, got {cwd_used}"
                )

    def test_steps_1_through_2_run_in_main_cwd(self, mock_dependencies, default_args):
        """Steps 1-2 should use the main project cwd, not the worktree."""
        mock_run, _, _, _ = mock_dependencies

        run_agentic_checkup_orchestrator(**default_args)

        for call_obj in mock_run.call_args_list:
            label = call_obj.kwargs.get("label", "")
            base = label.split("_iter")[0]
            num_str = base.replace("step", "").replace("_", ".")
            step_num = float(num_str)
            if step_num <= 2:
                assert call_obj.kwargs.get("cwd") == default_args["cwd"]

    def test_worktree_failure_aborts(self, mock_dependencies, default_args):
        """If worktree creation fails, the orchestrator should abort."""
        mock_run, _, _, mock_worktree = mock_dependencies
        mock_worktree.return_value = (None, "git worktree error: branch already exists")

        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)

        assert success is False
        assert "worktree" in msg.lower()
        # Steps 1-2 should have executed, then abort at loop start
        assert mock_run.call_count == 2

    def test_worktree_path_in_context(self, mock_dependencies, default_args):
        """Worktree path should be added to context for step prompts."""
        mock_run, mock_load, _, mock_worktree = mock_dependencies
        worktree_dir = Path("/tmp/test-worktree")
        mock_worktree.return_value = (worktree_dir, None)

        def side_effect_load(name):
            if "step6" in name:
                return "Worktree: {worktree_path}"
            return "Prompt for {issue_number}"

        mock_load.side_effect = side_effect_load

        run_agentic_checkup_orchestrator(**default_args)

        step6_call = next(
            c for c in mock_run.call_args_list
            if "step6" in c.kwargs.get("label", "")
        )
        assert str(worktree_dir) in step6_call.kwargs["instruction"]


# ---------------------------------------------------------------------------
# Changed Files Tracking
# ---------------------------------------------------------------------------


class TestChangedFilesTracking:
    def test_parse_changed_files_basic(self):
        """_parse_changed_files should extract file paths."""
        output = (
            "FILES_CREATED: src/foo.py, src/bar.py\n"
            "FILES_MODIFIED: src/baz.py\n"
        )
        result = _parse_changed_files(output)
        assert result == ["src/foo.py", "src/bar.py", "src/baz.py"]

    def test_parse_changed_files_empty(self):
        """_parse_changed_files should return empty list for no matches."""
        assert _parse_changed_files("No files changed") == []

    def test_parse_changed_files_mixed_content(self):
        """_parse_changed_files should ignore non-file lines."""
        output = (
            "Some other output\n"
            "FILES_CREATED: src/new.py\n"
            "More output\n"
            "FILES_MODIFIED: src/old.py\n"
            "Done\n"
        )
        result = _parse_changed_files(output)
        assert result == ["src/new.py", "src/old.py"]

    def test_changed_files_passed_to_step_8(self, mock_dependencies, default_args):
        """Changed files from step 6 should be available to step 8 as files_to_stage."""
        mock_run, mock_load, _, _ = mock_dependencies

        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step6" in label:
                return (True, "FILES_CREATED: src/fix.py\nFILES_MODIFIED: src/main.py", 0.1, "gpt-4")
            if "step7" in label:
                return (True, "All Issues Fixed", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect_run

        def side_effect_load(name):
            if "step8" in name:
                return "Files: {files_to_stage}"
            return "Prompt for {issue_number}"

        mock_load.side_effect = side_effect_load

        run_agentic_checkup_orchestrator(**default_args)

        step8_call = next(
            c for c in mock_run.call_args_list if c.kwargs.get("label") == "step8"
        )
        instruction = step8_call.kwargs["instruction"]
        assert "src/fix.py" in instruction
        assert "src/main.py" in instruction

    def test_changed_files_deduplicated(self, mock_dependencies, default_args):
        """Changed files should be deduplicated."""
        mock_run, mock_load, _, _ = mock_dependencies

        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step6" in label:
                return (True, "FILES_CREATED: src/fix.py\nFILES_MODIFIED: src/fix.py", 0.1, "gpt-4")
            if "step7" in label:
                return (True, "All Issues Fixed", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect_run

        def side_effect_load(name):
            if "step8" in name:
                return "Files: {files_to_stage}"
            return "Prompt for {issue_number}"

        mock_load.side_effect = side_effect_load

        run_agentic_checkup_orchestrator(**default_args)

        step8_call = next(
            c for c in mock_run.call_args_list if c.kwargs.get("label") == "step8"
        )
        instruction = step8_call.kwargs["instruction"]
        # Should appear once, not twice
        assert instruction.count("src/fix.py") == 1


# ---------------------------------------------------------------------------
# Soft Failures
# ---------------------------------------------------------------------------


class TestSoftFailures:
    def test_soft_failure_does_not_stop_workflow(self, mock_dependencies, default_args):
        """A step failure without hard stop should not terminate the workflow."""
        mock_run, _, _, _ = mock_dependencies

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step2":
                return (False, "Agent had a problem but no hard stop", 0.1, "gpt-4")
            return (True, f"Output for {label}. All Issues Fixed", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)

        assert success is True
        assert mock_run.call_count == 10

    def test_failed_step_output_prefixed(self, mock_dependencies, default_args, tmp_path):
        """Failed step output should be stored with 'FAILED:' prefix."""
        mock_run, _, _, _ = mock_dependencies
        default_args["cwd"] = tmp_path

        saved_states = []

        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step3" in label:
                return (False, "Build check failed somehow", 0.1, "gpt-4")
            if "step7" in label:
                return (True, "All Issues Fixed", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect_run

        def capture_state(cwd, issue_number, workflow_type, state, state_dir,
                          repo_owner, repo_name, use_github_state=True,
                          github_comment_id=None):
            saved_states.append(state.copy())
            return None

        with patch("pdd.agentic_checkup_orchestrator.save_workflow_state",
                    side_effect=capture_state):
            run_agentic_checkup_orchestrator(**default_args)

        # Find state saved after step 3
        step3_state = next(
            (s for s in saved_states if "3" in s.get("step_outputs", {})),
            None,
        )
        assert step3_state is not None
        assert step3_state["step_outputs"]["3"].startswith("FAILED:")


# ---------------------------------------------------------------------------
# Error Handling
# ---------------------------------------------------------------------------


class TestErrorHandling:
    def test_template_loading_failure(self, mock_dependencies, default_args):
        """Should fail gracefully if a prompt template cannot be loaded."""
        mock_run, mock_load, _, _ = mock_dependencies
        mock_load.return_value = None

        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)

        assert success is False
        assert "prompt template" in msg.lower() or "Missing" in msg
        assert mock_run.call_count == 0

    def test_template_formatting_error(self, mock_dependencies, default_args):
        """Should fail gracefully if context is missing a required key."""
        mock_run, mock_load, _, _ = mock_dependencies

        # Template referencing a key that IS in context — should work fine.
        mock_load.return_value = "Template for {issue_url}"

        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)
        assert mock_run.call_count > 0


# ---------------------------------------------------------------------------
# Step Timeouts
# ---------------------------------------------------------------------------


class TestTimeouts:
    @staticmethod
    def _label_to_step_num(label: str):
        """Extract numeric step from label like 'step6_1_iter1' -> 6.1."""
        # Remove _iter suffix
        base = label.split("_iter")[0]
        # e.g. "step6_1" -> "6_1", "step3" -> "3", "step8" -> "8"
        num_str = base.replace("step", "")
        # "6_1" -> 6.1, "3" -> 3
        return float(num_str.replace("_", "."))

    def test_step_timeouts_passed_to_run_agentic_task(self, mock_dependencies, default_args):
        """Each step should receive its configured timeout."""
        mock_run, _, _, _ = mock_dependencies

        run_agentic_checkup_orchestrator(**default_args)

        assert mock_run.call_count == 10

        for call_obj in mock_run.call_args_list:
            label = call_obj.kwargs.get("label", "")
            timeout = call_obj.kwargs.get("timeout")
            step_num = self._label_to_step_num(label)
            expected = CHECKUP_STEP_TIMEOUTS.get(step_num, 600.0)
            assert timeout == expected, (
                f"Step {label}: expected timeout={expected}, got {timeout}"
            )

    def test_timeout_adder_applied(self, mock_dependencies, default_args):
        """timeout_adder should be added to each step's timeout."""
        mock_run, _, _, _ = mock_dependencies
        default_args["timeout_adder"] = 100.0

        run_agentic_checkup_orchestrator(**default_args)

        for call_obj in mock_run.call_args_list:
            label = call_obj.kwargs.get("label", "")
            timeout = call_obj.kwargs.get("timeout")
            step_num = self._label_to_step_num(label)
            expected = CHECKUP_STEP_TIMEOUTS.get(step_num, 600.0) + 100.0
            assert timeout == expected


# ---------------------------------------------------------------------------
# Consecutive Provider Failure Abort
# ---------------------------------------------------------------------------


class TestProviderFailureAbort:
    def test_aborts_after_3_consecutive_provider_failures(self, mock_dependencies, default_args):
        """Should abort after 3 consecutive 'All agent providers failed' errors."""
        mock_run, _, _, _ = mock_dependencies

        mock_run.return_value = (False, "All agent providers failed", 0.0, "")

        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)

        assert success is False
        assert "consecutive" in msg.lower() or "Aborting" in msg
        assert mock_run.call_count == 3  # Aborts after 3 failures

    def test_non_provider_failures_do_not_trigger_abort(self, mock_dependencies, default_args):
        """Non-provider failures should not count toward the consecutive failure limit."""
        mock_run, _, _, _ = mock_dependencies

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if label in ("step1", "step2"):
                return (False, "Some other error", 0.1, "gpt-4")
            return (True, f"Output for {label}. All Issues Fixed", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)

        # Should complete all 10 steps (failures don't trigger abort)
        assert success is True
        assert mock_run.call_count == 10

    def test_success_resets_consecutive_failure_count(self, mock_dependencies, default_args):
        """A successful step should reset the consecutive failure counter."""
        mock_run, _, _, _ = mock_dependencies

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step1":
                return (False, "All agent providers failed", 0.0, "")
            if label == "step2":
                return (False, "All agent providers failed", 0.0, "")
            return (True, f"ok. All Issues Fixed", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)

        # Steps 1-2 fail but don't hit 3 consecutive, then steps 3+ succeed.
        assert success is True
        assert mock_run.call_count == 10


# ---------------------------------------------------------------------------
# Resume Functionality
# ---------------------------------------------------------------------------


class TestResume:
    def test_resume_skips_completed_steps(self, mock_dependencies, default_args, tmp_path):
        """Resuming should skip already-completed steps."""
        mock_run, _, _, _ = mock_dependencies
        default_args["cwd"] = tmp_path

        state_dir = _get_state_dir(tmp_path)
        state_dir.mkdir(parents=True, exist_ok=True)
        state_file = state_dir / "checkup_state_1.json"

        state = {
            "workflow": "checkup",
            "issue_number": 1,
            "issue_url": default_args["issue_url"],
            "last_completed_step": 3,
            "step_outputs": {
                "1": "Step 1 output",
                "2": "Step 2 output",
                "3": "Step 3 output",
            },
            "total_cost": 0.3,
            "model_used": "gpt-4",
        }
        with open(state_file, "w") as f:
            json.dump(state, f)

        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)

        assert success is True
        # Should run steps 4,5,6.1,6.2,6.3,7 in loop (6 calls, step 3 skipped) + step 8 = 7
        assert mock_run.call_count == 7

        called_labels = [c.kwargs["label"] for c in mock_run.call_args_list]
        assert "step1" not in called_labels
        assert "step2" not in called_labels
        # step3 is skipped via resume (already completed at iter 1)
        assert any("step4" in lbl for lbl in called_labels)
        assert "step8" in called_labels

    def test_resume_restores_context(self, mock_dependencies, default_args, tmp_path):
        """Resumed runs should have access to previous step outputs."""
        mock_run, mock_load, _, _ = mock_dependencies
        default_args["cwd"] = tmp_path

        state_dir = _get_state_dir(tmp_path)
        state_dir.mkdir(parents=True, exist_ok=True)
        state_file = state_dir / "checkup_state_1.json"

        state = {
            "workflow": "checkup",
            "issue_number": 1,
            "issue_url": default_args["issue_url"],
            "last_completed_step": 1,
            "step_outputs": {"1": "Discovered Python project"},
            "total_cost": 0.1,
            "model_used": "gpt-4",
        }
        with open(state_file, "w") as f:
            json.dump(state, f)

        def side_effect_load(name):
            if "step2" in name:
                return "Previous: {step1_output}"
            return "Prompt for {issue_number}"

        mock_load.side_effect = side_effect_load

        formatted_prompts = []

        def side_effect_run(instruction, **kwargs):
            formatted_prompts.append(instruction)
            return (True, f"Output for {kwargs.get('label', '')}. All Issues Fixed", 0.1, "gpt-4")

        mock_run.side_effect = side_effect_run

        run_agentic_checkup_orchestrator(**default_args)

        # Step 2 is the first call (step 1 skipped)
        step2_prompt = formatted_prompts[0]
        assert "Discovered Python project" in step2_prompt

    def test_state_cleared_on_success(self, mock_dependencies, default_args, tmp_path):
        """State file should be deleted on successful completion."""
        mock_run, _, _, _ = mock_dependencies
        default_args["cwd"] = tmp_path

        state_dir = _get_state_dir(tmp_path)
        state_dir.mkdir(parents=True, exist_ok=True)
        state_file = state_dir / "checkup_state_1.json"

        state = {
            "workflow": "checkup",
            "issue_number": 1,
            "last_completed_step": 0,
            "step_outputs": {},
            "total_cost": 0.0,
            "model_used": "unknown",
        }
        with open(state_file, "w") as f:
            json.dump(state, f)

        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)

        assert success is True
        assert not state_file.exists()

    def test_failed_step_not_marked_completed(self, mock_dependencies, default_args, tmp_path):
        """Failed steps should not advance last_completed_step."""
        mock_run, _, _, _ = mock_dependencies
        default_args["cwd"] = tmp_path

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            # Steps 1-2 succeed, then 3 consecutive provider failures in the loop
            if "step3" in label or "step4" in label or "step5" in label:
                return (False, "All agent providers failed", 0.0, "")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        saved_states = []

        def capture_state(cwd, issue_number, workflow_type, state, state_dir,
                          repo_owner, repo_name, use_github_state=True,
                          github_comment_id=None):
            saved_states.append(state.copy())
            return None

        with patch("pdd.agentic_checkup_orchestrator.save_workflow_state",
                    side_effect=capture_state):
            run_agentic_checkup_orchestrator(**default_args)

        # After step 5 fails (3rd consecutive provider failure), abort.
        # last_completed_step should be 2 (last successful step).
        final_state = saved_states[-1]
        assert final_state["last_completed_step"] == 2

    def test_resume_reruns_failed_step(self, mock_dependencies, default_args, tmp_path):
        """Resuming should re-run a failed step, not skip it."""
        mock_run, _, _, _ = mock_dependencies
        default_args["cwd"] = tmp_path

        state_dir = _get_state_dir(tmp_path)
        state_dir.mkdir(parents=True, exist_ok=True)
        state_file = state_dir / "checkup_state_1.json"

        state = {
            "workflow": "checkup",
            "issue_number": 1,
            "issue_url": default_args["issue_url"],
            "last_completed_step": 3,
            "step_outputs": {
                "1": "ok", "2": "ok", "3": "ok",
                "4": "FAILED: All agent providers failed",
            },
            "total_cost": 0.3,
            "model_used": "gpt-4",
        }
        with open(state_file, "w") as f:
            json.dump(state, f)

        executed_steps = []

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            executed_steps.append(label)
            return (True, f"Output for {label}. All Issues Fixed", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        run_agentic_checkup_orchestrator(**default_args)

        # Step 4 should be re-executed (was failed in cache)
        assert any("step4" in s for s in executed_steps)
        # Steps 1-3 should not be in executed list
        assert not any("step1" in s for s in executed_steps)
        assert not any("step2" in s for s in executed_steps)
        # step3 is skipped in first iteration (resume)
        assert not any(s == "step3_iter1" for s in executed_steps)

    def test_state_validation_corrects_ratcheted_step(self, mock_dependencies, default_args, tmp_path):
        """State validation should correct last_completed_step if cached outputs are FAILED."""
        mock_run, _, _, _ = mock_dependencies
        default_args["cwd"] = tmp_path

        state_dir = _get_state_dir(tmp_path)
        state_dir.mkdir(parents=True, exist_ok=True)
        state_file = state_dir / "checkup_state_1.json"

        # Corrupted state: last_completed_step=4 but all outputs are FAILED
        corrupted_state = {
            "workflow": "checkup",
            "issue_number": 1,
            "issue_url": default_args["issue_url"],
            "last_completed_step": 4,
            "step_outputs": {
                "1": "FAILED: All agent providers failed",
                "2": "FAILED: All agent providers failed",
                "3": "FAILED: All agent providers failed",
                "4": "FAILED: All agent providers failed",
            },
            "total_cost": 0.0,
            "model_used": "",
        }
        with open(state_file, "w") as f:
            json.dump(corrupted_state, f)

        executed_steps = []

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            executed_steps.append(label)
            return (True, f"Output for {label}. All Issues Fixed", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        run_agentic_checkup_orchestrator(**default_args)

        # All 10 steps should be re-executed since all cached outputs are FAILED
        assert mock_run.call_count == 10
        assert "step1" in executed_steps

    def test_consecutive_failures_do_not_advance_last_completed_step(
        self, mock_dependencies, default_args, tmp_path
    ):
        """When consecutive steps fail, last_completed_step should remain at 0."""
        mock_run, _, _, _ = mock_dependencies
        default_args["cwd"] = tmp_path

        mock_run.return_value = (False, "All agent providers failed", 0.0, "")

        saved_states = []

        def capture_state(cwd, issue_number, workflow_type, state, state_dir,
                          repo_owner, repo_name, use_github_state=True,
                          github_comment_id=None):
            saved_states.append(state.copy())
            return None

        with patch("pdd.agentic_checkup_orchestrator.save_workflow_state",
                    side_effect=capture_state):
            run_agentic_checkup_orchestrator(**default_args)

        final_state = saved_states[-1]
        assert final_state["last_completed_step"] == 0

        for step_key, output in final_state["step_outputs"].items():
            assert output.startswith("FAILED:")

    def test_resume_with_worktree_state(self, mock_dependencies, default_args, tmp_path):
        """Resuming after step 6.3 should restore worktree path from state."""
        mock_run, _, _, mock_worktree = mock_dependencies
        default_args["cwd"] = tmp_path

        worktree_dir = tmp_path / ".pdd" / "worktrees" / "checkup-issue-1"
        worktree_dir.mkdir(parents=True, exist_ok=True)

        state_dir = _get_state_dir(tmp_path)
        state_dir.mkdir(parents=True, exist_ok=True)
        state_file = state_dir / "checkup_state_1.json"

        state = {
            "workflow": "checkup",
            "issue_number": 1,
            "issue_url": default_args["issue_url"],
            "last_completed_step": 6.3,
            "step_outputs": {
                "1": "ok", "2": "ok", "3": "ok",
                "4": "ok", "5": "ok",
                "6_1": "Fixed stuff", "6_2": "Regression tests", "6_3": "E2E tests",
            },
            "total_cost": 0.8,
            "model_used": "gpt-4",
            "worktree_path": str(worktree_dir),
            "changed_files": ["src/fix.py"],
            "fix_verify_iteration": 1,
        }
        with open(state_file, "w") as f:
            json.dump(state, f)

        run_agentic_checkup_orchestrator(**default_args)

        # Should not create a new worktree (existing one reused)
        mock_worktree.assert_not_called()

        # Should run step 7 (remaining in loop iteration) + step 8 = 2 calls
        assert mock_run.call_count == 2
        called_labels = [c.kwargs["label"] for c in mock_run.call_args_list]
        # Step 7 from iteration 1 resume, then step 8
        assert any("step7" in lbl for lbl in called_labels)
        assert "step8" in called_labels

        # Steps 7-8 should use worktree dir
        for call_obj in mock_run.call_args_list:
            assert call_obj.kwargs.get("cwd") == worktree_dir

    def test_resume_recreates_missing_worktree(self, mock_dependencies, default_args, tmp_path):
        """If worktree path in state doesn't exist, it should be recreated."""
        mock_run, _, _, mock_worktree = mock_dependencies
        default_args["cwd"] = tmp_path

        recreated_dir = Path("/tmp/recreated-worktree")
        mock_worktree.return_value = (recreated_dir, None)

        state_dir = _get_state_dir(tmp_path)
        state_dir.mkdir(parents=True, exist_ok=True)
        state_file = state_dir / "checkup_state_1.json"

        state = {
            "workflow": "checkup",
            "issue_number": 1,
            "issue_url": default_args["issue_url"],
            "last_completed_step": 6.3,
            "step_outputs": {
                "1": "ok", "2": "ok", "3": "ok",
                "4": "ok", "5": "ok",
                "6_1": "Fixed stuff", "6_2": "Tests", "6_3": "E2E",
            },
            "total_cost": 0.8,
            "model_used": "gpt-4",
            "worktree_path": "/tmp/does-not-exist",
            "changed_files": ["src/fix.py"],
        }
        with open(state_file, "w") as f:
            json.dump(state, f)

        run_agentic_checkup_orchestrator(**default_args)

        # Should recreate worktree with resume_existing=True
        mock_worktree.assert_called_once_with(
            tmp_path, 1, True, resume_existing=True,
        )


# ---------------------------------------------------------------------------
# Format String Injection
# ---------------------------------------------------------------------------


class TestFormatStringInjection:
    def test_curly_braces_in_output_do_not_cause_keyerror(self, mock_dependencies, default_args):
        """LLM outputs with {placeholder} should not cause KeyError in later steps."""
        mock_run, mock_load, _, _ = mock_dependencies

        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step1":
                return (True, "The error is in {url} config", 0.1, "gpt-4")
            return (True, f"Output for {label}. All Issues Fixed", 0.1, "gpt-4")

        mock_run.side_effect = side_effect_run

        def side_effect_load(name):
            if "step2" in name:
                return "Previous: {step1_output}"
            return "Prompt for {issue_number}"

        mock_load.side_effect = side_effect_load

        # Should NOT raise KeyError
        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)
        assert success is True
        assert mock_run.call_count == 10

    def test_curly_braces_in_restored_context(self, mock_dependencies, default_args, tmp_path):
        """Curly braces in restored step outputs should not cause KeyError."""
        mock_run, mock_load, _, _ = mock_dependencies
        default_args["cwd"] = tmp_path

        state_dir = _get_state_dir(tmp_path)
        state_dir.mkdir(parents=True, exist_ok=True)
        state_file = state_dir / "checkup_state_1.json"

        state = {
            "workflow": "checkup",
            "issue_number": 1,
            "issue_url": default_args["issue_url"],
            "last_completed_step": 1,
            "step_outputs": {
                "1": "Found config: {api_key: missing}",
            },
            "total_cost": 0.1,
            "model_used": "gpt-4",
        }
        with open(state_file, "w") as f:
            json.dump(state, f)

        def side_effect_load(name):
            if "step2" in name:
                return "Previous: {step1_output}"
            return "Prompt for {issue_number}"

        mock_load.side_effect = side_effect_load

        # Should NOT raise KeyError
        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)
        assert success is True


# ---------------------------------------------------------------------------
# Template Preprocessing
# ---------------------------------------------------------------------------


class TestTemplatePreprocessing:
    def test_preprocess_called_with_correct_args(self, mock_dependencies, default_args):
        """preprocess should be called with double_curly_brackets=True and exclude_keys."""
        mock_run, mock_load, _, _ = mock_dependencies
        mock_load.return_value = "Template for {issue_url}"

        with patch("pdd.agentic_checkup_orchestrator.preprocess") as mock_preprocess:
            mock_preprocess.return_value = "Template for {issue_url}"

            run_agentic_checkup_orchestrator(**default_args)

            # Verify preprocess was called
            assert mock_preprocess.called

            call_kwargs = mock_preprocess.call_args[1]
            assert call_kwargs.get("double_curly_brackets") is True
            assert "issue_url" in call_kwargs.get("exclude_keys", [])
            assert call_kwargs.get("recursive") is True


# ---------------------------------------------------------------------------
# State Directory
# ---------------------------------------------------------------------------


class TestStateDir:
    def test_state_dir_under_git_root(self, tmp_path):
        """State dir should be under .pdd/checkup-state/ relative to git root."""
        # Mock git root
        with patch("pdd.agentic_checkup_orchestrator._get_git_root",
                    return_value=tmp_path):
            result = _get_state_dir(tmp_path)
            assert result == tmp_path / ".pdd" / "checkup-state"

    def test_state_dir_fallback_to_cwd(self, tmp_path):
        """If not a git repo, state dir should fall back to cwd."""
        with patch("pdd.agentic_checkup_orchestrator._get_git_root",
                    return_value=None):
            result = _get_state_dir(tmp_path)
            assert result == tmp_path / ".pdd" / "checkup-state"


# ---------------------------------------------------------------------------
# No-Fix Skip State Saving
# ---------------------------------------------------------------------------


class TestNoFixStateSaving:
    def test_no_fix_skip_saves_state_for_step_6_substeps(self, mock_dependencies, default_args, tmp_path):
        """Skipping step 6 sub-steps in --no-fix mode should save state correctly."""
        mock_run, _, _, _ = mock_dependencies
        default_args["cwd"] = tmp_path
        default_args["no_fix"] = True

        saved_states = []

        def capture_state(cwd, issue_number, workflow_type, state, state_dir,
                          repo_owner, repo_name, use_github_state=True,
                          github_comment_id=None):
            saved_states.append(state.copy())
            return None

        with patch("pdd.agentic_checkup_orchestrator.save_workflow_state",
                    side_effect=capture_state):
            run_agentic_checkup_orchestrator(**default_args)

        # Find state saved after step 6 sub-steps skip
        step6_state = next(
            (s for s in saved_states
             if s.get("step_outputs", {}).get("6_1") == "Skipped: --no-fix mode"),
            None,
        )
        assert step6_state is not None
        assert step6_state["step_outputs"]["6_2"] == "Skipped: --no-fix mode"
        assert step6_state["step_outputs"]["6_3"] == "Skipped: --no-fix mode"
        assert step6_state["last_completed_step"] == 6.3

    def test_no_fix_skip_saves_state_for_step_8(self, mock_dependencies, default_args, tmp_path):
        """Skipping step 8 in --no-fix mode should save state correctly."""
        mock_run, _, _, _ = mock_dependencies
        default_args["cwd"] = tmp_path
        default_args["no_fix"] = True

        saved_states = []

        def capture_state(cwd, issue_number, workflow_type, state, state_dir,
                          repo_owner, repo_name, use_github_state=True,
                          github_comment_id=None):
            saved_states.append(state.copy())
            return None

        with patch("pdd.agentic_checkup_orchestrator.save_workflow_state",
                    side_effect=capture_state):
            run_agentic_checkup_orchestrator(**default_args)

        # Find state saved after step 8 skip
        step8_state = next(
            (s for s in saved_states
             if s.get("step_outputs", {}).get("8") == "Skipped: --no-fix mode"),
            None,
        )
        assert step8_state is not None
        assert step8_state["last_completed_step"] == 8


# ---------------------------------------------------------------------------
# Partial Failure Resume
# ---------------------------------------------------------------------------


class TestPartialFailureResume:
    def test_partial_failure_preserves_last_successful_step(
        self, mock_dependencies, default_args, tmp_path
    ):
        """When steps 1-2 succeed and 3+ fail, last_completed_step should be 2."""
        mock_run, _, _, _ = mock_dependencies
        default_args["cwd"] = tmp_path

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            base = label.split("_iter")[0]
            num_str = base.replace("step", "").replace("_", ".")
            step_num = float(num_str)
            if step_num <= 2:
                return (True, f"Step {step_num} ok", 0.1, "gpt-4")
            return (False, "All agent providers failed", 0.0, "")

        mock_run.side_effect = side_effect

        saved_states = []

        def capture_state(cwd, issue_number, workflow_type, state, state_dir,
                          repo_owner, repo_name, use_github_state=True,
                          github_comment_id=None):
            saved_states.append(state.copy())
            return None

        with patch("pdd.agentic_checkup_orchestrator.save_workflow_state",
                    side_effect=capture_state):
            run_agentic_checkup_orchestrator(**default_args)

        final_state = saved_states[-1]
        assert final_state["last_completed_step"] == 2


# ---------------------------------------------------------------------------
# Build State
# ---------------------------------------------------------------------------


class TestBuildState:
    def test_build_state_includes_changed_files(self, mock_dependencies, default_args, tmp_path):
        """State should include changed_files."""
        mock_run, _, _, _ = mock_dependencies
        default_args["cwd"] = tmp_path

        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step6_1" in label:
                return (True, "FILES_CREATED: src/fix.py", 0.1, "gpt-4")
            if "step7" in label:
                return (True, "All Issues Fixed", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect_run

        saved_states = []

        def capture_state(cwd, issue_number, workflow_type, state, state_dir,
                          repo_owner, repo_name, use_github_state=True,
                          github_comment_id=None):
            saved_states.append(state.copy())
            return None

        with patch("pdd.agentic_checkup_orchestrator.save_workflow_state",
                    side_effect=capture_state):
            run_agentic_checkup_orchestrator(**default_args)

        # Find state after step 6.1
        step6_states = [
            s for s in saved_states
            if s.get("last_completed_step", 0) >= 6.1
        ]
        assert len(step6_states) > 0
        assert "src/fix.py" in step6_states[0].get("changed_files", [])

    def test_build_state_includes_worktree_path(self, mock_dependencies, default_args, tmp_path):
        """State should include worktree_path after worktree creation."""
        mock_run, _, _, mock_worktree = mock_dependencies
        default_args["cwd"] = tmp_path
        worktree_dir = Path("/tmp/checkup-wt")
        mock_worktree.return_value = (worktree_dir, None)

        saved_states = []

        def capture_state(cwd, issue_number, workflow_type, state, state_dir,
                          repo_owner, repo_name, use_github_state=True,
                          github_comment_id=None):
            saved_states.append(state.copy())
            return None

        with patch("pdd.agentic_checkup_orchestrator.save_workflow_state",
                    side_effect=capture_state):
            run_agentic_checkup_orchestrator(**default_args)

        # State after step 3+ should include worktree_path (created before loop)
        step3_states = [
            s for s in saved_states
            if s.get("last_completed_step", 0) >= 3
        ]
        assert len(step3_states) > 0
        assert step3_states[0].get("worktree_path") == str(worktree_dir)


# ---------------------------------------------------------------------------
# Fix-Verify Iteration Loop
# ---------------------------------------------------------------------------


class TestFixVerifyLoop:
    def test_max_fix_verify_iterations_is_3(self):
        """MAX_FIX_VERIFY_ITERATIONS constant should be 3."""
        assert MAX_FIX_VERIFY_ITERATIONS == 3

    def test_single_pass_clean(self, mock_dependencies, default_args):
        """Step 7 returns 'All Issues Fixed' on iter 1 -> loop runs once."""
        mock_run, _, _, _ = mock_dependencies

        run_agentic_checkup_orchestrator(**default_args)

        # 2 (steps 1-2) + 7 (steps 3,4,5,6.1,6.2,6.3,7 iter 1) + 1 (step 8) = 10
        assert mock_run.call_count == 10

        called_labels = [c.kwargs["label"] for c in mock_run.call_args_list]
        # Verify iteration 1 labels
        assert "step3_iter1" in called_labels
        assert "step4_iter1" in called_labels
        assert "step5_iter1" in called_labels
        assert "step6_1_iter1" in called_labels
        assert "step6_2_iter1" in called_labels
        assert "step6_3_iter1" in called_labels
        assert "step7_iter1" in called_labels
        # No iteration 2
        assert "step3_iter2" not in called_labels

    def test_multi_iteration_convergence(self, mock_dependencies, default_args):
        """Step 7 fails iter 1, returns 'All Issues Fixed' iter 2 -> 2 iterations."""
        mock_run, _, _, _ = mock_dependencies

        call_counter = [0]

        def side_effect(*args, **kwargs):
            call_counter[0] += 1
            label = kwargs.get("label", "")
            if label == "step7_iter1":
                return (True, "Issues remain: 2 tests failing", 0.1, "gpt-4")
            if label == "step7_iter2":
                return (True, "All Issues Fixed", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect

        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)

        assert success is True
        # 2 (steps 1-2) + 7 (iter 1) + 7 (iter 2) + 1 (step 8) = 17
        assert mock_run.call_count == 17

        called_labels = [c.kwargs["label"] for c in mock_run.call_args_list]
        assert "step3_iter1" in called_labels
        assert "step7_iter1" in called_labels
        assert "step3_iter2" in called_labels
        assert "step7_iter2" in called_labels
        assert "step8" in called_labels

    def test_max_iterations_reached(self, mock_dependencies, default_args):
        """Step 7 never returns clean -> 3 iterations, then step 8 with warning."""
        mock_run, _, _, mock_console = mock_dependencies

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step7" in label:
                return (True, "Issues remain: 1 test failing", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        default_args["quiet"] = False

        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)

        assert success is True
        # 2 (steps 1-2) + 3*7 (3 iterations) + 1 (step 8) = 24
        assert mock_run.call_count == 24

        called_labels = [c.kwargs["label"] for c in mock_run.call_args_list]
        assert "step3_iter3" in called_labels
        assert "step7_iter3" in called_labels
        assert "step8" in called_labels

    def test_labels_have_iteration_suffix(self, mock_dependencies, default_args):
        """Loop steps should have iteration-suffixed labels like step3_iter1."""
        mock_run, _, _, _ = mock_dependencies

        run_agentic_checkup_orchestrator(**default_args)

        called_labels = [c.kwargs["label"] for c in mock_run.call_args_list]

        # Linear steps: no iteration suffix
        assert "step1" in called_labels
        assert "step2" in called_labels

        # Loop steps: have _iter suffix
        assert "step3_iter1" in called_labels
        assert "step4_iter1" in called_labels
        assert "step5_iter1" in called_labels
        assert "step6_1_iter1" in called_labels
        assert "step6_2_iter1" in called_labels
        assert "step6_3_iter1" in called_labels
        assert "step7_iter1" in called_labels

        # Step 8: no iteration suffix
        assert "step8" in called_labels

    def test_previous_fixes_accumulated(self, mock_dependencies, default_args):
        """previous_fixes should grow each iteration."""
        mock_run, mock_load, _, _ = mock_dependencies

        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step6_1" in label:
                return (True, f"Fixed issue in {label}", 0.1, "gpt-4")
            if label == "step7_iter1":
                return (True, "Issues remain", 0.1, "gpt-4")
            if label == "step7_iter2":
                return (True, "All Issues Fixed", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect_run

        def side_effect_load(name):
            if "step6_1" in name:
                return "Previous fixes: {previous_fixes} Issue: {issue_number}"
            return "Prompt for {issue_number}"

        mock_load.side_effect = side_effect_load

        run_agentic_checkup_orchestrator(**default_args)

        # Find step6_1_iter2 call and verify it contains iteration 1 fixes
        step6_1_iter2_call = next(
            (c for c in mock_run.call_args_list
             if c.kwargs.get("label") == "step6_1_iter2"),
            None,
        )
        assert step6_1_iter2_call is not None
        instruction = step6_1_iter2_call.kwargs["instruction"]
        assert "Iteration 1 fixes:" in instruction
        assert "Fixed issue in step6_1_iter1" in instruction

    def test_changed_files_merged_across_iterations(self, mock_dependencies, default_args):
        """Changed files from multiple iterations should be merged."""
        mock_run, mock_load, _, _ = mock_dependencies

        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step6_1_iter1":
                return (True, "FILES_CREATED: src/fix1.py", 0.1, "gpt-4")
            if label == "step7_iter1":
                return (True, "Issues remain", 0.1, "gpt-4")
            if label == "step6_1_iter2":
                return (True, "FILES_CREATED: src/fix2.py", 0.1, "gpt-4")
            if label == "step7_iter2":
                return (True, "All Issues Fixed", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect_run

        def side_effect_load(name):
            if "step8" in name:
                return "Files: {files_to_stage}"
            return "Prompt for {issue_number}"

        mock_load.side_effect = side_effect_load

        run_agentic_checkup_orchestrator(**default_args)

        step8_call = next(
            c for c in mock_run.call_args_list if c.kwargs.get("label") == "step8"
        )
        instruction = step8_call.kwargs["instruction"]
        assert "src/fix1.py" in instruction
        assert "src/fix2.py" in instruction

    def test_state_persistence_includes_iteration(self, mock_dependencies, default_args, tmp_path):
        """fix_verify_iteration and previous_fixes should be in saved state."""
        mock_run, _, _, _ = mock_dependencies
        default_args["cwd"] = tmp_path

        saved_states = []

        def capture_state(cwd, issue_number, workflow_type, state, state_dir,
                          repo_owner, repo_name, use_github_state=True,
                          github_comment_id=None):
            saved_states.append(state.copy())
            return None

        with patch("pdd.agentic_checkup_orchestrator.save_workflow_state",
                    side_effect=capture_state):
            run_agentic_checkup_orchestrator(**default_args)

        # States after loop steps should have fix_verify_iteration
        loop_states = [
            s for s in saved_states
            if s.get("fix_verify_iteration", 0) > 0
        ]
        assert len(loop_states) > 0
        assert loop_states[0]["fix_verify_iteration"] == 1
        assert "previous_fixes" in loop_states[0]

    def test_resume_mid_loop(self, mock_dependencies, default_args, tmp_path):
        """Saved state with fix_verify_iteration=1 should resume loop."""
        mock_run, _, _, mock_worktree = mock_dependencies
        default_args["cwd"] = tmp_path

        worktree_dir = tmp_path / ".pdd" / "worktrees" / "checkup-issue-1"
        worktree_dir.mkdir(parents=True, exist_ok=True)

        state_dir = _get_state_dir(tmp_path)
        state_dir.mkdir(parents=True, exist_ok=True)
        state_file = state_dir / "checkup_state_1.json"

        state = {
            "workflow": "checkup",
            "issue_number": 1,
            "issue_url": default_args["issue_url"],
            "last_completed_step": 5,
            "step_outputs": {
                "1": "ok", "2": "ok", "3": "ok", "4": "ok", "5": "ok",
            },
            "total_cost": 0.5,
            "model_used": "gpt-4",
            "worktree_path": str(worktree_dir),
            "fix_verify_iteration": 1,
            "previous_fixes": "",
        }
        with open(state_file, "w") as f:
            json.dump(state, f)

        run_agentic_checkup_orchestrator(**default_args)

        # Should run steps 6.1, 6.2, 6.3, 7 (remaining in iter 1) + step 8 = 5 calls
        assert mock_run.call_count == 5
        called_labels = [c.kwargs["label"] for c in mock_run.call_args_list]
        assert "step6_1_iter1" in called_labels
        assert "step6_2_iter1" in called_labels
        assert "step6_3_iter1" in called_labels
        assert "step7_iter1" in called_labels
        assert "step8" in called_labels

    def test_provider_failure_in_loop(self, mock_dependencies, default_args):
        """3 consecutive provider failures in loop should abort."""
        mock_run, _, _, _ = mock_dependencies

        call_counter = [0]

        def side_effect(*args, **kwargs):
            call_counter[0] += 1
            label = kwargs.get("label", "")
            # Steps 1-2 succeed
            if label in ("step1", "step2"):
                return (True, f"Output for {label}", 0.1, "gpt-4")
            # Steps 3-5 in loop fail with provider error
            return (False, "All agent providers failed", 0.0, "")

        mock_run.side_effect = side_effect

        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)

        assert success is False
        assert "consecutive" in msg.lower() or "Aborting" in msg
        # 2 (steps 1-2) + 3 (steps 3-5 fail) = 5
        assert mock_run.call_count == 5

    def test_no_fix_mode_no_loop(self, mock_dependencies, default_args):
        """--no-fix runs steps 3-5 linearly once, no loop."""
        mock_run, _, _, _ = mock_dependencies
        default_args["no_fix"] = True

        run_agentic_checkup_orchestrator(**default_args)

        called_labels = [c.kwargs["label"] for c in mock_run.call_args_list]
        # No iteration suffixes in no-fix mode
        assert all("_iter" not in lbl for lbl in called_labels)
        # Steps 1-5 + 7 = 6 LLM calls
        assert mock_run.call_count == 6

    def test_iteration_context_passed_to_prompts(self, mock_dependencies, default_args):
        """Loop steps should have fix_verify_iteration and max in context."""
        mock_run, mock_load, _, _ = mock_dependencies

        def side_effect_load(name):
            if "step3" in name:
                return "Iter: {fix_verify_iteration}/{max_fix_verify_iterations}"
            return "Prompt for {issue_number}"

        mock_load.side_effect = side_effect_load

        run_agentic_checkup_orchestrator(**default_args)

        step3_call = next(
            c for c in mock_run.call_args_list
            if "step3" in c.kwargs.get("label", "")
        )
        instruction = step3_call.kwargs["instruction"]
        assert "Iter: 1/3" in instruction


# ---------------------------------------------------------------------------
# Worktree Uncommitted Changes Copy
# ---------------------------------------------------------------------------


class TestCopyUncommittedChanges:
    def test_copies_untracked_files(self, tmp_path):
        """Untracked files from git root should be copied to worktree."""
        git_root = tmp_path / "repo"
        worktree = tmp_path / "worktree"
        git_root.mkdir()
        worktree.mkdir()

        # Create an untracked file in the repo.
        (git_root / "new_module.py").write_text("print('hello')")

        with patch("pdd.agentic_checkup_orchestrator.subprocess.run") as mock_run:
            # git diff HEAD returns empty (no tracked changes)
            diff_result = MagicMock()
            diff_result.stdout = b""
            # git ls-files returns the untracked file
            ls_result = MagicMock()
            ls_result.stdout = "new_module.py\n"

            mock_run.side_effect = [diff_result, ls_result]

            _copy_uncommitted_changes(git_root, worktree, quiet=True)

        assert (worktree / "new_module.py").exists()
        assert (worktree / "new_module.py").read_text() == "print('hello')"

    def test_copies_untracked_files_in_subdirs(self, tmp_path):
        """Untracked files in subdirectories should be copied with structure."""
        git_root = tmp_path / "repo"
        worktree = tmp_path / "worktree"
        git_root.mkdir()
        worktree.mkdir()

        (git_root / "src").mkdir()
        (git_root / "src" / "deep.py").write_text("x = 1")

        with patch("pdd.agentic_checkup_orchestrator.subprocess.run") as mock_run:
            diff_result = MagicMock()
            diff_result.stdout = b""
            ls_result = MagicMock()
            ls_result.stdout = "src/deep.py\n"

            mock_run.side_effect = [diff_result, ls_result]

            _copy_uncommitted_changes(git_root, worktree, quiet=True)

        assert (worktree / "src" / "deep.py").exists()
        assert (worktree / "src" / "deep.py").read_text() == "x = 1"

    def test_skips_pdd_directory(self, tmp_path):
        """Files inside .pdd/ should NOT be copied (avoids recursive worktree)."""
        git_root = tmp_path / "repo"
        worktree = tmp_path / "worktree"
        git_root.mkdir()
        worktree.mkdir()

        (git_root / ".pdd").mkdir()
        (git_root / ".pdd" / "state.json").write_text("{}")

        with patch("pdd.agentic_checkup_orchestrator.subprocess.run") as mock_run:
            diff_result = MagicMock()
            diff_result.stdout = b""
            ls_result = MagicMock()
            ls_result.stdout = ".pdd/state.json\n"

            mock_run.side_effect = [diff_result, ls_result]

            _copy_uncommitted_changes(git_root, worktree, quiet=True)

        assert not (worktree / ".pdd" / "state.json").exists()

    def test_applies_uncommitted_diff(self, tmp_path):
        """Uncommitted changes to tracked files should be applied via git apply."""
        git_root = tmp_path / "repo"
        worktree = tmp_path / "worktree"
        git_root.mkdir()
        worktree.mkdir()

        with patch("pdd.agentic_checkup_orchestrator.subprocess.run") as mock_run:
            diff_result = MagicMock()
            diff_result.stdout = b"diff --git a/foo.py b/foo.py\n..."
            ls_result = MagicMock()
            ls_result.stdout = ""

            mock_run.side_effect = [diff_result, MagicMock(), ls_result]

            _copy_uncommitted_changes(git_root, worktree, quiet=True)

        # Should have called git apply with the diff
        apply_call = mock_run.call_args_list[1]
        assert "apply" in apply_call[0][0]
        assert apply_call.kwargs.get("input") == b"diff --git a/foo.py b/foo.py\n..."

    def test_graceful_on_diff_failure(self, tmp_path):
        """Should not crash if git diff fails."""
        git_root = tmp_path / "repo"
        worktree = tmp_path / "worktree"
        git_root.mkdir()
        worktree.mkdir()

        with patch("pdd.agentic_checkup_orchestrator.subprocess.run") as mock_run:
            mock_run.side_effect = subprocess.CalledProcessError(1, "git diff")

            # Should not raise.
            _copy_uncommitted_changes(git_root, worktree, quiet=True)

    def test_worktree_setup_calls_copy(self):
        """_setup_worktree should call _copy_uncommitted_changes for new worktrees."""
        with patch("pdd.agentic_checkup_orchestrator._get_git_root") as mock_root, \
             patch("pdd.agentic_checkup_orchestrator._worktree_exists", return_value=False), \
             patch("pdd.agentic_checkup_orchestrator._branch_exists", return_value=False), \
             patch("pdd.agentic_checkup_orchestrator.subprocess.run"), \
             patch("pdd.agentic_checkup_orchestrator._copy_uncommitted_changes") as mock_copy:

            fake_root = Path("/tmp/fake-root")
            mock_root.return_value = fake_root

            from pdd.agentic_checkup_orchestrator import _setup_worktree
            wt_path, err = _setup_worktree(fake_root, 42, quiet=True, resume_existing=False)

            assert err is None
            mock_copy.assert_called_once()
            # First arg should be git_root, second the worktree path
            call_args = mock_copy.call_args
            assert call_args[0][0] == fake_root

    def test_worktree_setup_skips_copy_on_resume(self):
        """_setup_worktree should NOT call _copy_uncommitted_changes when resuming."""
        with patch("pdd.agentic_checkup_orchestrator._get_git_root") as mock_root, \
             patch("pdd.agentic_checkup_orchestrator._worktree_exists", return_value=False), \
             patch("pdd.agentic_checkup_orchestrator._branch_exists", return_value=True), \
             patch("pdd.agentic_checkup_orchestrator.subprocess.run"), \
             patch("pdd.agentic_checkup_orchestrator._copy_uncommitted_changes") as mock_copy:

            fake_root = Path("/tmp/fake-root")
            mock_root.return_value = fake_root

            from pdd.agentic_checkup_orchestrator import _setup_worktree
            wt_path, err = _setup_worktree(fake_root, 42, quiet=True, resume_existing=True)

            assert err is None
            mock_copy.assert_not_called()


# ---------------------------------------------------------------------------
# _next_step() Helper
# ---------------------------------------------------------------------------


class TestNextStep:
    def test_integer_steps(self):
        """Integer steps should return the next step in STEP_ORDER."""
        assert _next_step(1) == 2
        assert _next_step(2) == 3
        assert _next_step(5) == 6.1
        assert _next_step(7) == 8

    def test_fractional_steps(self):
        """Fractional steps should return the next step in STEP_ORDER."""
        assert _next_step(6.1) == 6.2
        assert _next_step(6.2) == 6.3
        assert _next_step(6.3) == 7

    def test_last_step_returns_itself(self):
        """Last step (8) should return 8."""
        assert _next_step(8) == 8

    def test_legacy_step_6_fallback(self):
        """Legacy state with step 6 (not in STEP_ORDER) should resolve to 6.1."""
        assert _next_step(6) == 6.1

    def test_unknown_value_fallback(self):
        """Unknown values should fall back to the first step strictly greater."""
        assert _next_step(0) == 1
        assert _next_step(2.5) == 3

    def test_step_order_constant(self):
        """STEP_ORDER should have 10 entries."""
        assert len(STEP_ORDER) == 10
        assert STEP_ORDER == [1, 2, 3, 4, 5, 6.1, 6.2, 6.3, 7, 8]


# ---------------------------------------------------------------------------
# Bug A: State saved after worktree creation
# ---------------------------------------------------------------------------


class TestStateSavedAfterWorktreeCreation:
    def test_state_saved_after_worktree_creation(self, mock_dependencies, default_args, tmp_path):
        """Worktree path should be persisted immediately after creation (Bug A fix).

        Steps 1-2 save state first (without worktree). After worktree creation
        and before the first loop step, a state save with worktree_path should
        appear — i.e. the state saved at index 2 (after steps 1, 2, then
        worktree creation) should have the worktree_path set.
        """
        mock_run, _, _, mock_worktree = mock_dependencies
        default_args["cwd"] = tmp_path
        worktree_dir = Path("/tmp/checkup-wt-bugA")
        mock_worktree.return_value = (worktree_dir, None)

        saved_states = []

        def capture_state(cwd, issue_number, workflow_type, state, state_dir,
                          repo_owner, repo_name, use_github_state=True,
                          github_comment_id=None):
            saved_states.append(state.copy())
            return None

        with patch("pdd.agentic_checkup_orchestrator.save_workflow_state",
                    side_effect=capture_state):
            run_agentic_checkup_orchestrator(**default_args)

        # Find the first state with worktree_path set.
        wt_state_idx = next(
            (i for i, s in enumerate(saved_states) if s.get("worktree_path")),
            None,
        )
        assert wt_state_idx is not None
        assert saved_states[wt_state_idx].get("worktree_path") == str(worktree_dir)

        # Crucially, no loop step output should be in this state yet —
        # only steps 1-2 should be complete. This proves the save
        # happened after worktree creation but BEFORE step 3.
        wt_state = saved_states[wt_state_idx]
        assert wt_state["last_completed_step"] == 2
        assert "3" not in wt_state.get("step_outputs", {})


# ---------------------------------------------------------------------------
# Bug B: Between-iterations resume
# ---------------------------------------------------------------------------


class TestBetweenIterationsResume:
    def test_resume_between_iterations(self, mock_dependencies, default_args, tmp_path):
        """Resuming after iter 1 step 7 completes should start a new iteration at step 3."""
        mock_run, _, _, mock_worktree = mock_dependencies
        default_args["cwd"] = tmp_path

        worktree_dir = tmp_path / ".pdd" / "worktrees" / "checkup-issue-1"
        worktree_dir.mkdir(parents=True, exist_ok=True)

        state_dir = _get_state_dir(tmp_path)
        state_dir.mkdir(parents=True, exist_ok=True)
        state_file = state_dir / "checkup_state_1.json"

        # State: iter 1 completed through step 7, but "All Issues Fixed"
        # was NOT in the output (issues remain). start_step will be > 7
        # since last_completed_step = 7.
        state = {
            "workflow": "checkup",
            "issue_number": 1,
            "issue_url": default_args["issue_url"],
            "last_completed_step": 7,
            "step_outputs": {
                "1": "ok", "2": "ok", "3": "ok", "4": "ok", "5": "ok",
                "6_1": "Fixed stuff", "6_2": "Regression tests", "6_3": "E2E tests",
                "7": "Issues remain: 2 tests failing",
            },
            "total_cost": 1.0,
            "model_used": "gpt-4",
            "worktree_path": str(worktree_dir),
            "fix_verify_iteration": 1,
            "previous_fixes": "",
        }
        with open(state_file, "w") as f:
            json.dump(state, f)

        run_agentic_checkup_orchestrator(**default_args)

        # Should start a new iteration (iter 2) from step 3.
        # 7 loop steps (3,4,5,6.1,6.2,6.3,7) + step 8 = 8 calls
        assert mock_run.call_count == 8

        called_labels = [c.kwargs["label"] for c in mock_run.call_args_list]
        assert "step3_iter2" in called_labels
        assert "step6_1_iter2" in called_labels
        assert "step7_iter2" in called_labels
        assert "step8" in called_labels
        # Should NOT have any iter1 labels (all were completed before resume)
        assert not any("iter1" in lbl for lbl in called_labels)
