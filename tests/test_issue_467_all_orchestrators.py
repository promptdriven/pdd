"""
Tests for Issue #467: False Cached Steps fix across all orchestrators.

Validates that:
1. Consecutive failures don't advance last_completed_step (ratchet effect)
2. Resume from corrupted state re-runs failed steps (blind resume)
3. The common validate_cached_state helper works correctly
4. The architecture orchestrator ratchet fix is correct
"""

import json
import pytest
from pathlib import Path
from unittest.mock import MagicMock, patch, call
from typing import Union

from pdd.agentic_common import validate_cached_state


# ============================================================================
# Tests for validate_cached_state helper
# ============================================================================


class TestValidateCachedState:
    """Tests for the shared validate_cached_state helper in agentic_common."""

    def test_all_steps_successful_no_correction(self):
        """When all cached outputs are successful, no correction is needed."""
        step_outputs = {
            "1": "Step 1 output",
            "2": "Step 2 output",
            "3": "Step 3 output",
        }
        result = validate_cached_state(3, step_outputs, quiet=True)
        assert result == 3

    def test_all_steps_failed_corrects_to_zero(self):
        """When all cached outputs are FAILED, corrects to 0."""
        step_outputs = {
            "1": "FAILED: All agent providers failed",
            "2": "FAILED: All agent providers failed",
            "3": "FAILED: All agent providers failed",
        }
        result = validate_cached_state(3, step_outputs, quiet=True)
        assert result == 0

    def test_partial_failure_corrects_to_last_success(self):
        """When steps 1-2 succeed and 3+ fail, corrects to 2."""
        step_outputs = {
            "1": "Step 1 output",
            "2": "Step 2 output",
            "3": "FAILED: All agent providers failed",
            "4": "FAILED: All agent providers failed",
        }
        result = validate_cached_state(4, step_outputs, quiet=True)
        assert result == 2

    def test_no_correction_when_already_correct(self):
        """When last_completed_step matches actual last success, no correction."""
        step_outputs = {
            "1": "Step 1 output",
            "2": "Step 2 output",
            "3": "FAILED: error",
        }
        result = validate_cached_state(2, step_outputs, quiet=True)
        assert result == 2

    def test_empty_outputs_no_correction(self):
        """Empty step_outputs dict should not cause errors."""
        result = validate_cached_state(5, {}, quiet=True)
        assert result == 5

    def test_gap_in_outputs_stops_at_gap(self):
        """If step 2 is missing, stops at step 1."""
        step_outputs = {
            "1": "Step 1 output",
            "3": "Step 3 output",
        }
        result = validate_cached_state(3, step_outputs, quiet=True)
        # With derived order [1, 3], step 1 succeeds, step 3 succeeds
        # but with explicit order [1, 2, 3], step 2 is missing so stops at 1
        step_order = [1, 2, 3]
        result = validate_cached_state(3, step_outputs, step_order=step_order, quiet=True)
        assert result == 1

    def test_float_step_numbers(self):
        """Handles float step numbers like 5.5 (used by bug orchestrator)."""
        step_outputs = {
            "1": "output",
            "2": "output",
            "3": "output",
            "4": "FAILED: error",
            "5": "FAILED: error",
            "5.5": "FAILED: error",
        }
        step_order = [1, 2, 3, 4, 5, 5.5]
        result = validate_cached_state(5.5, step_outputs, step_order=step_order, quiet=True)
        assert result == 3

    def test_prints_warning_when_not_quiet(self):
        """When quiet=False, prints a warning about correction."""
        step_outputs = {
            "1": "FAILED: error",
        }
        with patch("pdd.agentic_common.console") as mock_console:
            result = validate_cached_state(1, step_outputs, quiet=False)
            assert result == 0
            mock_console.print.assert_called_once()
            call_args = mock_console.print.call_args[0][0]
            assert "correcting" in call_args.lower()


# ============================================================================
# Tests for agentic_architecture_orchestrator (ratchet + blind resume)
# ============================================================================


class TestArchitectureOrchestratorIssue467:
    """Tests for Issue #467 fixes in the architecture orchestrator."""

    @pytest.fixture
    def mock_deps(self, tmp_path):
        """Mock dependencies for architecture orchestrator."""
        with patch("pdd.agentic_architecture_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_architecture_orchestrator.load_workflow_state") as mock_load_state, \
             patch("pdd.agentic_architecture_orchestrator.save_workflow_state") as mock_save_state, \
             patch("pdd.agentic_architecture_orchestrator.clear_workflow_state") as mock_clear_state, \
             patch("pdd.agentic_architecture_orchestrator.load_prompt_template") as mock_load_template, \
             patch("pdd.agentic_architecture_orchestrator.console") as mock_console:
            mock_load_state.return_value = (None, None)
            mock_load_template.return_value = "Prompt for {issue_title}"
            mock_run.return_value = (True, "Step Output", 0.1, "gpt-4")
            mock_save_state.return_value = None

            yield {
                "run": mock_run,
                "load_state": mock_load_state,
                "save_state": mock_save_state,
                "clear_state": mock_clear_state,
                "load_template": mock_load_template,
                "console": mock_console,
            }

    @pytest.fixture
    def base_args(self, tmp_path):
        """Default args for architecture orchestrator."""
        arch_json = tmp_path / "architecture.json"
        arch_json.write_text('[{"name": "mod"}]')
        return {
            "issue_url": "http://github.com/owner/repo/issues/1",
            "issue_content": "Build a web app",
            "repo_owner": "owner",
            "repo_name": "repo",
            "issue_number": 1,
            "issue_author": "user",
            "issue_title": "Feature Request",
            "cwd": tmp_path,
            "verbose": False,
            "quiet": True,
            "timeout_adder": 0.0,
            "use_github_state": False,
            "skip_prompts": True,
        }

    def test_consecutive_failures_no_ratchet(self, mock_deps, base_args):
        """Consecutive failures should not advance last_completed_step."""
        saved_states = []

        def capture_save(*args, **kwargs):
            state = args[3] if len(args) > 3 else kwargs.get("state", {})
            saved_states.append(dict(state))
            return None

        mock_deps["save_state"].side_effect = capture_save
        mock_deps["run"].return_value = (False, "All agent providers failed", 0.0, "")

        from pdd.agentic_architecture_orchestrator import run_agentic_architecture_orchestrator
        run_agentic_architecture_orchestrator(**base_args)

        # After all failures, last_completed_step should remain 0
        final_state = saved_states[-1]
        assert final_state["last_completed_step"] == 0, (
            f"Expected last_completed_step=0 after all failures, "
            f"got {final_state['last_completed_step']} (ratchet effect)"
        )

    def test_failure_stores_failed_prefix(self, mock_deps, base_args):
        """Failed step outputs should be prefixed with 'FAILED:'."""
        saved_states = []

        def capture_save(*args, **kwargs):
            state = args[3] if len(args) > 3 else kwargs.get("state", {})
            saved_states.append(dict(state))
            return None

        mock_deps["save_state"].side_effect = capture_save
        # Step 1 fails, step 2 succeeds, then continue
        call_count = [0]

        def run_side_effect(*args, **kwargs):
            call_count[0] += 1
            if call_count[0] == 1:
                return (False, "Provider error", 0.0, "")
            return (True, "Step Output", 0.1, "gpt-4")

        mock_deps["run"].side_effect = run_side_effect

        from pdd.agentic_architecture_orchestrator import run_agentic_architecture_orchestrator
        run_agentic_architecture_orchestrator(**base_args)

        # First saved state should have FAILED: prefix for step 1
        first_state = saved_states[0]
        assert first_state["step_outputs"]["1"].startswith("FAILED:"), (
            "Failed step output should start with 'FAILED:'"
        )

    def test_resume_from_corrupted_state(self, mock_deps, base_args, tmp_path):
        """Resume from state with all FAILED outputs should re-run from step 1."""
        corrupted_state = {
            "last_completed_step": 5,
            "step_outputs": {
                "1": "FAILED: error",
                "2": "FAILED: error",
                "3": "FAILED: error",
                "4": "FAILED: error",
                "5": "FAILED: error",
            },
            "total_cost": 0.0,
            "model_used": "unknown",
            "scaffolding_files": [],
            "prompt_files": [],
        }
        mock_deps["load_state"].return_value = (corrupted_state, None)

        executed_labels = []

        def track_run(*args, **kwargs):
            label = kwargs.get("label", "")
            executed_labels.append(label)
            return (True, "Step Output", 0.1, "gpt-4")

        mock_deps["run"].side_effect = track_run

        from pdd.agentic_architecture_orchestrator import run_agentic_architecture_orchestrator
        run_agentic_architecture_orchestrator(**base_args)

        assert "step1" in executed_labels, (
            f"Step 1 should be re-executed when its cached output is FAILED, "
            f"but executed steps were: {executed_labels}"
        )

    def test_partial_failure_preserves_last_success(self, mock_deps, base_args):
        """Steps 1-3 succeed, 4+ fail: last_completed_step should be 3."""
        saved_states = []

        def capture_save(*args, **kwargs):
            state = args[3] if len(args) > 3 else kwargs.get("state", {})
            saved_states.append(dict(state))
            return None

        mock_deps["save_state"].side_effect = capture_save

        call_count = [0]

        def run_side_effect(*args, **kwargs):
            call_count[0] += 1
            if call_count[0] <= 3:
                return (True, "Success", 0.1, "gpt-4")
            return (False, "Provider error", 0.0, "")

        mock_deps["run"].side_effect = run_side_effect

        from pdd.agentic_architecture_orchestrator import run_agentic_architecture_orchestrator
        run_agentic_architecture_orchestrator(**base_args)

        final_state = saved_states[-1]
        assert final_state["last_completed_step"] == 3, (
            f"Expected last_completed_step=3, got {final_state['last_completed_step']}"
        )


# ============================================================================
# Tests for agentic_test_orchestrator (blind resume)
# ============================================================================


class TestTestOrchestratorIssue467:
    """Tests for Issue #467 blind resume fix in the test orchestrator."""

    @pytest.fixture
    def mock_deps(self):
        """Mock dependencies for test orchestrator."""
        with patch("pdd.agentic_test_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_test_orchestrator.load_workflow_state") as mock_load, \
             patch("pdd.agentic_test_orchestrator.save_workflow_state") as mock_save, \
             patch("pdd.agentic_test_orchestrator.clear_workflow_state") as mock_clear, \
             patch("pdd.agentic_test_orchestrator.load_prompt_template") as mock_template, \
             patch("pdd.agentic_test_orchestrator._setup_worktree") as mock_setup_wt, \
             patch("pdd.agentic_test_orchestrator.console") as mock_console, \
             patch("pdd.agentic_test_orchestrator._get_git_root") as mock_git_root:
            mock_load.return_value = (None, None)
            mock_template.return_value = "Prompt for {issue_number}"
            mock_run.return_value = (True, "Step Output", 0.1, "gpt-4")
            mock_save.return_value = None
            mock_setup_wt.return_value = (Path("/tmp/worktree"), None)
            mock_git_root.return_value = Path("/repo/root")

            yield {
                "run": mock_run,
                "load": mock_load,
                "save": mock_save,
                "clear": mock_clear,
                "template": mock_template,
                "console": mock_console,
            }

    @pytest.fixture
    def default_args(self, tmp_path):
        return {
            "issue_url": "http://github.com/o/r/issues/1",
            "issue_content": "Fix bug",
            "repo_owner": "owner",
            "repo_name": "repo",
            "issue_number": 1,
            "issue_author": "user",
            "issue_title": "Bug",
            "cwd": tmp_path,
            "quiet": True,
        }

    def test_resume_from_corrupted_state_reruns_failed(self, mock_deps, default_args):
        """Resume from state with all FAILED outputs should re-run from step 1."""
        corrupted_state = {
            "last_completed_step": 5,
            "step_outputs": {
                "1": "FAILED: error",
                "2": "FAILED: error",
                "3": "FAILED: error",
                "4": "FAILED: error",
                "5": "FAILED: error",
            },
            "total_cost": 0.0,
            "model_used": "unknown",
        }
        mock_deps["load"].return_value = (corrupted_state, None)

        executed_labels = []

        def track_run(*args, **kwargs):
            label = kwargs.get("label", "")
            executed_labels.append(label)
            return (True, "Step Output", 0.1, "gpt-4")

        mock_deps["run"].side_effect = track_run

        from pdd.agentic_test_orchestrator import run_agentic_test_orchestrator
        run_agentic_test_orchestrator(**default_args)

        assert "step1" in executed_labels, (
            f"Step 1 should be re-executed when cached output is FAILED, "
            f"but executed: {executed_labels}"
        )

    def test_partial_failure_reruns_from_correct_step(self, mock_deps, default_args):
        """Steps 1-3 cached OK, 4-5 FAILED: should resume from step 4."""
        corrupted_state = {
            "last_completed_step": 5,
            "step_outputs": {
                "1": "No duplicates",
                "2": "Codebase reviewed",
                "3": "Enough info",
                "4": "FAILED: error",
                "5": "FAILED: error",
            },
            "total_cost": 0.3,
            "model_used": "gpt-4",
        }
        mock_deps["load"].return_value = (corrupted_state, None)

        executed_labels = []

        def track_run(*args, **kwargs):
            label = kwargs.get("label", "")
            executed_labels.append(label)
            return (True, "Step Output", 0.1, "gpt-4")

        mock_deps["run"].side_effect = track_run

        from pdd.agentic_test_orchestrator import run_agentic_test_orchestrator
        run_agentic_test_orchestrator(**default_args)

        # Steps 1-3 should be skipped
        assert "step1" not in executed_labels
        assert "step2" not in executed_labels
        assert "step3" not in executed_labels
        # Step 4 should be re-run
        assert "step4" in executed_labels


# ============================================================================
# Tests for agentic_change_orchestrator (blind resume + line 706)
# ============================================================================


class TestChangeOrchestratorIssue467:
    """Tests for Issue #467 fixes in the change orchestrator."""

    @pytest.fixture
    def mock_deps(self, tmp_path):
        """Mock dependencies for change orchestrator."""
        with patch("pdd.agentic_change_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_change_orchestrator.load_prompt_template") as mock_template, \
             patch("pdd.agentic_change_orchestrator.load_workflow_state") as mock_load, \
             patch("pdd.agentic_change_orchestrator.save_workflow_state") as mock_save, \
             patch("pdd.agentic_change_orchestrator.clear_workflow_state") as mock_clear, \
             patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_subprocess, \
             patch("pdd.agentic_change_orchestrator.post_step_comment") as mock_post, \
             patch("pdd.agentic_change_orchestrator.console") as mock_console:
            mock_run.return_value = (True, "Default Output", 0.1, "gpt-4")
            mock_template.return_value = "Prompt for {issue_number}"
            mock_load.return_value = (None, None)
            mock_save.return_value = None
            mock_subprocess.return_value.stdout = str(tmp_path)
            mock_subprocess.return_value.returncode = 0
            mock_post.return_value = True

            yield {
                "run": mock_run,
                "template": mock_template,
                "load": mock_load,
                "save": mock_save,
                "clear": mock_clear,
                "console": mock_console,
            }

    @pytest.fixture
    def default_args(self, tmp_path):
        return {
            "issue_url": "http://github.com/o/r/issues/1",
            "issue_content": "Change request",
            "repo_owner": "owner",
            "repo_name": "repo",
            "issue_number": 1,
            "issue_author": "user",
            "issue_title": "Change",
            "cwd": tmp_path,
            "quiet": True,
            "use_github_state": False,
        }

    def test_resume_from_corrupted_state_reruns_failed(self, mock_deps, default_args):
        """Resume from corrupted state should re-run from first failed step."""
        corrupted_state = {
            "last_completed_step": 6,
            "step_outputs": {
                "1": "FAILED: error",
                "2": "FAILED: error",
                "3": "FAILED: error",
                "4": "FAILED: error",
                "5": "FAILED: error",
                "6": "FAILED: error",
            },
            "total_cost": 0.0,
            "model_used": "unknown",
        }
        mock_deps["load"].return_value = (corrupted_state, None)

        executed_labels = []

        def track_run(*args, **kwargs):
            label = kwargs.get("label", "")
            executed_labels.append(label)
            return (True, "Default Output", 0.1, "gpt-4")

        mock_deps["run"].side_effect = track_run

        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        run_agentic_change_orchestrator(**default_args)

        assert "step1" in executed_labels, (
            f"Step 1 should be re-executed when cached output is FAILED, "
            f"but executed: {executed_labels}"
        )

    def test_step9_no_files_does_not_use_step_num_minus_1(self, mock_deps, default_args, tmp_path):
        """Step 9 with no changed files should not use step_num - 1."""
        saved_states = []

        def capture_save(*args, **kwargs):
            state = args[3] if len(args) > 3 else kwargs.get("state", {})
            saved_states.append(dict(state))
            return None

        mock_deps["save"].side_effect = capture_save

        call_count = [0]

        def run_side_effect(*args, **kwargs):
            call_count[0] += 1
            label = kwargs.get("label", "")
            if label == "step9":
                # Step 9 succeeds but reports no FILES_CREATED/MODIFIED
                return (True, "No files changed", 0.1, "gpt-4")
            return (True, "Default Output", 0.1, "gpt-4")

        mock_deps["run"].side_effect = run_side_effect

        from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator
        success, msg, cost, model, files = run_agentic_change_orchestrator(**default_args)

        # When step 9 produces no files, it should return False
        assert not success
        assert "no file changes" in msg.lower()

        # The saved state should mark step 9 as FAILED, not use step_num - 1
        # Find the state saved right before the early return
        step9_states = [s for s in saved_states if "9" in s.get("step_outputs", {})]
        if step9_states:
            last = step9_states[-1]
            assert last["step_outputs"]["9"].startswith("FAILED:"), (
                "Step 9 with no files should be marked as FAILED"
            )


# ============================================================================
# Tests for agentic_e2e_fix_orchestrator (blind resume)
# ============================================================================


class TestE2eFixOrchestratorIssue467:
    """Tests for Issue #467 blind resume fix in the e2e fix orchestrator."""

    @pytest.fixture
    def mock_deps(self, tmp_path):
        """Mock dependencies for e2e fix orchestrator."""
        with patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task") as mock_run, \
             patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state") as mock_load, \
             patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state") as mock_save, \
             patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state") as mock_clear, \
             patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template") as mock_template, \
             patch("pdd.agentic_e2e_fix_orchestrator.console") as mock_console, \
             patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes") as mock_hashes, \
             patch("pdd.agentic_e2e_fix_orchestrator._commit_and_push") as mock_commit:
            mock_run.return_value = (True, "Step Output", 0.1, "gpt-4")
            mock_load.return_value = (None, None)
            mock_save.return_value = None
            mock_template.return_value = "Prompt for {issue_number}"
            mock_hashes.return_value = {}
            mock_commit.return_value = (True, "No changes")

            yield {
                "run": mock_run,
                "load": mock_load,
                "save": mock_save,
                "clear": mock_clear,
                "template": mock_template,
                "console": mock_console,
            }

    @pytest.fixture
    def default_args(self, tmp_path):
        return {
            "issue_url": "http://github.com/o/r/issues/1",
            "issue_content": "E2E test failure",
            "repo_owner": "owner",
            "repo_name": "repo",
            "issue_number": 1,
            "issue_author": "user",
            "issue_title": "E2E Fix",
            "cwd": tmp_path,
            "quiet": True,
            "max_cycles": 1,
            "resume": True,
            "use_github_state": False,
        }

    def test_resume_from_corrupted_state_reruns_failed(self, mock_deps, default_args):
        """Resume from corrupted state should re-run from first failed step."""
        corrupted_state = {
            "workflow": "e2e_fix",
            "issue_number": 1,
            "current_cycle": 1,
            "last_completed_step": 5,
            "step_outputs": {
                "1": "FAILED: error",
                "2": "FAILED: error",
                "3": "FAILED: error",
                "4": "FAILED: error",
                "5": "FAILED: error",
            },
            "total_cost": 0.0,
            "model_used": "unknown",
            "changed_files": [],
            "dev_unit_states": {},
        }
        mock_deps["load"].return_value = (corrupted_state, None)

        executed_labels = []

        def track_run(*args, **kwargs):
            label = kwargs.get("label", "")
            executed_labels.append(label)
            # Step 2: ALL_TESTS_PASS for early exit
            if "step2" in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, "Step Output", 0.1, "gpt-4")

        mock_deps["run"].side_effect = track_run

        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator
        run_agentic_e2e_fix_orchestrator(**default_args)

        assert any("step1" in l for l in executed_labels), (
            f"Step 1 should be re-executed when cached output is FAILED, "
            f"but executed: {executed_labels}"
        )

    def test_partial_failure_reruns_from_correct_step(self, mock_deps, default_args):
        """Steps 1-3 cached OK, 4-5 FAILED: should resume from step 4."""
        corrupted_state = {
            "workflow": "e2e_fix",
            "issue_number": 1,
            "current_cycle": 1,
            "last_completed_step": 5,
            "step_outputs": {
                "1": "Tests ran successfully",
                "2": "Some tests failing",
                "3": "Root cause identified",
                "4": "FAILED: error",
                "5": "FAILED: error",
            },
            "total_cost": 0.3,
            "model_used": "gpt-4",
            "changed_files": [],
            "dev_unit_states": {},
        }
        mock_deps["load"].return_value = (corrupted_state, None)

        executed_labels = []

        def track_run(*args, **kwargs):
            label = kwargs.get("label", "")
            executed_labels.append(label)
            if "step9" in label:
                return (True, "ALL_TESTS_PASS", 0.1, "gpt-4")
            return (True, "Step Output", 0.1, "gpt-4")

        mock_deps["run"].side_effect = track_run

        from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator
        run_agentic_e2e_fix_orchestrator(**default_args)

        # Steps 1-3 should be skipped
        assert not any("step1" in l for l in executed_labels)
        assert not any("step2" in l for l in executed_labels)
        assert not any("step3" in l for l in executed_labels)
        # Step 4 should be re-run
        assert any("step4" in l for l in executed_labels), (
            f"Step 4 should be re-executed, but executed: {executed_labels}"
        )
