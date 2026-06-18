"""Tests for pdd.agentic_checkup_orchestrator module."""
from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path
from typing import Dict, List, Optional
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_checkup_orchestrator import (
    CHECKUP_STEP_TIMEOUTS,
    MAX_FIX_VERIFY_ITERATIONS,
    STEP_ORDER,
    TOTAL_STEPS,
    _copy_uncommitted_changes,
    _discard_clean_run_side_effects,
    _format_pr_changed_files_for_prompt,
    _format_step_abort_message,
    _get_state_dir,
    _is_step_timeout_failure,
    _load_step5_shell_evidence_from_memory,
    _next_step,
    _normalised_failure_signal_text,
    _parse_changed_files,
    _parse_expansion_items,
    _parse_failure_signal_block,
    _pr_base_tracking_ref,
    _run_step5_shell_first_evidence,
    _select_step5_python_tests,
    _targeted_non_code_step5_result,
    run_agentic_checkup_orchestrator,
)


# Round-4 Finding 1: Step 7 must emit structured JSON for `_step7_passed`
# to permit the orchestrator to push or create a PR. Tests that previously
# only emitted the "All Issues Fixed" loop-exit sentinel now must include
# this JSON payload too. Trailing it on every step output is harmless —
# the JSON gate only consults the step-7 output.
STEP7_VERDICT_JSON = (
    '```json\n'
    '{"success": true, "message": "ok", "issue_aligned": true, '
    '"issues": [], "changed_files": []}\n'
    '```'
)
ALL_ISSUES_FIXED = f"All Issues Fixed\n{STEP7_VERDICT_JSON}"

# Round-8 Finding 1: the Step 5 prompt REQUIRES a structured
# ``failure_signal`` block, and the orchestrator now fails closed when
# it's missing or carries an unknown ``status`` word. Tests that intend
# Step 5 to be logically clean (provider success AND no test failures)
# must include this block so the orchestrator can verify the
# contract — otherwise the run is treated as a logical failure and the
# fixer is invoked, which is the safety behaviour the round-8 fix
# introduced.
STEP5_CLEAN_OUTPUT = (
    "All tests passed.\n"
    "```failure_signal\n"
    "command: pytest -q\n"
    "exit_code: 0\n"
    "status: pass\n"
    "failing_ids: none\n"
    "artifact_path: inline\n"
    "output: |\n"
    "  42 passed in 0.42s\n"
    "```"
)


class TestStep5ShellFirstEvidence:
    def test_selects_existing_python_tests_from_changed_modules(self, tmp_path):
        (tmp_path / "pdd").mkdir()
        (tmp_path / "pdd" / "widget.py").write_text("VALUE = 1\n", encoding="utf-8")
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "test_widget.py").write_text(
            "def test_widget(): pass\n",
            encoding="utf-8",
        )

        selected = _select_step5_python_tests(tmp_path, ["pdd/widget.py"])

        assert selected == ["tests/test_widget.py"]

    def test_persists_failed_pytest_evidence(self, tmp_path, monkeypatch):
        (tmp_path / "pdd").mkdir()
        (tmp_path / "pdd" / "widget.py").write_text("VALUE = 1\n", encoding="utf-8")
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "test_widget.py").write_text(
            "def test_widget(): pass\n",
            encoding="utf-8",
        )
        env_token = "customToken123456789"
        gh_token = "ghp_" + "A" * 36
        monkeypatch.setenv("GITHUB_TOKEN", env_token)
        context = {
            "pr_mode": "true",
            "pr_scope_changed_files": "Base: refs/remotes/pdd-checkup/pr-1/base\n"
            f"- M: pdd/widget.py\n- M: docs/{gh_token}.txt",
        }
        completed = subprocess.CompletedProcess(
            args=["python", "-m", "pytest", "-q", "tests/test_widget.py"],
            returncode=1,
            stdout=(
                "FAILED tests/test_widget.py::test_breaks\n"
                f"Authorization: Bearer {gh_token}\n"
                f"env token: {env_token}\n"
            ),
            stderr="",
        )

        with patch(
            "pdd.agentic_checkup_orchestrator.subprocess.run",
            return_value=completed,
        ) as run_mock:
            evidence = _run_step5_shell_first_evidence(
                context,
                tmp_path,
                tmp_path,
                pr_number=1,
                iteration=2,
                quiet=True,
            )

        assert evidence is not None
        assert evidence["status"] == "failed"
        assert evidence["selected_tests"] == ["tests/test_widget.py"]
        assert "tests/test_widget.py::test_breaks" in evidence["output"]
        assert "step5_shell_evidence" in context
        artifact = tmp_path / ".pdd" / "checkup-pr-1" / "layer1-step5-evidence.json"
        assert not artifact.exists()
        payload = _load_step5_shell_evidence_from_memory(tmp_path, 1)
        assert payload is not None
        assert payload["status"] == "failed"
        assert "tests/test_widget.py::test_breaks" in context["step5_shell_evidence"]
        memory_text = json.dumps(payload, indent=2, sort_keys=True)
        assert "tests/test_widget.py::test_breaks" in memory_text
        artifact_text = memory_text
        assert gh_token not in artifact_text
        assert env_token not in artifact_text
        assert gh_token not in context["step5_shell_evidence"]
        assert env_token not in context["step5_shell_evidence"]
        assert run_mock.call_args.args[0][-1] == "tests/test_widget.py"


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

        mock_run.return_value = (True, f"Step output. {ALL_ISSUES_FIXED}", 0.1, "gpt-4")
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
            return (True, f"Output {call_counter[0]}. {ALL_ISSUES_FIXED}", call_counter[0] * 0.1, "gpt-4")

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
            return (True, f"Output for {label}. {ALL_ISSUES_FIXED}", 0.1, "gpt-4")

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

    def test_timeout_on_step_5_aborts_no_fix_before_step_7_with_timeout_message(
        self, mock_dependencies, default_args, tmp_path
    ):
        """A Step 5 agent timeout should not be reported as provider outage."""
        mock_run, _, _, _ = mock_dependencies
        default_args["no_fix"] = True
        default_args["cwd"] = tmp_path

        saved_states = []

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if label == "step5":
                return (False, "All agent providers failed: openai: Timeout expired", 0.0, "")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        def capture_state(cwd, issue_number, workflow_type, state, state_dir,
                          repo_owner, repo_name, use_github_state=True,
                          github_comment_id=None):
            saved_states.append(state.copy())
            return None

        mock_run.side_effect = side_effect

        with patch("pdd.agentic_checkup_orchestrator.save_workflow_state",
                   side_effect=capture_state):
            success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)

        assert success is False
        assert "timed out" in msg
        assert "agent providers unavailable" not in msg
        assert "Step 5" in msg
        assert mock_run.call_count == 5

        called_labels = [c.kwargs["label"] for c in mock_run.call_args_list]
        assert "step7" not in called_labels

        final_state = saved_states[-1]
        assert final_state["last_completed_step"] == 4
        assert final_state["step_outputs"]["5"] == (
            "FAILED: All agent providers failed: openai: Timeout expired"
        )
        assert "6_1" not in final_state["step_outputs"]

    def test_start_step_7_runs_verify_without_rerunning_step_5(
        self, mock_dependencies, default_args
    ):
        """Recovery override can jump past a stuck test step to Step 7."""
        mock_run, mock_load, _, _ = mock_dependencies
        default_args["no_fix"] = True
        default_args["start_step_override"] = 7
        mock_load.return_value = (
            "step5={step5_output}\n"
            "step6={step6_1_output}\n"
            "pr_files={pr_changed_files}"
        )

        success, _msg, _cost, _model = run_agentic_checkup_orchestrator(
            **default_args
        )

        assert success is True
        assert [c.kwargs["label"] for c in mock_run.call_args_list] == ["step7"]

    # ------------------------------------------------------------------
    # --no-fix --pr Step 5 status contract (issue #1212 round-12)
    # ------------------------------------------------------------------

    def _make_pr_nofix_patches(self, tmp_path, step5_output: str):
        """Return context manager that runs --no-fix --pr with a given Step 5 output."""
        from unittest.mock import patch as _patch

        wt = tmp_path / "wt"
        wt.mkdir()
        stable_metadata = {
            "clone_url": "https://github.com/o/r.git",
            "head_ref": "change/test",
            "head_owner": "o",
            "head_repo": "r",
            "head_sha": "deadbeef0000",
        }

        def run_step(step_num, _name, _ctx, **_kw):
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.0, "fake")
            if step_num == 5:
                return (True, step5_output, 0.0, "fake")
            return (True, f"out-{step_num}", 0.0, "fake")

        return (
            _patch("pdd.agentic_checkup_orchestrator._setup_pr_worktree", return_value=(wt, None)),
            _patch("pdd.agentic_checkup_orchestrator._fetch_pr_metadata", return_value=stable_metadata),
            _patch("pdd.agentic_checkup_orchestrator.load_workflow_state", return_value=(None, None)),
            _patch("pdd.agentic_checkup_orchestrator.save_workflow_state", return_value=None),
            _patch("pdd.agentic_checkup_orchestrator.clear_workflow_state"),
            _patch("pdd.agentic_checkup_orchestrator._run_single_step", side_effect=run_step),
        )

    def _run_pr_nofix(self, tmp_path, step5_output: str):
        patches = self._make_pr_nofix_patches(tmp_path, step5_output)
        with patches[0], patches[1], patches[2], patches[3], patches[4], patches[5]:
            return run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=True,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

    def test_nofix_pr_step5_skipped_status_returns_failure(self, tmp_path):
        """--no-fix --pr must fail when Step 5 reports status: skipped."""
        step5_out = (
            "No test suite found.\n"
            "```failure_signal\n"
            "status: skipped\n"
            "exit_code: skipped\n"
            "failing_ids: none\n"
            "artifact_path: none\n"
            "output: No tests found.\n"
            "```\n"
        )
        success, msg, _cost, _model = self._run_pr_nofix(tmp_path, step5_out)
        assert success is False
        assert "skipped" in msg.lower()
        assert "tests did not run" in msg.lower()

    def test_nofix_pr_step5_logical_failure_returns_failure(self, tmp_path):
        """--no-fix --pr must fail when Step 5 block says status: fail."""
        step5_out = (
            "Test suite failed.\n"
            "```failure_signal\n"
            "status: fail\n"
            "exit_code: 1\n"
            "failing_ids: test_foo\n"
            "artifact_path: none\n"
            "output: FAILED test_foo.\n"
            "```\n"
        )
        success, msg, _cost, _model = self._run_pr_nofix(tmp_path, step5_out)
        assert success is False
        assert "test failure" in msg.lower()

    def test_nofix_pr_step5_missing_block_returns_failure(self, tmp_path):
        """--no-fix --pr must fail closed when failure_signal block is missing."""
        step5_out = "Tests ran and some failed (prose only, no structured block)."
        success, msg, _cost, _model = self._run_pr_nofix(tmp_path, step5_out)
        assert success is False
        assert "test failure" in msg.lower()
        assert "missing or malformed" in msg.lower()

    def test_nofix_pr_step5_empty_output_returns_failure(self, tmp_path):
        """--no-fix --pr must fail closed when Step 5 produces empty output.

        Pass-17 Finding 1: a provider returning success with empty Step 5
        output previously skipped the gate (the `if _s5_raw:` truthiness
        guard) and returned 'Checkup complete' without any test evidence.
        Empty output is now parsed as a missing block and fails closed.
        """
        success, msg, _cost, _model = self._run_pr_nofix(tmp_path, "")
        assert success is False
        assert "test failure" in msg.lower()
        assert "missing or malformed" in msg.lower()

    def test_nofix_pr_step5_skipped_on_resume_returns_failure(self, tmp_path):
        """Resumed --no-fix --pr must still fail when cached Step 5 is skipped.

        Round-14 Finding 1: when start_step > 5 the Step 5 block in the loop
        is skipped via `continue`, so the post-loop gate must read from
        step_outputs (loaded from state) to catch the cached skipped status.
        """
        from unittest.mock import patch as _patch

        wt = tmp_path / "wt"
        wt.mkdir()
        step5_skipped_out = (
            "No test suite found.\n"
            "```failure_signal\n"
            "status: skipped\n"
            "exit_code: skipped\n"
            "failing_ids: none\n"
            "artifact_path: none\n"
            "output: No tests found.\n"
            "```\n"
        )
        # Simulate cached state where Step 5 completed with status: skipped
        cached_state = {
            "mode": "pr",
            "pr_number": 200,
            "pr_owner": "o",
            "pr_repo": "r",
            "pr_head_sha": "deadbeef0000",
            "last_completed_step": 5,
            "step_outputs": {
                "1": "Discovered project",
                "2": "Deps ok",
                "3": "Build ok",
                "4": "Interfaces ok",
                "5": step5_skipped_out,
            },
            "changed_files": [],
            "total_cost": 0.1,
            "model_used": "fake",
            "fix_verify_iteration": 0,
            "previous_fixes": "",
        }
        stable_metadata = {
            "clone_url": "https://github.com/o/r.git",
            "head_ref": "change/test",
            "head_owner": "o",
            "head_repo": "r",
            "head_sha": "deadbeef0000",
        }

        def run_step(step_num, _name, _ctx, **_kw):
            return (True, ALL_ISSUES_FIXED, 0.0, "fake")

        with (
            _patch("pdd.agentic_checkup_orchestrator._setup_pr_worktree", return_value=(wt, None)),
            _patch("pdd.agentic_checkup_orchestrator._fetch_pr_metadata", return_value=stable_metadata),
            _patch("pdd.agentic_checkup_orchestrator.load_workflow_state", return_value=(cached_state, None)),
            _patch("pdd.agentic_checkup_orchestrator.save_workflow_state", return_value=None),
            _patch("pdd.agentic_checkup_orchestrator.clear_workflow_state"),
            _patch("pdd.agentic_checkup_orchestrator._run_single_step", side_effect=run_step),
        ):
            success, msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=True,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success is False, f"Expected failure, got success. msg={msg!r}"
        assert "skipped" in msg.lower()
        assert "tests did not run" in msg.lower()

    def test_nofix_pr_step5_refusal_writes_artifact(self, tmp_path):
        """--no-fix --pr refusal must write a durable artifact file."""
        step5_out = (
            "No tests.\n"
            "```failure_signal\n"
            "status: skipped\n"
            "exit_code: skipped\n"
            "failing_ids: none\n"
            "artifact_path: none\n"
            "output: No tests.\n"
            "```\n"
        )
        self._run_pr_nofix(tmp_path, step5_out)
        art_dir = tmp_path / ".pdd" / "checkup-pr-200"
        assert art_dir.exists(), "Artifact directory was not created"
        assert (art_dir / "nofix-step5-skipped-refusal.txt").exists(), (
            "Refusal artifact file was not written"
        )

    def test_nofix_pr_step5_refusal_clears_workflow_state(self, tmp_path):
        """Early refusal must call clear_workflow_state so the next run reruns Step 5.

        Round-17 Fix: without clear_workflow_state the next pdd checkup --pr
        --no-fix reuses cached step_outputs["5"] and fires the same refusal
        again even after the user fixes the test environment.
        """
        from unittest.mock import patch as _patch, MagicMock

        wt = tmp_path / "wt"
        wt.mkdir()
        stable_metadata = {
            "clone_url": "https://github.com/o/r.git",
            "head_ref": "change/test",
            "head_owner": "o",
            "head_repo": "r",
            "head_sha": "deadbeef0000",
        }
        step5_out = (
            "No test suite found.\n"
            "```failure_signal\n"
            "status: skipped\n"
            "exit_code: skipped\n"
            "failing_ids: none\n"
            "artifact_path: none\n"
            "output: No tests found.\n"
            "```\n"
        )

        def run_step(step_num, _name, _ctx, **_kw):
            if step_num == 5:
                return (True, step5_out, 0.0, "fake")
            return (True, f"out-{step_num}", 0.0, "fake")

        mock_clear = MagicMock()
        with (
            _patch("pdd.agentic_checkup_orchestrator._setup_pr_worktree", return_value=(wt, None)),
            _patch("pdd.agentic_checkup_orchestrator._fetch_pr_metadata", return_value=stable_metadata),
            _patch("pdd.agentic_checkup_orchestrator.load_workflow_state", return_value=(None, None)),
            _patch("pdd.agentic_checkup_orchestrator.save_workflow_state", return_value=None),
            _patch("pdd.agentic_checkup_orchestrator.clear_workflow_state", mock_clear),
            _patch("pdd.agentic_checkup_orchestrator._run_single_step", side_effect=run_step),
        ):
            success, _msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=True,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success is False
        assert mock_clear.called, (
            "clear_workflow_state must be called on early no-fix refusal to "
            "prevent stale-cache replay on the next run"
        )

    def test_nofix_pr_step5_refusal_reruns_step5_on_second_run(self, tmp_path):
        """Round-17 Finding 2: prove the fix end-to-end with the REAL
        clear_workflow_state against real local state — two consecutive
        --no-fix --pr runs must BOTH execute Step 5 (the first run's
        clear wipes the cached skipped output so the second is not a
        stale-cache replay)."""
        from unittest.mock import patch as _patch

        wt = tmp_path / "wt"
        wt.mkdir()
        stable_metadata = {
            "clone_url": "https://github.com/o/r.git",
            "head_ref": "change/test",
            "head_owner": "o",
            "head_repo": "r",
            "head_sha": "deadbeef0000",
        }
        step5_out = (
            "No test suite found.\n"
            "```failure_signal\n"
            "status: skipped\n"
            "exit_code: skipped\n"
            "failing_ids: none\n"
            "artifact_path: none\n"
            "output: No tests found.\n"
            "```\n"
        )

        step5_calls = {"n": 0}

        def run_step(step_num, _name, _ctx, **_kw):
            if step_num == 5:
                step5_calls["n"] += 1
                return (True, step5_out, 0.0, "fake")
            return (True, f"out-{step_num}", 0.0, "fake")

        common_args = dict(
            issue_url="https://github.com/o/r/issues/99",
            issue_content="stub",
            repo_owner="o",
            repo_name="r",
            issue_number=99,
            issue_title="stub",
            architecture_json="{}",
            pddrc_content="",
            cwd=tmp_path,
            verbose=False,
            quiet=True,
            no_fix=True,
            timeout_adder=0.0,
            # use_github_state=False keeps clear/load against the real
            # LOCAL state file so we exercise the genuine clear path.
            use_github_state=False,
            pr_url="https://github.com/o/r/pull/200",
            pr_owner="o",
            pr_repo="r",
            pr_number=200,
        )

        # NOTE: clear_workflow_state is NOT mocked — we want the real
        # local-state deletion to happen between runs.
        for _run in range(2):
            with (
                _patch("pdd.agentic_checkup_orchestrator._setup_pr_worktree", return_value=(wt, None)),
                _patch("pdd.agentic_checkup_orchestrator._fetch_pr_metadata", return_value=stable_metadata),
                _patch("pdd.agentic_checkup_orchestrator._run_single_step", side_effect=run_step),
            ):
                success, _msg, _cost, _model = run_agentic_checkup_orchestrator(**common_args)
            assert success is False

        assert step5_calls["n"] == 2, (
            "Step 5 must run on BOTH runs — the first run's "
            "clear_workflow_state must have wiped the cached skipped "
            f"output so the second run is not a stale replay. Got "
            f"{step5_calls['n']} Step 5 call(s)."
        )

    def test_nofix_pr_step5_refusal_warns_when_clear_unconfirmed(self, tmp_path):
        """Round-17 Finding 1: when clear_workflow_state cannot confirm the
        clear (e.g. the GitHub state comment could neither be deleted nor
        neutralised), the returned message must warn the operator that a
        rerun may replay the cached result."""
        from unittest.mock import patch as _patch

        wt = tmp_path / "wt"
        wt.mkdir()
        stable_metadata = {
            "clone_url": "https://github.com/o/r.git",
            "head_ref": "change/test",
            "head_owner": "o",
            "head_repo": "r",
            "head_sha": "deadbeef0000",
        }
        step5_out = (
            "No test suite found.\n"
            "```failure_signal\n"
            "status: skipped\n"
            "exit_code: skipped\n"
            "failing_ids: none\n"
            "artifact_path: none\n"
            "output: No tests found.\n"
            "```\n"
        )

        def run_step(step_num, _name, _ctx, **_kw):
            if step_num == 5:
                return (True, step5_out, 0.0, "fake")
            return (True, f"out-{step_num}", 0.0, "fake")

        with (
            _patch("pdd.agentic_checkup_orchestrator._setup_pr_worktree", return_value=(wt, None)),
            _patch("pdd.agentic_checkup_orchestrator._fetch_pr_metadata", return_value=stable_metadata),
            _patch("pdd.agentic_checkup_orchestrator.load_workflow_state", return_value=(None, None)),
            _patch("pdd.agentic_checkup_orchestrator.save_workflow_state", return_value=None),
            # Simulate an unconfirmed clear (remote comment stuck).
            _patch("pdd.agentic_checkup_orchestrator.clear_workflow_state", return_value=False),
            _patch("pdd.agentic_checkup_orchestrator._run_single_step", side_effect=run_step),
        ):
            success, msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=True,
                timeout_adder=0.0,
                use_github_state=True,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
            )

        assert success is False
        assert "could not confirm" in (msg or "").lower(), (
            f"Expected an unconfirmed-clear warning in the message; got {msg!r}"
        )


class TestClearWorkflowStateRemoteNeutralize:
    """Round-17 Finding 1 (root cause): github_clear_state must neutralise
    a state comment it cannot DELETE so load_workflow_state — which loads
    GitHub state with priority over local — can't replay it."""

    def test_neutralizes_comment_when_delete_fails(self):
        from unittest.mock import patch as _patch
        from pdd import agentic_common

        edited = {}

        def fake_edit(_owner, _repo, cid, body, _cwd):
            edited["id"] = cid
            edited["body"] = body
            return True

        with (
            _patch.object(agentic_common, "_find_all_state_comments", return_value=[123]),
            _patch.object(agentic_common, "_github_delete_comment", return_value=False),
            _patch.object(agentic_common, "_github_edit_comment", side_effect=fake_edit),
        ):
            ok = agentic_common.github_clear_state("o", "r", 99, "checkup", Path("/tmp"))

        assert ok is True, "Neutralise fallback should count as a successful clear"
        assert edited.get("id") == 123
        # The tombstone body must NOT contain the live state marker.
        assert agentic_common.GITHUB_STATE_MARKER_START not in edited.get("body", ""), (
            "Neutralised body must not carry the PDD_WORKFLOW_STATE marker, "
            "or load_workflow_state would still parse it as resumable state."
        )

    def test_returns_false_when_delete_and_edit_both_fail(self):
        from unittest.mock import patch as _patch
        from pdd import agentic_common

        with (
            _patch.object(agentic_common, "_find_all_state_comments", return_value=[123]),
            _patch.object(agentic_common, "_github_delete_comment", return_value=False),
            _patch.object(agentic_common, "_github_edit_comment", return_value=False),
        ):
            ok = agentic_common.github_clear_state("o", "r", 99, "checkup", Path("/tmp"))

        assert ok is False, (
            "When a state comment can be neither deleted nor neutralised, "
            "github_clear_state must report failure so callers can warn."
        )

    def test_delete_success_does_not_attempt_edit(self):
        from unittest.mock import patch as _patch
        from pdd import agentic_common

        edit_mock = MagicMock()
        with (
            _patch.object(agentic_common, "_find_all_state_comments", return_value=[1, 2]),
            _patch.object(agentic_common, "_github_delete_comment", return_value=True),
            _patch.object(agentic_common, "_github_edit_comment", edit_mock),
        ):
            ok = agentic_common.github_clear_state("o", "r", 99, "checkup", Path("/tmp"))

        assert ok is True
        edit_mock.assert_not_called()

    def test_clear_workflow_state_returns_false_on_remote_failure(self, tmp_path):
        from unittest.mock import patch as _patch
        from pdd import agentic_common

        with (
            _patch.object(agentic_common, "_should_use_github_state", return_value=True),
            _patch.object(agentic_common, "github_clear_state", return_value=False),
        ):
            ok = agentic_common.clear_workflow_state(
                cwd=tmp_path,
                issue_number=99,
                workflow_type="checkup",
                state_dir=tmp_path / ".pdd" / "checkup-state",
                repo_owner="o",
                repo_name="r",
                use_github_state=True,
            )
        assert ok is False


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
            return (True, f"Output for {label}. {ALL_ISSUES_FIXED}", 0.1, "gpt-4")

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
    @staticmethod
    def _init_git_repo(path: Path, initial_branch: str = "master") -> None:
        subprocess.run(["git", "init"], cwd=path, check=True, capture_output=True)
        subprocess.run(
            ["git", "branch", "-m", initial_branch],
            cwd=path,
            check=True,
            capture_output=True,
        )
        subprocess.run(
            ["git", "config", "user.email", "test@example.com"],
            cwd=path,
            check=True,
            capture_output=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Test User"],
            cwd=path,
            check=True,
            capture_output=True,
        )

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

    def test_timeout_detects_runner_timeout_messages(self):
        """Timeout failures should be classified separately from provider outages."""
        assert _is_step_timeout_failure(
            "All agent providers failed: openai: Timeout expired"
        )
        assert _is_step_timeout_failure("subprocess.TimeoutExpired after 600s")
        assert _is_step_timeout_failure("Agent timed out while running tests")
        assert not _is_step_timeout_failure(
            "All agent providers failed: openai: request timed out"
        )

    def test_timeout_abort_message_is_not_provider_outage(self):
        """A timeout wrapped in provider failure text should get timeout wording."""
        msg = _format_step_abort_message(
            5,
            "All agent providers failed: openai: Timeout expired",
        )

        assert "timed out" in msg
        assert "agent providers unavailable" not in msg

    def test_format_pr_changed_files_uses_base_ref_diff(self, tmp_path):
        """PR-mode prompt context should list merge-base changed files."""
        self._init_git_repo(tmp_path)
        (tmp_path / "app.py").write_text("print('base')\n", encoding="utf-8")
        subprocess.run(["git", "add", "app.py"], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "base"], cwd=tmp_path, check=True)
        subprocess.run(["git", "branch", "base"], cwd=tmp_path, check=True)
        subprocess.run(["git", "checkout", "-b", "feature"], cwd=tmp_path, check=True)
        (tmp_path / "app.py").write_text("print('feature')\n", encoding="utf-8")
        (tmp_path / "tests").mkdir()
        (tmp_path / "tests" / "test_app.py").write_text(
            "def test_app():\n    assert True\n",
            encoding="utf-8",
        )
        subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "feature"], cwd=tmp_path, check=True)
        base_ref = _pr_base_tracking_ref(77)
        subprocess.run(
            ["git", "update-ref", base_ref, "base"],
            cwd=tmp_path,
            check=True,
        )

        result = _format_pr_changed_files_for_prompt(
            tmp_path,
            {"base_ref": "base", "base_local_ref": base_ref},
        )

        assert f"Base: {base_ref}" in result
        assert "- M: app.py" in result
        assert "- A: tests/test_app.py" in result

    def test_targeted_step5_docs_only_uses_diff_check_fast_path(self, tmp_path):
        """Docs-only targeted PRs should not ask the agent to run full suites."""
        self._init_git_repo(tmp_path)
        (tmp_path / "README.md").write_text("base\n", encoding="utf-8")
        subprocess.run(["git", "add", "README.md"], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "base"], cwd=tmp_path, check=True)
        subprocess.run(["git", "branch", "base"], cwd=tmp_path, check=True)
        subprocess.run(["git", "checkout", "-b", "feature"], cwd=tmp_path, check=True)
        (tmp_path / "staging2_checkup.md").write_text("marker\n", encoding="utf-8")
        subprocess.run(["git", "add", "staging2_checkup.md"], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "docs"], cwd=tmp_path, check=True)
        base_ref = _pr_base_tracking_ref(77)
        subprocess.run(["git", "update-ref", base_ref, "base"], cwd=tmp_path, check=True)
        changed_files = _format_pr_changed_files_for_prompt(
            tmp_path,
            {"base_ref": "base", "base_local_ref": base_ref},
        )

        result = _targeted_non_code_step5_result(
            {
                "pr_mode": "true",
                "pr_test_scope": "targeted",
                "pr_changed_files": changed_files,
            },
            tmp_path,
            iteration=1,
        )

        assert result is not None
        success, output, cost, model = result
        assert success is True
        assert cost == 0.0
        assert model == "deterministic-step5"
        assert "git diff --check" in output
        assert "status: pass" in output
        assert "0 executable tests" in output

    def test_targeted_step5_code_change_uses_agent_path(self, tmp_path):
        """Code-like paths still need normal targeted test selection."""
        result = _targeted_non_code_step5_result(
            {
                "pr_mode": "true",
                "pr_test_scope": "targeted",
                "pr_changed_files": "Base: refs/pdd/base\n- A: src/app.py",
            },
            tmp_path,
            iteration=1,
        )

        assert result is None

    def test_format_pr_changed_files_includes_all_pr_commits(self, tmp_path):
        """Merge-base diff should not collapse multi-commit PRs to HEAD~1."""
        self._init_git_repo(tmp_path)
        (tmp_path / "README.md").write_text("base\n", encoding="utf-8")
        subprocess.run(["git", "add", "README.md"], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "base"], cwd=tmp_path, check=True)
        subprocess.run(["git", "branch", "base"], cwd=tmp_path, check=True)
        subprocess.run(["git", "checkout", "-b", "feature"], cwd=tmp_path, check=True)

        (tmp_path / "first.py").write_text("print('first')\n", encoding="utf-8")
        subprocess.run(["git", "add", "first.py"], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "first"], cwd=tmp_path, check=True)

        (tmp_path / "second.py").write_text("print('second')\n", encoding="utf-8")
        subprocess.run(["git", "add", "second.py"], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "second"], cwd=tmp_path, check=True)
        base_ref = _pr_base_tracking_ref(77)
        subprocess.run(
            ["git", "update-ref", base_ref, "base"],
            cwd=tmp_path,
            check=True,
        )

        result = _format_pr_changed_files_for_prompt(
            tmp_path,
            {"base_ref": "base", "base_local_ref": base_ref},
        )

        assert f"Base: {base_ref}" in result
        assert "- A: first.py" in result
        assert "- A: second.py" in result

    def test_format_pr_changed_files_uses_refreshed_base_not_stale_origin(
        self, tmp_path
    ):
        """A stale origin/main must not broaden PR-scoped test context."""
        self._init_git_repo(tmp_path, initial_branch="main")
        (tmp_path / "README.md").write_text("base\n", encoding="utf-8")
        subprocess.run(["git", "add", "README.md"], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "root"], cwd=tmp_path, check=True)
        root_sha = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=tmp_path,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
        subprocess.run(
            ["git", "update-ref", "refs/remotes/origin/main", root_sha],
            cwd=tmp_path,
            check=True,
        )

        (tmp_path / "base_only.py").write_text("print('base')\n", encoding="utf-8")
        subprocess.run(["git", "add", "base_only.py"], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "advance base"], cwd=tmp_path, check=True)
        base_sha = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=tmp_path,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
        base_ref = _pr_base_tracking_ref(77)
        subprocess.run(
            ["git", "update-ref", base_ref, base_sha],
            cwd=tmp_path,
            check=True,
        )

        subprocess.run(["git", "checkout", "-b", "feature"], cwd=tmp_path, check=True)
        (tmp_path / "feature.py").write_text("print('feature')\n", encoding="utf-8")
        subprocess.run(["git", "add", "feature.py"], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "feature"], cwd=tmp_path, check=True)

        result = _format_pr_changed_files_for_prompt(
            tmp_path,
            {"base_ref": "main", "base_local_ref": base_ref},
        )

        assert "- A: feature.py" in result
        assert "base_only.py" not in result

    def test_format_pr_changed_files_requires_refreshed_pr_base(self, tmp_path):
        """PR metadata must not fall back to stale origin/<base>."""
        self._init_git_repo(tmp_path, initial_branch="main")
        (tmp_path / "README.md").write_text("base\n", encoding="utf-8")
        subprocess.run(["git", "add", "README.md"], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "root"], cwd=tmp_path, check=True)
        subprocess.run(["git", "update-ref", "refs/remotes/origin/main", "HEAD"], cwd=tmp_path, check=True)
        subprocess.run(["git", "checkout", "-b", "feature"], cwd=tmp_path, check=True)
        (tmp_path / "feature.py").write_text("print('feature')\n", encoding="utf-8")
        subprocess.run(["git", "add", "feature.py"], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "feature"], cwd=tmp_path, check=True)

        result = _format_pr_changed_files_for_prompt(
            tmp_path,
            {"base_ref": "main"},
        )

        assert result.startswith("PR changed files unavailable")
        assert "Do not use stale origin/main" in result
        assert "feature.py" not in result

    def test_format_pr_changed_files_uses_api_fallback_when_base_fetch_fails(
        self, tmp_path
    ):
        """A failed git base refresh should still keep PR-scoped files if API data exists."""
        result = _format_pr_changed_files_for_prompt(
            tmp_path,
            {
                "base_ref": "main",
                "base_ref_fetch_error": "network unreachable",
                "api_changed_files": (
                    "- ADDED: feature.py\n"
                    "- RENAMED: old_name.py -> new_name.py"
                ),
            },
        )

        assert result.startswith("Source: GitHub PR files API")
        assert "- ADDED: feature.py" in result
        assert "- RENAMED: old_name.py -> new_name.py" in result
        assert "origin/main" not in result

    def test_format_pr_changed_files_uses_api_fallback_when_base_metadata_missing(
        self, tmp_path
    ):
        """Failed PR metadata should still use PR files API data when present."""
        result = _format_pr_changed_files_for_prompt(
            tmp_path,
            {"api_changed_files": "- MODIFIED: src/feature.py"},
        )

        assert result == "Source: GitHub PR files API\n- MODIFIED: src/feature.py"

    def test_format_pr_changed_files_writes_full_api_fallback_artifact(
        self, tmp_path
    ):
        """A truncated API preview should point agents at the full local file list."""
        result = _format_pr_changed_files_for_prompt(
            tmp_path,
            {
                "base_ref": "main",
                "base_ref_fetch_error": "network unreachable",
                "api_changed_files": (
                    "- MODIFIED: pdd/file_0.py\n"
                    "NOTE: GitHub PR files API list truncated; showing 1 of 2 files."
                ),
                "api_changed_files_full": (
                    "- MODIFIED: pdd/file_0.py\n"
                    "- MODIFIED: pdd/file_1.py"
                ),
            },
        )

        artifact = tmp_path / ".pdd" / "checkup-context" / "pr-changed-files-api.txt"
        assert (
            "Full API changed-file list artifact: "
            ".pdd/checkup-context/pr-changed-files-api.txt"
        ) in result
        assert artifact.read_text(encoding="utf-8") == (
            "- MODIFIED: pdd/file_0.py\n"
            "- MODIFIED: pdd/file_1.py\n"
        )

    def test_format_pr_changed_files_missing_pr_metadata_is_unavailable(self, tmp_path):
        """PR mode with failed metadata fetch must not use conventional fallbacks."""
        self._init_git_repo(tmp_path, initial_branch="main")
        (tmp_path / "README.md").write_text("base\n", encoding="utf-8")
        subprocess.run(["git", "add", "README.md"], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "root"], cwd=tmp_path, check=True)
        subprocess.run(
            ["git", "update-ref", "refs/remotes/origin/main", "HEAD"],
            cwd=tmp_path,
            check=True,
        )
        subprocess.run(["git", "checkout", "-b", "feature"], cwd=tmp_path, check=True)
        (tmp_path / "feature.py").write_text("print('feature')\n", encoding="utf-8")
        subprocess.run(["git", "add", "feature.py"], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "feature"], cwd=tmp_path, check=True)

        result = _format_pr_changed_files_for_prompt(tmp_path, {})

        assert result.startswith("PR changed files unavailable")
        assert "metadata is missing" in result
        assert "feature.py" not in result

    def test_format_pr_changed_files_does_not_use_head_parent_fallback(self, tmp_path):
        """Missing base refs should be explicit instead of diffing only HEAD~1."""
        self._init_git_repo(tmp_path, initial_branch="trunk")
        (tmp_path / "README.md").write_text("base\n", encoding="utf-8")
        subprocess.run(["git", "add", "README.md"], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "base"], cwd=tmp_path, check=True)
        subprocess.run(["git", "checkout", "-b", "feature"], cwd=tmp_path, check=True)

        (tmp_path / "first.py").write_text("print('first')\n", encoding="utf-8")
        subprocess.run(["git", "add", "first.py"], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "first"], cwd=tmp_path, check=True)

        (tmp_path / "second.py").write_text("print('second')\n", encoding="utf-8")
        subprocess.run(["git", "add", "second.py"], cwd=tmp_path, check=True)
        subprocess.run(["git", "commit", "-m", "second"], cwd=tmp_path, check=True)

        result = _format_pr_changed_files_for_prompt(tmp_path)

        assert result.startswith("PR changed files unavailable")
        assert "Do not infer PR scope from HEAD~1" in result
        assert "second.py" not in result

    def _run_orchestrator_capturing_context(
        self,
        tmp_path,
        *,
        test_scope: str,
        format_call_count: list,
    ):
        """Helper: run orchestrator in PR mode, capture step contexts."""
        captured_contexts = []
        wt = tmp_path / "wt"
        wt.mkdir()

        def capture_step(step_num, _name, context, **_kw):  # noqa: ANN001
            captured_contexts.append(dict(context))
            if step_num == 7:
                output = ALL_ISSUES_FIXED
            elif step_num == 5:
                # PR + no-fix path now applies the Step 5 logical-status
                # contract; mock must include a valid failure_signal block.
                output = (
                    "All tests passed.\n"
                    "```failure_signal\n"
                    "status: pass\n"
                    "exit_code: 0\n"
                    "failing_ids: none\n"
                    "artifact_path: none\n"
                    "output: All tests passed.\n"
                    "```\n"
                )
            else:
                output = f"out-{step_num}"
            return (True, output, 0.0, "fake")

        def fake_format(*_args, **_kwargs):
            format_call_count.append(1)
            return "Base: main\n- M: pdd/example.py"

        # Stable PR head metadata for both the entry capture and the
        # post-Step-7 no-fix freshness refetch (issue #1116). Without
        # this mock the orchestrator's gh-CLI call would fail in the
        # test sandbox, leaving current_pr_head_sha empty and
        # triggering the unverified-freshness fail-closed downgrade.
        stable_metadata = {
            "clone_url": "https://github.com/o/r.git",
            "head_ref": "change/test",
            "head_owner": "o",
            "head_repo": "r",
            "head_sha": "deadbeef00000001",
        }
        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._format_pr_changed_files_for_prompt",
            side_effect=fake_format,
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=capture_step,
        ), patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value=stable_metadata,
        ), patch("pdd.agentic_checkup_orchestrator.clear_workflow_state"):
            success, _msg, _cost, _model = run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                verbose=False,
                quiet=True,
                no_fix=True,
                timeout_adder=0.0,
                use_github_state=False,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
                test_scope=test_scope,
            )

        assert success is True
        assert captured_contexts
        return captured_contexts

    def test_pr_mode_targeted_scope_includes_changed_files(self, tmp_path):
        """Opt-in targeted scope passes changed-file summary into step prompts."""
        format_calls: list = []
        captured = self._run_orchestrator_capturing_context(
            tmp_path,
            test_scope="targeted",
            format_call_count=format_calls,
        )
        assert format_calls, "formatter should be invoked under targeted scope"
        assert captured[0]["pr_test_scope"] == "targeted"
        assert captured[0]["pr_changed_files"] == (
            "Base: main\n- M: pdd/example.py"
        )

    def test_pr_mode_full_scope_skips_changed_files(self, tmp_path):
        """Default 'full' scope keeps the test-selection placeholder empty.

        ``pr_changed_files`` is a Step-5 test-selection signal that must
        remain empty in full mode so the agent runs the entire suite. The
        formatter still runs to populate ``pr_scope_changed_files``
        (Step 6 fixer scope, codex round-4 Finding 2) but the targeted
        placeholder stays empty.
        """
        format_calls: list = []
        captured = self._run_orchestrator_capturing_context(
            tmp_path,
            test_scope="full",
            format_call_count=format_calls,
        )
        assert captured[0]["pr_test_scope"] == "full"
        assert captured[0]["pr_changed_files"] == ""
        # Codex round-4 Finding 2: fixer-scope placeholder is populated
        # regardless of test_scope.
        assert captured[0]["pr_scope_changed_files"] == (
            "Base: main\n- M: pdd/example.py"
        )
        # Formatter is invoked exactly once (to populate the scope
        # placeholder); the targeted branch must not call it a second
        # time on the same setup.
        assert format_calls == [1], (
            "formatter should run once to populate pr_scope_changed_files "
            "and never again on a single PR-mode setup"
        )

    def test_pr_mode_full_scope_step6_prompt_renders_scope_list(self, tmp_path):
        """Codex round-4 Finding 2: under default full scope, the Step 6
        prompt context still carries the authoritative PR scope list.

        Regression: ``pr_scope_changed_files`` must be non-empty in PR
        mode regardless of ``test_scope`` so the prompt's scope guard has
        an authoritative list to constrain the fixer against.
        """
        format_calls: list = []
        captured = self._run_orchestrator_capturing_context(
            tmp_path,
            test_scope="full",
            format_call_count=format_calls,
        )
        # Every step context must carry the populated scope list — the
        # Step 6 prompt depends on it being non-empty in PR mode.
        for ctx in captured:
            assert ctx.get("pr_scope_changed_files", "").startswith("Base:"), (
                "pr_scope_changed_files must be populated for every step "
                "context in PR mode, including the default full scope"
            )

    def test_orchestrator_rejects_invalid_test_scope(self, tmp_path):
        """Invalid test_scope must fail loudly, not silently fall back."""
        with pytest.raises(ValueError, match="test_scope"):
            run_agentic_checkup_orchestrator(
                issue_url="https://github.com/o/r/issues/99",
                issue_content="stub",
                repo_owner="o",
                repo_name="r",
                issue_number=99,
                issue_title="stub",
                architecture_json="{}",
                pddrc_content="",
                cwd=tmp_path,
                quiet=True,
                pr_url="https://github.com/o/r/pull/200",
                pr_owner="o",
                pr_repo="r",
                pr_number=200,
                test_scope="quick",
            )

    def test_changed_files_passed_to_step_8(self, mock_dependencies, default_args):
        """Changed files from step 6 should be available to step 8 as files_to_stage."""
        mock_run, mock_load, _, _ = mock_dependencies

        def side_effect_run(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step6" in label:
                return (True, "FILES_CREATED: src/fix.py\nFILES_MODIFIED: src/main.py", 0.1, "gpt-4")
            if "step7" in label:
                return (True, ALL_ISSUES_FIXED, 0.1, "gpt-4")
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
                return (True, ALL_ISSUES_FIXED, 0.1, "gpt-4")
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
            return (True, f"Output for {label}. {ALL_ISSUES_FIXED}", 0.1, "gpt-4")

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
                return (True, ALL_ISSUES_FIXED, 0.1, "gpt-4")
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

        mock_run.side_effect = None
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
            return (True, f"Output for {label}. {ALL_ISSUES_FIXED}", 0.1, "gpt-4")

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
            return (True, f"ok. {ALL_ISSUES_FIXED}", 0.1, "gpt-4")

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
            return (True, f"Output for {kwargs.get('label', '')}. {ALL_ISSUES_FIXED}", 0.1, "gpt-4")

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
            return (True, f"Output for {label}. {ALL_ISSUES_FIXED}", 0.1, "gpt-4")

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
            return (True, f"Output for {label}. {ALL_ISSUES_FIXED}", 0.1, "gpt-4")

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

        mock_run.side_effect = None
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
            return (True, f"Output for {label}. {ALL_ISSUES_FIXED}", 0.1, "gpt-4")

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
        """preprocess should be called with double_curly_brackets=True and exclude."""
        mock_run, mock_load, _, _ = mock_dependencies
        mock_load.return_value = "Template for {issue_url}"

        with patch("pdd.agentic_checkup_orchestrator.preprocess") as mock_preprocess:
            mock_preprocess.return_value = "Template for {issue_url}"

            run_agentic_checkup_orchestrator(**default_args)

            # Verify preprocess was called
            assert mock_preprocess.called

            call_kwargs = mock_preprocess.call_args[1]
            assert call_kwargs.get("double_curly_brackets") is True
            assert "issue_url" in call_kwargs.get("exclude", [])
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
                return (True, ALL_ISSUES_FIXED, 0.1, "gpt-4")
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
                return (True, ALL_ISSUES_FIXED, 0.1, "gpt-4")
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
        """Step 7 never returns clean -> 3 iterations, then fail closed."""
        mock_run, _, _, mock_console = mock_dependencies

        def side_effect(*args, **kwargs):
            label = kwargs.get("label", "")
            if "step7" in label:
                return (True, "Issues remain: 1 test failing", 0.1, "gpt-4")
            return (True, f"Output for {label}", 0.1, "gpt-4")

        mock_run.side_effect = side_effect
        default_args["quiet"] = False

        success, msg, cost, model = run_agentic_checkup_orchestrator(**default_args)

        assert success is False
        assert "did not verify all issues fixed" in msg.lower()
        # 2 (steps 1-2) + 3*7 (3 iterations), then no step 8.
        assert mock_run.call_count == 23

        called_labels = [c.kwargs["label"] for c in mock_run.call_args_list]
        assert "step3_iter3" in called_labels
        assert "step7_iter3" in called_labels
        assert "step8" not in called_labels

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
                return (True, ALL_ISSUES_FIXED, 0.1, "gpt-4")
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
                return (True, ALL_ISSUES_FIXED, 0.1, "gpt-4")
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


# ---------------------------------------------------------------------------
# Trusted step-comment wiring
# ---------------------------------------------------------------------------


class TestTrustedStepCommentPosting:
    """The checkup orchestrator must extract <step_report> from each successful
    step's output and post via post_step_comment_once with a composite-key
    encoding (fractional 6.1/6.2/6.3 and iterated fix-verify loop)."""

    def test_success_path_posts_step_comment_once(self, mock_dependencies, default_args):
        mock_run, _, _, _ = mock_dependencies
        mock_run.return_value = (
            True,
            f"<step_report>step report body</step_report>\n{ALL_ISSUES_FIXED}",
            0.1,
            "gpt-4",
        )

        with patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment_once",
            return_value=True,
        ) as mock_post_once:
            success, _, _, _ = run_agentic_checkup_orchestrator(**default_args)

        assert success is True
        assert mock_post_once.call_count >= 1
        for c in mock_post_once.call_args_list:
            assert "step_num" in c.kwargs
            assert isinstance(c.kwargs["step_num"], int)
            assert "posted_steps" in c.kwargs

    def test_step_report_missing_posts_fallback_comment(
        self, mock_dependencies, default_args
    ):
        mock_run, _, _, _ = mock_dependencies
        mock_run.return_value = (True, f"Step output. {ALL_ISSUES_FIXED}", 0.1, "gpt-4")

        with patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment_once",
            return_value=True,
        ) as mock_post_once:
            success, _, _, _ = run_agentic_checkup_orchestrator(**default_args)

        assert success is True
        assert mock_post_once.call_count >= 1
        assert any(
            "no `<step_report>` block returned by agent" in c.kwargs["body"]
            and "Raw output retained in workflow state" in c.kwargs["body"]
            for c in mock_post_once.call_args_list
        )

    def test_post_exception_does_not_break_run(self, mock_dependencies, default_args):
        mock_run, _, _, _ = mock_dependencies
        mock_run.return_value = (
            True,
            f"<step_report>some report</step_report>\n{ALL_ISSUES_FIXED}",
            0.1,
            "gpt-4",
        )

        with patch(
            "pdd.agentic_checkup_orchestrator.post_step_comment_once",
            side_effect=RuntimeError("simulated gh failure"),
        ):
            success, _, _, _ = run_agentic_checkup_orchestrator(**default_args)

        assert success is True


class TestRefreshPrBaseRefTimeout:
    """Iter-20 Finding 3: the base-ref fetch MUST be bounded so a
    stalled transport (auth prompt, dead remote, transient hang)
    cannot hold the review loop forever. The deterministic-gate
    layer's own ``gate_timeout`` does NOT apply to this subprocess
    because the fetch runs BEFORE gate discovery.
    """

    def test_passes_timeout_to_subprocess_run(self, tmp_path):
        import subprocess as sp
        from pdd.agentic_checkup_orchestrator import _refresh_pr_base_ref

        sp.run(["git", "init", "-q"], cwd=tmp_path, check=True)
        recorded = {}

        def fake_run(args, **kwargs):
            recorded["args"] = args
            recorded["kwargs"] = kwargs
            return sp.CompletedProcess(args, 0, b"", b"")

        with patch(
            "pdd.agentic_checkup_orchestrator._get_git_root",
            return_value=tmp_path,
        ), patch(
            "pdd.agentic_checkup_orchestrator._resolve_pr_remote",
            return_value="https://github.com/o/r.git",
        ), patch(
            "pdd.agentic_checkup_orchestrator.subprocess.run",
            side_effect=fake_run,
        ):
            md = {"base_ref": "release-1.4"}
            _refresh_pr_base_ref(tmp_path, "o", "r", 1, md, quiet=True)

        assert "timeout" in recorded["kwargs"], (
            "subprocess.run MUST be called with a timeout kwarg so a stalled "
            "fetch cannot hang the review loop"
        )
        assert recorded["kwargs"]["timeout"] > 0
        assert md.get("base_local_ref") == "refs/remotes/pdd-checkup/pr-1/base"

    def test_timeout_expired_populates_base_ref_fetch_error(self, tmp_path):
        import subprocess as sp
        from pdd.agentic_checkup_orchestrator import _refresh_pr_base_ref

        sp.run(["git", "init", "-q"], cwd=tmp_path, check=True)

        def fake_run(args, **kwargs):
            raise sp.TimeoutExpired(cmd=args, timeout=60)

        with patch(
            "pdd.agentic_checkup_orchestrator._get_git_root",
            return_value=tmp_path,
        ), patch(
            "pdd.agentic_checkup_orchestrator._resolve_pr_remote",
            return_value="https://github.com/o/r.git",
        ), patch(
            "pdd.agentic_checkup_orchestrator.subprocess.run",
            side_effect=fake_run,
        ):
            md = {"base_ref": "release-1.4"}
            _refresh_pr_base_ref(tmp_path, "o", "r", 1, md, quiet=True)

        # MUST be caught and surfaced as base_ref_fetch_error so the
        # review-loop's iter-19 fail-closed path kicks in. MUST NOT
        # leak as an unhandled TimeoutExpired exception.
        assert "base_ref_fetch_error" in md
        assert "timed out" in md["base_ref_fetch_error"].lower()
        assert "base_local_ref" not in md

    def test_called_process_error_scrubs_secrets_from_stderr(self, tmp_path):
        """``_refresh_pr_base_ref`` MUST
        route the failed-fetch stderr through ``_scrub_secrets`` (regex
        catch-all) BEFORE storing it on ``pr_metadata`` or printing it
        to the console. Env-token redaction alone misses credentials
        supplied by the git credential helper, GitHub App installation
        tokens minted at runtime, embedded ``https://<user>:<token>@host``
        basic-auth, and verbose-transport ``Bearer`` headers. The
        console.print output and ``pr_metadata["base_ref_fetch_error"]``
        both flow into long-term log capture and the rendered checkup
        report — they are public surfaces.
        """
        import subprocess as sp
        from pdd.agentic_checkup_orchestrator import _refresh_pr_base_ref

        sp.run(["git", "init", "-q"], cwd=tmp_path, check=True)

        # stderr carrying a GitHub App installation token (`ghs_…`)
        # that is NOT in process env — would slip past the env-token
        # redaction unless the regex scrub runs.
        leaky_stderr = (
            "remote: Invalid username or token. "
            "Token ghs_ABCDEFGHIJKLMNOPQRSTUVWXYZ012345 has expired\n"
            "fatal: Authentication failed for "
            "'https://x-access-token:ghp_AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA@github.com/o/r.git/'\n"
        )

        def fake_run(args, **kwargs):
            raise sp.CalledProcessError(
                returncode=128, cmd=args, output="", stderr=leaky_stderr
            )

        with patch(
            "pdd.agentic_checkup_orchestrator._get_git_root",
            return_value=tmp_path,
        ), patch(
            "pdd.agentic_checkup_orchestrator._resolve_pr_remote",
            return_value="upstream",
        ), patch(
            "pdd.agentic_checkup_orchestrator._github_token_from_env",
            return_value="",
        ), patch(
            "pdd.agentic_checkup_orchestrator.subprocess.run",
            side_effect=fake_run,
        ):
            md = {"base_ref": "main"}
            _refresh_pr_base_ref(tmp_path, "o", "r", 1, md, quiet=True)

        stored = md["base_ref_fetch_error"]
        # Both token shapes MUST be redacted even though the env is empty.
        assert "ghs_ABCDEFGHIJKLMNOPQRSTUVWXYZ012345" not in stored
        assert "ghp_AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA" not in stored
        assert "[REDACTED]" in stored
        # Surrounding context (the operator-useful diagnostic) survives.
        assert "Authentication failed" in stored or "expired" in stored.lower()

    def test_called_process_error_scrubs_generic_url_userinfo(self, tmp_path):
        """Generic ``scheme://user:password@host`` basic-auth credentials
        in git stderr MUST be scrubbed even when the password does not
        match any prefix-anchored token pattern (custom internal token
        shape, runtime-minted App installation token, credential-helper
        PAT). The URL-userinfo regex uses lookbehind/lookahead around
        ``://``…``@`` so the scheme + host stay readable for diagnostics
        while the credential payload is replaced.
        """
        import subprocess as sp
        from pdd.agentic_checkup_orchestrator import _refresh_pr_base_ref

        sp.run(["git", "init", "-q"], cwd=tmp_path, check=True)

        # Generic basic-auth URL whose password is a custom token shape
        # — does NOT start with ghp_/ghs_/sk-/etc., would slip past
        # every other pattern unless URL-userinfo redaction runs.
        leaky_stderr = (
            "fatal: Authentication failed for "
            "'https://x-access-token:customToken123456789@github.com/o/r.git/'\n"
        )

        def fake_run(args, **kwargs):
            raise sp.CalledProcessError(
                returncode=128, cmd=args, output="", stderr=leaky_stderr
            )

        with patch(
            "pdd.agentic_checkup_orchestrator._get_git_root",
            return_value=tmp_path,
        ), patch(
            "pdd.agentic_checkup_orchestrator._resolve_pr_remote",
            return_value="upstream",
        ), patch(
            "pdd.agentic_checkup_orchestrator._github_token_from_env",
            return_value="",
        ), patch(
            "pdd.agentic_checkup_orchestrator.subprocess.run",
            side_effect=fake_run,
        ):
            md = {"base_ref": "main"}
            _refresh_pr_base_ref(tmp_path, "o", "r", 1, md, quiet=True)

        stored = md["base_ref_fetch_error"]
        # The generic-shape credential MUST NOT survive verbatim.
        assert "customToken123456789" not in stored
        assert "x-access-token:customToken123456789" not in stored
        # Scheme + host remain readable so the diagnostic is still useful.
        assert "github.com/o/r.git" in stored
        assert "[REDACTED]" in stored

    def test_refresh_pr_base_ref_uses_trusted_git_under_dot_path(
        self, tmp_path, monkeypatch
    ):
        """Greg PR #1095 review: the base-ref refresh is part of the
        gates-on flow and must not execute a PR-controlled ``./git`` shim
        before gate discovery starts.
        """
        from pdd.agentic_checkup_orchestrator import (
            _pr_base_tracking_ref,
            _refresh_pr_base_ref,
        )

        remote = tmp_path / "remotes" / "o" / "r.git"
        seed = tmp_path / "seed"
        worktree = tmp_path / "worktree"
        subprocess.run(
            ["git", "init", "--bare", "-q", "-b", "main", str(remote)],
            check=True,
        )
        subprocess.run(["git", "init", "-q", "-b", "main", str(seed)], check=True)
        (seed / "README.md").write_text("base\n", encoding="utf-8")
        subprocess.run(["git", "add", "README.md"], cwd=seed, check=True)
        subprocess.run(
            [
                "git",
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@x",
                "commit",
                "-m",
                "base",
                "-q",
            ],
            cwd=seed,
            check=True,
        )
        subprocess.run(["git", "remote", "add", "origin", str(remote)], cwd=seed, check=True)
        subprocess.run(["git", "push", "-q", "origin", "main"], cwd=seed, check=True)
        subprocess.run(["git", "clone", "-q", str(remote), str(worktree)], check=True)

        shim = worktree / "git"
        marker = worktree / "marker"
        shim.write_text(
            "#!/bin/sh\n"
            f"echo shim >> {marker}\n"
            "exit 1\n",
            encoding="utf-8",
        )
        shim.chmod(0o755)
        monkeypatch.setenv("PATH", f".{os.pathsep}{os.environ.get('PATH', '')}")

        md = {"base_ref": "main"}
        _refresh_pr_base_ref(worktree, "o", "r", 1, md, quiet=True)

        assert md.get("base_local_ref") == _pr_base_tracking_ref(1)
        assert "base_ref_fetch_error" not in md
        assert not marker.exists()


# ---------------------------------------------------------------------------
# Issue #1212 — checkup --pr hides test failures, lets fixer push unrelated
# code, never converges.
#
# Bug 1: Step 5 failure detail not surfaced to user (only generic warning logged)
# Bug 2: Step 6 fixer has no scope guard; can create files outside PR changed-file set
# Bug 3: Step 7 verifier non-discriminating; passes without causal-connection check
# Bug 5: Fixer (steps 6.1/6.2/6.3) always runs even when Step 5 is clean
#
# Tests marked FAILS_ON_CURRENT_CODE will fail on buggy code, pass once fixed.
# Tests marked PASSES_ON_CURRENT_CODE guard existing correct behaviour.
# ---------------------------------------------------------------------------


# PR metadata snapshot used by all issue-1212 tests.
_PR_META_1212: Dict[str, str] = {
    "clone_url": "https://github.com/o/r.git",
    "head_ref": "change/fix",
    "head_owner": "o",
    "head_repo": "r",
    "head_sha": "abc123deadbeef",
    "api_changed_files": "- M: pdd/main.py\n- M: tests/test_main.py",
    "api_changed_files_full": "- M: pdd/main.py\n- M: tests/test_main.py",
}

# Minimal PR-mode arguments for run_agentic_checkup_orchestrator.
_PR_ARGS_1212: Dict = {
    "issue_url": "https://github.com/o/r/issues/99",
    "issue_content": "Bug in pdd/main.py causing test failures",
    "repo_owner": "o",
    "repo_name": "r",
    "issue_number": 99,
    "issue_title": "Fix pdd/main.py",
    "architecture_json": "{}",
    "pddrc_content": "",
    "verbose": False,
    "quiet": True,
    "no_fix": False,
    "use_github_state": False,
    "timeout_adder": 0.0,
    "pr_url": "https://github.com/o/r/pull/200",
    "pr_owner": "o",
    "pr_repo": "r",
    "pr_number": 200,
    "test_scope": "targeted",
}


def _pr_patches_1212(
    tmp_path: Path,
    *,
    step_side_effect,
    git_changed_files: Optional[List[str]] = None,
    commit_push_return=(True, "No changes to commit"),
    pr_metadata: Optional[Dict] = None,
) -> tuple:
    """Return a tuple of context-manager patchers for a PR-fix-mode run.

    Usage::

        patches = _pr_patches_1212(tmp_path, step_side_effect=fn)
        with patches[0], patches[1], ...:
            run_agentic_checkup_orchestrator(...)
    """
    wt = tmp_path / "wt"
    wt.mkdir(exist_ok=True)
    meta = pr_metadata if pr_metadata is not None else dict(_PR_META_1212)
    return (
        patch("pdd.agentic_checkup_orchestrator._setup_pr_worktree", return_value=(wt, None)),
        patch("pdd.agentic_checkup_orchestrator._fetch_pr_metadata", return_value=meta),
        patch("pdd.agentic_checkup_orchestrator._run_single_step", side_effect=step_side_effect),
        patch("pdd.agentic_checkup_orchestrator._git_changed_files",
              return_value=git_changed_files or []),
        patch("pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
              return_value=commit_push_return),
        patch("pdd.agentic_checkup_orchestrator.load_workflow_state", return_value=(None, None)),
        patch("pdd.agentic_checkup_orchestrator.save_workflow_state", return_value=None),
        patch("pdd.agentic_checkup_orchestrator.clear_workflow_state"),
        patch("pdd.agentic_checkup_orchestrator._check_architecture_registry_edit_guard",
              return_value=None),
        patch("pdd.agentic_checkup_orchestrator._check_prompt_source_guard", return_value=None),
        patch("pdd.agentic_checkup_orchestrator.console"),
    )


class TestTargetedPrStep7Exit:
    """Targeted PR mode can exit on the structured Step 7 verdict."""

    def test_structured_targeted_pass_exits_without_legacy_marker(self, tmp_path):
        labels: List[str] = []
        targeted_step7_pass = (
            "## Step 7/8: Verification & Final Report\n"
            "Targeted verification passed; full suite not run here.\n"
            "```json\n"
            '{"success": true, '
            '"message": "Verification scope: targeted — full suite not run. '
            'Project-wide build issues remain but are outside PR scope.", '
            '"issue_aligned": true, '
            '"issues": [{"severity": "critical", "fixed": false, '
            '"description": "tsc fails because src is missing", '
            '"module": "frontend", "file": "frontend/", '
            '"scope": "out-of-scope", '
            '"out_of_scope_reason": "pre-existing project-wide build failure outside this docs PR"}], '
            '"changed_files": ["docs/checkup.md"]}\n'
            "```"
        )

        def step_side_effect(step_num, name, context, **kwargs):
            labels.append(kwargs.get("label", ""))
            if step_num == 5:
                return (True, STEP5_CLEAN_OUTPUT, 0.1, "model")
            if step_num == 7:
                return (True, targeted_step7_pass, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(tmp_path, step_side_effect=step_side_effect)
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        assert success is True, msg
        assert "step7_iter1" in labels
        assert "step3_iter2" not in labels

    def test_structured_targeted_pass_on_final_iteration_does_not_fail_max(
        self, tmp_path
    ):
        labels: List[str] = []
        targeted_step7_pass = (
            "## Step 7/8: Verification & Final Report\n"
            "Targeted verification passed; full suite not run here.\n"
            "```json\n"
            '{"success": true, '
            '"message": "Verification scope: targeted — full suite not run.", '
            '"issue_aligned": true, '
            '"issues": [], '
            '"changed_files": ["docs/checkup.md"]}\n'
            "```"
        )

        def step_side_effect(step_num, name, context, **kwargs):
            label = kwargs.get("label", "")
            labels.append(label)
            if step_num == 5:
                return (True, STEP5_CLEAN_OUTPUT, 0.1, "model")
            if step_num == 7 and label == "step7_iter3":
                return (True, targeted_step7_pass, 0.1, "model")
            if step_num == 7:
                return (True, "Issues remain", 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(tmp_path, step_side_effect=step_side_effect)
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        assert success is True, msg
        assert "did not verify all issues fixed" not in msg.lower()
        assert "step7_iter3" in labels


class TestIssue1212Bug1Step5FailureSignalPropagation:
    """Bug 1: Step 5 failure output must flow to Step 6's context and user-visible logs."""

    def test_step5_failure_output_in_step6_context(self, tmp_path):
        """Step 5 failure text is stored in context and passed to Step 6's prompt.

        PASSES_ON_CURRENT_CODE: context["step5_output"] is correctly set to the raw
        step-5 output, so Step 6 receives it. This test guards against regression.
        """
        step5_failure_text = "FAILED: test_foo.py::test_bar - AssertionError: got None"
        captured_step6_contexts: List[Dict] = []

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, step5_failure_text, 0.1, "model")
            if step_num == 6.1:
                captured_step6_contexts.append(dict(context))
                return (True, "FILES_MODIFIED: pdd/main.py", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(tmp_path, step_side_effect=step_side_effect)
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        assert captured_step6_contexts, "Step 6.1 must be invoked after Step 5 failure"
        ctx = captured_step6_contexts[0]
        assert "step5_output" in ctx
        # The mock text already begins with "FAILED:" to simulate a failure description.
        assert "FAILED:" in ctx["step5_output"]
        assert "test_foo.py" in ctx["step5_output"]

    def test_step5_failure_logged_visibly_not_only_as_warning(self, tmp_path):
        """When Step 5 fails, its actual failure content must be printed to the console.

        FAILS_ON_CURRENT_CODE: The orchestrator prints only a generic yellow warning;
        the actual pytest failure detail (test IDs, FAILED lines) is never shown.
        """
        step5_failure_text = (
            "FAILED tests/test_main.py::test_critical_path - AssertionError\n"
            "short test summary info\n"
            "FAILED tests/test_main.py::test_critical_path"
        )

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, step5_failure_text, 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(tmp_path, step_side_effect=step_side_effect)
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], \
             patches[10] as mc:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        all_printed = " ".join(
            str(arg) for call_obj in mc.print.call_args_list for arg in call_obj.args
        )
        # Actual failure content (test IDs, FAILED lines) must appear in the log.
        # On current code only the generic warning is printed — this assertion FAILS.
        assert "test_critical_path" in all_printed or "FAILED tests" in all_printed, (
            "Step 5 failure detail must be printed to the console so operators can see "
            "what failed. Currently only a generic warning is shown."
        )


class TestIssue1212Bug2FixerScopeGuard:
    """Bug 2: Step 6 fixer must be constrained to the PR's existing changed-file set."""

    def test_fixer_out_of_scope_files_rejected_before_push(self, tmp_path):
        """Fixer files outside the PR's changed-file set must be rejected before push.

        FAILS_ON_CURRENT_CODE: No scope guard compares _git_changed_files() against
        pr_metadata["api_changed_files"]. The fixer can create 6866 lines of unrelated
        plugin code and it gets pushed.

        Acceptance criterion from issue #1212:
          "A test asserts that a Step 6 fixer producing files outside the PR's existing
          changed-file set is rejected (or routed through an explicit expansion path)
          before commit."
        """
        out_of_scope_files = [
            "plugins/security-guidance/README.md",
            "plugins/security-guidance/rules/xss.yaml",
            "plugins/security-guidance/rules/sqli.yaml",
        ]

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=out_of_scope_files,
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        # Must NOT push when out-of-scope files were added (no scope guard on current code).
        push_mock.assert_not_called()
        assert success is False

    def test_fixer_scope_guard_allows_in_scope_files(self, tmp_path):
        """Fixer changes that stay within the PR's changed-file set are allowed.

        PASSES_ON_CURRENT_CODE (positive case): fixer only modifies files already in
        api_changed_files — push should proceed normally.
        """
        in_scope_files = ["pdd/main.py", "tests/test_main.py"]

        def step_side_effect(step_num, name, context, **kwargs):
            # Make Step 5 fail so Step 6.x runs and the worktree changes
            # are attributable to the fixer instead of clean-run side
            # effects.
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=in_scope_files,
            commit_push_return=(True, "Pushed 2 files to PR branch"),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        push_mock.assert_called_once()


class TestIssue1212Bug3Step7NonDiscriminatingVerifier:
    """Bug 3: Step 7 must verify causal connection between fixer diff and Step 5 failure."""

    def test_step7_context_contains_step5_failure_and_fixer_files(self, tmp_path):
        """Step 7 context includes both Step 5 failure output and fixer changed files.

        PASSES_ON_CURRENT_CODE: plumbing is already correct — this test guards regression.
        """
        step5_failure = "FAILED pdd/main.py::test_import - ImportError: cannot import name 'foo'"
        captured_step7_contexts: List[Dict] = []

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, step5_failure, 0.1, "model")
            if step_num == 6.1:
                return (True, "FILES_MODIFIED: pdd/main.py", 0.1, "model")
            if step_num == 7:
                captured_step7_contexts.append(dict(context))
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        assert captured_step7_contexts, "Step 7 must be invoked"
        ctx = captured_step7_contexts[0]
        assert "step5_output" in ctx
        assert "pdd/main.py" in ctx["step5_output"]
        assert "test_import" in ctx["step5_output"]
        assert "pdd/main.py" in ctx.get("files_to_stage", "")

    def test_orchestrator_allows_push_when_fixer_diff_unrelated_to_step5_failure(
        self, tmp_path
    ):
        """Orchestrator must block push when fixer diff has no overlap with Step 5 failure paths.

        FAILS_ON_CURRENT_CODE: No causal-connection gate exists. When the fixer touches
        only files unrelated to the Step 5 failure paths, the push proceeds anyway —
        this is how 6866 lines of unrelated plugin code reached PR #1210.

        Acceptance criterion from issue #1212:
          "A test asserts that Step 7 fails the run if the fixer diff does not touch any
          file related to the Step 5 failure signal."
        """
        step5_failure = (
            "FAILED pdd/main.py::test_critical_path - AssertionError\n"
            "FAILED pdd/main.py::test_edge_case - AttributeError"
        )
        unrelated_fixer_files = ["plugins/security-guidance/README.md"]

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, step5_failure, 0.1, "model")
            if step_num == 6.1:
                return (True, "FILES_CREATED: plugins/security-guidance/README.md", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=unrelated_fixer_files,
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        # Must NOT push when fixer files have zero overlap with Step 5 failure paths.
        push_mock.assert_not_called()
        assert success is False


class TestIssue1212Bug5CleanRunConvergence:
    """Bug 5: Clean runs must produce zero commits so the loop has a stable finish line."""

    def test_clean_step5_skips_fixer_steps(self, tmp_path):
        """When Step 5 reports no failures (success=True), Steps 6.1/6.2/6.3 must be skipped.

        FAILS_ON_CURRENT_CODE: The fix-verify loop runs all steps including fixer steps
        regardless of Step 5's outcome. With no concrete failure to fix, the fixer
        hallucinates changes and the loop cannot converge.
        """
        invoked_steps: List = []

        def step_side_effect(step_num, name, context, **kwargs):
            invoked_steps.append(step_num)
            if step_num == 5:
                return (True, STEP5_CLEAN_OUTPUT, 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(tmp_path, step_side_effect=step_side_effect)
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        fixer_steps_invoked = [s for s in invoked_steps if s in (6.1, 6.2, 6.3)]
        assert not fixer_steps_invoked, (
            f"Fixer steps {fixer_steps_invoked} were invoked despite Step 5 reporting "
            "no failures. When Step 5 is clean the fixer steps must be skipped."
        )

    def test_clean_run_produces_no_commit_or_push(self, tmp_path):
        """A clean checkup run with no worktree changes must produce zero push calls.

        FAILS_ON_CURRENT_CODE: _commit_and_push_if_changed is called unconditionally
        after Step 7 passes, making it impossible to reach a stable no-op state.
        """
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (True, "All tests passed, no failures.", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=[],
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        push_mock.assert_not_called()

    def test_repeated_clean_runs_stay_stable(self, tmp_path):
        """Two consecutive clean runs each produce zero push calls (convergence).

        FAILS_ON_CURRENT_CODE: Each run finds something to push because the fixer always
        runs and the push gate has no stable success condition.
        """
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (True, "All tests passed, 0 failed.", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        push_call_counts: List[int] = []
        for run_num in range(2):
            run_dir = tmp_path / f"run{run_num}"
            run_dir.mkdir()
            patches = _pr_patches_1212(
                run_dir,
                step_side_effect=step_side_effect,
                git_changed_files=[],
            )
            with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
                 patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
                run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": run_dir})
            push_call_counts.append(push_mock.call_count)

        assert push_call_counts == [0, 0], (
            f"Expected [0, 0] push calls across two clean runs, got {push_call_counts}. "
            "Clean runs must be idempotent — each must produce zero commits."
        )

    def test_clean_run_flows_through_finalization(self, tmp_path):
        """Clean PR run must clear workflow state and reach Checkpoint D.

        Regression for codex round-1 critical finding at line 2534: the no-
        change branch used to return early before `clear_workflow_state`
        and before the Checkpoint D PR-head freshness check, leaving stale
        `.pdd/checkup-state/checkup_state_{N}.json` behind and publishing
        a clean verdict without the final freshness lease.
        """
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (True, "All tests passed.", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=[],
        )
        # patches[7] is clear_workflow_state.
        with patches[0], patches[1] as fetch_mock, patches[2], patches[3], \
             patches[4] as push_mock, patches[5], patches[6], \
             patches[7] as clear_mock, patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_not_called()
        assert success is True, msg
        # clear_workflow_state must be called on the clean-run path so the
        # checkup-state JSON does not linger.
        assert clear_mock.called, (
            "Clean PR run must route through clear_workflow_state, but "
            "the no-change branch returned before final cleanup."
        )
        # Checkpoint D refetches PR metadata — the fetch must have run
        # AFTER the entry fetch (≥ 2 invocations) on the clean-run path.
        assert fetch_mock.call_count >= 2, (
            "Clean PR run skipped Checkpoint D's PR-head freshness check "
            f"(saw only {fetch_mock.call_count} _fetch_pr_metadata calls)."
        )


# ---------------------------------------------------------------------------
# Codex round-1 regression coverage — issue #1215 PR loop
#
# Finding 1: scope guard must parse the REAL `_format_pr_api_changed_files`
# row shapes (MODIFIED / ADDED / RENAMED `old -> new` / etc.), not the
# hand-rolled `- M:` shorthand the older tests used.
# Finding 2: causal-connection check must allow a `tests/test_x.py` failure
# to be fixed by editing the corresponding `pdd/x.py` source file when the
# source file is also part of the PR.
# ---------------------------------------------------------------------------


_PR_META_REAL_API: Dict[str, str] = {
    **_PR_META_1212,
    # Real `gh api pulls/{n}/files` rows formatted by
    # `_format_pr_api_changed_files`.
    "api_changed_files": (
        "- MODIFIED: pdd/main.py\n"
        "- ADDED: pdd/new_feature.py\n"
        "- RENAMED: old/legacy.py -> pdd/renamed.py\n"
        "- DELETED: pdd/removed.py\n"
        "- NOTE: GitHub PR files API list truncated; showing 4 of 99 files."
    ),
    "api_changed_files_full": (
        "- MODIFIED: pdd/main.py\n"
        "- ADDED: pdd/new_feature.py\n"
        "- RENAMED: old/legacy.py -> pdd/renamed.py\n"
        "- DELETED: pdd/removed.py"
    ),
}


class TestIssue1215ScopeGuardRealApiFormat:
    """Finding 1: scope guard must parse real API row shapes."""

    def test_modified_row_is_in_scope(self, tmp_path):
        """A fixer touching a `- MODIFIED:` path is in scope and pushes."""
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            commit_push_return=(True, "Pushed 1 file"),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        push_mock.assert_called_once()

    def test_added_row_is_in_scope(self, tmp_path):
        """A fixer touching a `- ADDED:` path is in scope and pushes."""
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/new_feature.py"],
            commit_push_return=(True, "Pushed 1 file"),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        push_mock.assert_called_once()

    def test_renamed_row_both_sides_in_scope(self, tmp_path):
        """A fixer touching either side of a `- RENAMED: old -> new` row is in scope."""
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        # Touch the NEW path (the post-rename location).
        new_side = tmp_path / "new-side"
        new_side.mkdir()
        patches = _pr_patches_1212(
            new_side,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/renamed.py"],
            commit_push_return=(True, "Pushed"),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": new_side})
        push_mock.assert_called_once()

        # Touch the OLD path (the pre-rename location).
        old_side = tmp_path / "old-side"
        old_side.mkdir()
        patches = _pr_patches_1212(
            old_side,
            step_side_effect=step_side_effect,
            git_changed_files=["old/legacy.py"],
            commit_push_return=(True, "Pushed"),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": old_side})
        push_mock.assert_called_once()

    def test_file_outside_real_api_rows_blocked(self, tmp_path):
        """A fixer file absent from MODIFIED/ADDED/RENAMED/DELETED rows is rejected."""
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["plugins/unrelated/README.md"],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, _, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_not_called()
        assert success is False


class TestIssue1215CausalConnectionRealisticPytest:
    """Finding 2: a `tests/test_main.py` failure fixed by `pdd/main.py` must be allowed."""

    def test_test_file_failure_with_source_fix_allowed(self, tmp_path):
        """Realistic causal pattern: tests fail, source-file fix lands.

        Step 5 surfaces a failing `tests/test_main.py::test_x`, fixer edits
        `pdd/main.py` (which IS in the PR's changed-file set). The
        causal-connection guard must NOT refuse this push — the previous
        narrow check rejected it because the changed file did not appear
        in the Step 5 failure paths directly.
        """
        step5_failure = (
            "FAILED: pytest run\n"
            "============ FAILURES ============\n"
            "_____ tests/test_main.py::test_critical_path _____\n"
            "AssertionError: expected foo, got bar\n"
            "short test summary info:\n"
            "FAILED tests/test_main.py::test_critical_path"
        )

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, step5_failure, 0.1, "model")
            if step_num == 6.1:
                return (True, "FILES_MODIFIED: pdd/main.py", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            commit_push_return=(True, "Pushed pdd/main.py to PR branch"),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        push_mock.assert_called_once(), (
            "Causal-connection guard wrongly rejected a tests/test_main.py "
            "failure fixed by editing pdd/main.py (which IS in the PR)."
        )

    def test_unrelated_fixer_still_blocked(self, tmp_path):
        """Causal guard still blocks fixer files that overlap neither PR nor failure."""
        step5_failure = (
            "FAILED: pytest run\n"
            "FAILED tests/test_main.py::test_x - AssertionError"
        )

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, step5_failure, 0.1, "model")
            if step_num == 6.1:
                return (True, "FILES_CREATED: plugins/unrelated/x.py", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["plugins/unrelated/x.py"],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, _, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_not_called()
        assert success is False


# ---------------------------------------------------------------------------
# Codex round-2 regression coverage — PR #1215
#
# Findings:
#   1. Scope guard must filter the orchestrator's own ``.pdd/`` artifacts
#      from `_git_changed_files` output and read PR file list from
#      `api_changed_files_full` when present (the bounded preview rejected
#      large PRs).
#   2. EXPANSION_ITEMS must be a structured, justified allowlist — a blank
#      or paraphrased marker cannot disable the scope refusal for every
#      out-of-scope file.
#   3. Resuming a clean PR run mid-loop must NOT re-enter the fixer just
#      because the in-memory clean flags are False.
#   4. Step 5 failure output must be scrubbed BEFORE every persisted
#      surface (context, step_outputs, GitHub comments), not only console.
#   5. The ```failure_signal``` block from Step 5 must be parsed and
#      validated; Step 6 must receive a normalised structured block even
#      when Step 5 omits or paraphrases it.
# ---------------------------------------------------------------------------


class TestIssue1215Round2ScopeGuardArtifactFiltering:
    """Round-2 Finding 1: filter non-committable PDD artifacts and use the full API list."""

    def test_pdd_artifact_does_not_poison_clean_run(self, tmp_path):
        """A clean run with only a ``.pdd/checkup-context/...`` artifact reaches finalization."""
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=[".pdd/checkup-context/pr-changed-files-api.txt"],
            commit_push_return=(True, "No changes to push."),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_not_called()
        assert "scope-guard" not in (msg or "").lower(), (
            "Scope guard wrongly rejected the orchestrator's own .pdd artifact."
        )

    def test_large_pr_uses_api_changed_files_full(self, tmp_path):
        """A file beyond the preview but present in api_changed_files_full is in scope."""
        pr_meta = dict(_PR_META_REAL_API)
        pr_meta["api_changed_files"] = (
            "- MODIFIED: pdd/main.py\n"
            "- NOTE: GitHub PR files API list truncated; showing 1 of 250 files."
        )
        pr_meta["api_changed_files_full"] = (
            "- MODIFIED: pdd/main.py\n"
            "- MODIFIED: pdd/deep/nested_module.py"
        )

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/deep/nested_module.py"],
            commit_push_return=(True, "Pushed 1 file"),
            pr_metadata=pr_meta,
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        push_mock.assert_called_once()


class TestIssue1215Round2ExpansionItemsStructured:
    """Round-2 Finding 2: EXPANSION_ITEMS must be structured and justified."""

    def test_parse_expansion_items_blank_marker_invalid(self):
        paths, justified_paths = _parse_expansion_items(
            "Some preamble.\nEXPANSION_ITEMS:\nMore notes.\n"
        )
        assert paths == set()
        assert justified_paths == set()

    def test_parse_expansion_items_none_payload_invalid(self):
        paths, justified_paths = _parse_expansion_items(
            "EXPANSION_ITEMS: none\n"
        )
        assert paths == set()
        assert justified_paths == set()

    def test_parse_expansion_items_paths_no_justification(self):
        paths, justified_paths = _parse_expansion_items(
            "EXPANSION_ITEMS: tests/test_other.py, pdd/utils/helper.py\n"
            "FILES_MODIFIED: pdd/main.py\n"
        )
        assert paths == {"tests/test_other.py", "pdd/utils/helper.py"}
        assert justified_paths == set()

    def test_parse_expansion_items_with_inline_justification(self):
        paths, justified_paths = _parse_expansion_items(
            "EXPANSION_ITEMS: tests/test_other.py — test imports helper.py "
            "which the PR change to core.py broke\n"
        )
        assert paths == {"tests/test_other.py"}
        assert justified_paths == {"tests/test_other.py"}

    def test_blank_expansion_items_does_not_bypass_scope_guard(self, tmp_path):
        """A bare ``EXPANSION_ITEMS:`` marker no longer disables the scope refusal."""
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                # Step 5 must fail so the fixer runs — otherwise the
                # round-3 clean-run side-effect guard fires first and the
                # scope guard never gets a chance.
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 6.1:
                return (
                    True,
                    "FILES_MODIFIED: plugins/unrelated/x.py\n"
                    "EXPANSION_ITEMS:\n",
                    0.1,
                    "model",
                )
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["plugins/unrelated/x.py"],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success_blank, msg_blank, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_not_called()
        assert success_blank is False
        assert "scope guard" in (msg_blank or "").lower()

    def test_mismatched_expansion_items_still_refuses_uncovered_files(self, tmp_path):
        """An EXPANSION_ITEMS listing path A does NOT authorise touching path B."""
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 6.1:
                return (
                    True,
                    "FILES_MODIFIED: plugins/uncovered/y.py\n"
                    "EXPANSION_ITEMS: plugins/covered/x.py — test imports y.py\n",
                    0.1,
                    "model",
                )
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["plugins/uncovered/y.py"],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success_mismatch, msg_mismatch, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_not_called()
        assert success_mismatch is False
        assert "uncovered/y.py" in (msg_mismatch or "")


class TestIssue1215Round2ResumeCleanFlags:
    """Round-2 Finding 3: resuming a clean run must not re-enter the fixer."""

    def test_resume_after_clean_step5_skips_fixer(self, tmp_path):
        """A resume with last_completed_step=5 and clean cached Steps 3-5 skips Steps 6.x."""
        from pdd.agentic_checkup_orchestrator import _get_state_dir

        state_dir = _get_state_dir(tmp_path)
        state_dir.mkdir(parents=True, exist_ok=True)
        state_path = state_dir / "state.json"
        cached_state = {
            "issue_number": 99,
            "issue_url": "https://github.com/o/r/issues/99",
            "last_completed_step": 5,
            "step_outputs": {
                "1": "out-1",
                "2": "out-2",
                "3": "out-3",
                "4": "out-4",
                # Round-8 Finding 1: cached Step 5 must include a
                # ``failure_signal`` block with ``status: pass`` for the
                # resume to honour it as logically clean.
                "5": STEP5_CLEAN_OUTPUT,
            },
            "total_cost": 0.0,
            "model": "gpt-4",
            "github_comment_id": None,
            "fix_verify_iteration": 1,
            "previous_fixes": "",
            "step_comments": [],
            "issue_title": "Fix pdd/main.py",
            "issue_content": "Bug in pdd/main.py causing test failures",
        }
        state_path.write_text(json.dumps(cached_state))

        steps_invoked: List[float] = []

        def step_side_effect(step_num, name, context, **kwargs):
            steps_invoked.append(step_num)
            if step_num == 5:
                # Round-8 Finding 1: Step 5 must emit the structured
                # ``failure_signal`` block with ``status: pass`` to be
                # treated as logically clean — the orchestrator now
                # fails closed when the block is missing or unparseable.
                return (True, STEP5_CLEAN_OUTPUT, 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=[],
            commit_push_return=(True, "No changes to push."),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        assert 6.1 not in steps_invoked, (
            f"Fixer step 6.1 ran on resume of a clean run: invoked={steps_invoked}"
        )
        assert 6.2 not in steps_invoked
        assert 6.3 not in steps_invoked


class TestIssue1215Round2Step5PersistedScrubbing:
    """Round-2 Finding 4: Step 5 failure output is scrubbed BEFORE persistence."""

    def test_secret_in_step5_failure_not_persisted_to_step6_context(self, tmp_path):
        """Tokens in Step 5 stderr never reach Step 6 context or persisted state."""
        secret_token = "ghp_" + "A" * 36
        step5_failure_text = (
            f"FAILED tests/test_secrets.py::test_x\n"
            f"E   subprocess.CalledProcessError: cmd 'curl -H Authorization: token "
            f"{secret_token} ...'"
        )
        captured_step6_contexts: List[Dict] = []

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, step5_failure_text, 0.1, "model")
            if step_num == 6.1:
                captured_step6_contexts.append(dict(context))
                return (True, "FILES_MODIFIED: pdd/main.py", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            commit_push_return=(True, "Pushed 1 file"),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        assert captured_step6_contexts, "Step 6.1 must run after Step 5 failure"
        ctx = captured_step6_contexts[0]
        assert secret_token not in ctx.get("step5_output", ""), (
            "Step 5 raw token leaked into context['step5_output'] — scrubbing "
            "did not run before persistence."
        )
        assert secret_token not in ctx.get("step5_failure_signal", "")


class TestIssue1215Round2FailureSignalValidation:
    """Round-2 Finding 5: parse/validate the failure_signal block."""

    def test_parse_failure_signal_missing_block(self):
        fields, missing = _parse_failure_signal_block(
            "No fenced block at all."
        )
        assert fields == {}
        assert missing == ["__block__"]

    def test_parse_failure_signal_well_formed(self):
        text = (
            "Preamble.\n"
            "```failure_signal\n"
            "command: pytest -q\n"
            "exit_code: 1\n"
            "status: fail\n"
            "failing_ids: tests/test_main.py::test_x\n"
            "artifact_path: inline\n"
            "output: |\n"
            "  E   AssertionError: expected 1, got 2\n"
            "  FAILED tests/test_main.py::test_x\n"
            "```\n"
        )
        fields, missing = _parse_failure_signal_block(text)
        assert missing == []
        assert fields["command"] == "pytest -q"
        assert fields["status"] == "fail"
        assert "AssertionError" in fields["output"]

    def test_parse_failure_signal_missing_required_key(self):
        text = (
            "```failure_signal\n"
            "command: pytest -q\n"
            "exit_code: 1\n"
            "failing_ids: tests/test_main.py::test_x\n"
            "artifact_path: inline\n"
            "output: |\n"
            "  E   AssertionError\n"
            "```\n"
        )
        fields, missing = _parse_failure_signal_block(text)
        assert "status" in missing

    def test_normalised_signal_synthesises_when_missing(self):
        raw = "FAILED tests/test_x.py::test_y - AssertionError: 1 != 2"
        text = _normalised_failure_signal_text(raw, {}, ["__block__"])
        assert "```failure_signal" in text
        assert "orchestrator-note" in text
        assert "AssertionError" in text

    def test_step6_receives_artifact_log_when_step5_uses_artifact_path(self, tmp_path):
        """Codex round-4 Finding 3: when Step 5 emits an empty ``output:``
        but points to a real log file via ``artifact_path:``, the
        orchestrator must read the file and inject its (scrubbed)
        contents into ``context['step5_failure_signal']`` so Step 6 has
        the failure detail.
        """
        # The orchestrator's PR worktree is tmp_path / "wt"; place the
        # artifact under that worktree so the helper accepts it.
        wt = tmp_path / "wt"
        wt.mkdir(exist_ok=True)
        artifact_rel = ".pdd/checkup-context/pytest-iter1.log"
        artifact_full = wt / artifact_rel
        artifact_full.parent.mkdir(parents=True, exist_ok=True)
        artifact_full.write_text(
            "=== test session starts ===\n"
            "tests/test_main.py::test_critical_path FAILED\n"
            "E   AssertionError: expected 1, got 2 (from artifact)\n"
            "=== short test summary info ===\n"
            "FAILED tests/test_main.py::test_critical_path\n",
            encoding="utf-8",
        )

        step5_output = (
            "Tests failed (log saved to artifact).\n"
            "```failure_signal\n"
            "command: pytest -q\n"
            "exit_code: 1\n"
            "status: fail\n"
            "failing_ids: tests/test_main.py::test_critical_path\n"
            f"artifact_path: {artifact_rel}\n"
            "output: |\n"
            "```\n"
        )
        captured: List[Dict] = []

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, step5_output, 0.1, "model")
            if step_num == 6.1:
                captured.append(dict(context))
                return (True, "FILES_MODIFIED: pdd/main.py", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            commit_push_return=(True, "Pushed 1 file"),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        assert captured, "Step 6.1 must run after Step 5 failure"
        ctx = captured[0]
        signal = ctx.get("step5_failure_signal", "")
        # The full artifact body must reach Step 6 — not just the empty
        # inline output that Step 5 emitted.
        assert "expected 1, got 2 (from artifact)" in signal, (
            "Step 6 must see the artifact log content, not the empty inline "
            "output emitted by Step 5"
        )
        assert "test_critical_path" in signal
        # ``output`` is no longer missing once the artifact was read.
        assert "output" not in ctx.get("step5_failure_signal_missing", "")

    def test_artifact_path_outside_worktree_is_refused(self, tmp_path):
        """Path-traversal via ``artifact_path:`` must not leak files
        from outside the PR worktree into Step 6 context.
        """
        from pdd.agentic_checkup_orchestrator import (
            _read_failure_signal_artifact,
        )

        wt = tmp_path / "wt"
        wt.mkdir(exist_ok=True)
        # File outside the worktree — must not be read.
        outside = tmp_path / "secret.log"
        outside.write_text("super-secret token: ghp_abc\n", encoding="utf-8")

        result = _read_failure_signal_artifact("../secret.log", wt)
        assert result is None, "artifact_path must refuse paths outside worktree"

    def test_step6_receives_failure_signal_when_step5_omits_block(self, tmp_path):
        """Step 6 always receives ``context['step5_failure_signal']`` after Step 5 failure."""
        captured: List[Dict] = []

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, "FAILED tests/test_x.py::test_y - AssertionError", 0.1, "model")
            if step_num == 6.1:
                captured.append(dict(context))
                return (True, "FILES_MODIFIED: pdd/main.py", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            commit_push_return=(True, "Pushed 1 file"),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        assert captured, "Step 6.1 must run after Step 5 failure"
        ctx = captured[0]
        assert "```failure_signal" in ctx.get("step5_failure_signal", "")
        assert "__block__" in ctx.get("step5_failure_signal_missing", "")


class TestIssue1215Round3ScopeGuardJustification:
    """Round-3 Finding 1: only justified EXPANSION_ITEMS can subtract paths."""

    def test_unjustified_expansion_path_still_in_out_of_scope(self, tmp_path):
        """Listing an out-of-scope file under EXPANSION_ITEMS with no reason is refused."""
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 6.1:
                # EXPANSION_ITEMS lists the unrelated file but provides
                # NO justification — must be treated as out-of-scope.
                return (
                    True,
                    "FILES_MODIFIED: plugins/unrelated/x.py\n"
                    "EXPANSION_ITEMS: plugins/unrelated/x.py\n",
                    0.1,
                    "model",
                )
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["plugins/unrelated/x.py"],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_not_called()
        assert success is False
        assert "scope guard" in (msg or "").lower()
        assert "plugins/unrelated/x.py" in (msg or "")


class TestIssue1215Round3CleanRunSideEffect:
    """Round-3 Finding 2: clean Steps 3/4/5 must not push side-effect edits."""

    def test_clean_run_with_side_effect_dirty_file_discards_without_push(self, tmp_path):
        """Steps 3/4/5 clean → fixer skipped → side-effect dirt is restored."""
        steps_invoked: List[float] = []
        wt = tmp_path / "wt"
        (wt / "pdd").mkdir(parents=True, exist_ok=True)
        (wt / "pdd" / "main.py").write_text("side effect\n", encoding="utf-8")

        def step_side_effect(step_num, name, context, **kwargs):
            steps_invoked.append(step_num)
            if step_num == 5:
                # Round-8 Finding 1: Step 5 must emit ``status: pass`` to
                # be treated as logically clean — missing/unparseable
                # blocks now fail closed.
                return (True, STEP5_CLEAN_OUTPUT, 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10], \
             patch(
                 "pdd.agentic_checkup_orchestrator._trusted_gate_git",
                 return_value=("git", os.environ.copy()),
             ), patch(
                 "pdd.agentic_checkup_orchestrator._git_changed_files",
                 side_effect=[["pdd/main.py"], []],
             ):
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        # Confirm fixer steps were indeed skipped on the clean path.
        assert 6.1 not in steps_invoked, (
            f"Fixer 6.1 must be skipped on clean Steps 3-5: invoked={steps_invoked}"
        )
        push_mock.assert_not_called()
        assert success is True, msg
        assert not (wt / "pdd" / "main.py").exists()

    def test_clean_run_restores_tracked_normal_file_side_effect(self, tmp_path):
        """Tracked ordinary files are restored, not treated as Layer 1 failures."""
        wt = tmp_path / "repo"
        (wt / "app").mkdir(parents=True)
        target = wt / "app" / "calculator.py"
        target.write_text("def add(a, b):\n    return a + b\n", encoding="utf-8")
        subprocess.run(["git", "init"], cwd=wt, check=True, capture_output=True)
        subprocess.run(["git", "add", "."], cwd=wt, check=True, capture_output=True)
        subprocess.run(
            [
                "git",
                "-c",
                "user.email=test@example.com",
                "-c",
                "user.name=Test User",
                "commit",
                "-m",
                "initial",
            ],
            cwd=wt,
            check=True,
            capture_output=True,
        )
        target.write_text(
            "def add(a, b):\n    return a + b + 0\n",
            encoding="utf-8",
        )

        remaining, discarded = _discard_clean_run_side_effects(
            wt,
            ["app/calculator.py"],
        )

        assert remaining == []
        assert discarded == ["app/calculator.py"]
        assert target.read_text(encoding="utf-8") == "def add(a, b):\n    return a + b\n"

    def test_clean_run_discards_lockfile_tooling_noise(self, tmp_path):
        """Lockfile-only non-fixer dirt is restored, not treated as Layer 1 failure."""
        wt = tmp_path / "wt"
        (wt / "frontend").mkdir(parents=True)
        (wt / "frontend" / "package-lock.json").write_text(
            '{"lockfileVersion":3}\n',
            encoding="utf-8",
        )

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (True, STEP5_CLEAN_OUTPUT, 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value=dict(_PR_META_REAL_API),
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=step_side_effect,
        ), patch(
            "pdd.agentic_checkup_orchestrator._git_changed_files",
            side_effect=[["frontend/package-lock.json"], []],
        ), patch(
            "pdd.agentic_checkup_orchestrator._trusted_gate_git",
            return_value=("git", os.environ.copy()),
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed 1 file"),
        ) as push_mock, patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state",
        ), patch(
            "pdd.agentic_checkup_orchestrator._check_architecture_registry_edit_guard",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator._check_prompt_source_guard",
            return_value=None,
        ), patch("pdd.agentic_checkup_orchestrator.console"):
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        assert success is True, msg
        push_mock.assert_not_called()
        assert not (wt / "frontend" / "package-lock.json").exists()

    def test_clean_run_discards_prompt_generated_tooling_noise(self, tmp_path):
        """Generated-code non-fixer dirt is restored before prompt-source guard."""
        wt = tmp_path / "wt"
        (wt / "app").mkdir(parents=True)
        (wt / "app" / "async_helpers.py").write_text("dirty\n", encoding="utf-8")
        (wt / "requirements.txt").write_text("dirty\n", encoding="utf-8")

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (True, STEP5_CLEAN_OUTPUT, 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        with patch(
            "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
            return_value=(wt, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
            return_value={
                **dict(_PR_META_REAL_API),
                "api_changed_files": "- A: staging2_marker.md",
                "api_changed_files_full": "- A: staging2_marker.md",
            },
        ), patch(
            "pdd.agentic_checkup_orchestrator._run_single_step",
            side_effect=step_side_effect,
        ), patch(
            "pdd.agentic_checkup_orchestrator._git_changed_files",
            side_effect=[
                ["app/async_helpers.py", "requirements.txt"],
                [],
            ],
        ), patch(
            "pdd.agentic_checkup_orchestrator._load_prompt_source_map",
            return_value={
                "app/async_helpers.py": "pdd/prompts/async_helpers_Python.prompt",
                "requirements.txt": "pdd/prompts/backend_requirements_Text.prompt",
            },
        ), patch(
            "pdd.agentic_checkup_orchestrator._trusted_gate_git",
            return_value=("git", os.environ.copy()),
        ), patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=(True, "Pushed 1 file"),
        ) as push_mock, patch(
            "pdd.agentic_checkup_orchestrator.load_workflow_state",
            return_value=(None, None),
        ), patch(
            "pdd.agentic_checkup_orchestrator.save_workflow_state",
            return_value=None,
        ), patch(
            "pdd.agentic_checkup_orchestrator.clear_workflow_state",
        ), patch(
            "pdd.agentic_checkup_orchestrator._check_architecture_registry_edit_guard",
            return_value=None,
        ) as registry_guard_mock, patch(
            "pdd.agentic_checkup_orchestrator._check_prompt_source_guard",
            side_effect=lambda _wt, changed: (
                "generated-code-only fix refused" if changed else None
            ),
        ) as prompt_guard_mock, patch("pdd.agentic_checkup_orchestrator.console"):
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        assert success is True, msg
        push_mock.assert_not_called()
        registry_guard_mock.assert_called_once_with(wt, [])
        prompt_guard_mock.assert_called_once_with(wt, [])
        assert not (wt / "app" / "async_helpers.py").exists()
        assert not (wt / "requirements.txt").exists()


class TestIssue1215Round3FailureSignalContentValidation:
    """Round-3 Finding 4: failure_signal must have non-empty fields on fail status."""

    def test_empty_output_block_flagged_missing(self):
        text = (
            "```failure_signal\n"
            "command: pytest -q\n"
            "exit_code: 1\n"
            "status: fail\n"
            "failing_ids: tests/test_main.py::test_x\n"
            "artifact_path: inline\n"
            "output: |\n"
            "```\n"
        )
        fields, missing = _parse_failure_signal_block(text)
        assert "output" in missing

    def test_empty_exit_code_flagged_missing_on_fail(self):
        text = (
            "```failure_signal\n"
            "command: pytest -q\n"
            "exit_code: \n"
            "status: fail\n"
            "failing_ids: tests/test_main.py::test_x\n"
            "artifact_path: inline\n"
            "output: |\n"
            "  AssertionError\n"
            "```\n"
        )
        fields, missing = _parse_failure_signal_block(text)
        assert "exit_code" in missing

    def test_empty_failing_ids_flagged_missing_on_fail(self):
        text = (
            "```failure_signal\n"
            "command: pytest -q\n"
            "exit_code: 1\n"
            "status: error\n"
            "failing_ids: \n"
            "artifact_path: inline\n"
            "output: |\n"
            "  AssertionError\n"
            "```\n"
        )
        fields, missing = _parse_failure_signal_block(text)
        assert "failing_ids" in missing

    def test_empty_artifact_path_flagged_missing_on_fail(self):
        text = (
            "```failure_signal\n"
            "command: pytest -q\n"
            "exit_code: 1\n"
            "status: fail\n"
            "failing_ids: tests/test_main.py::test_x\n"
            "artifact_path: \n"
            "output: |\n"
            "  AssertionError\n"
            "```\n"
        )
        fields, missing = _parse_failure_signal_block(text)
        assert "artifact_path" in missing

    def test_pass_status_allows_empty_failure_fields(self):
        """When status indicates success, the failure-only required fields
        may legitimately be empty."""
        text = (
            "```failure_signal\n"
            "command: pytest -q\n"
            "exit_code: 0\n"
            "status: pass\n"
            "failing_ids: \n"
            "artifact_path: inline\n"
            "output: |\n"
            "```\n"
        )
        fields, missing = _parse_failure_signal_block(text)
        # ``pass`` status should not require failure-context fields.
        assert "failing_ids" not in missing
        assert "output" not in missing


class TestIssue1215Round3Step6PromptFailureSignalSlot:
    """Round-3 Finding 3: Step 6 prompt must contain ``step5_failure_signal``."""

    def test_step6_prompt_template_references_failure_signal(self):
        # Read the worktree's prompt file directly — the resolver picks up
        # whichever ``pdd`` package is on sys.path, which during ``pip
        # install -e`` may point at the installed copy rather than the
        # source-tree change we are verifying.
        from pathlib import Path

        prompt_path = (
            Path(__file__).resolve().parent.parent
            / "pdd"
            / "prompts"
            / "agentic_checkup_step6_1_fix_LLM.prompt"
        )
        assert prompt_path.exists(), f"step 6.1 prompt must exist at {prompt_path}"
        tmpl = prompt_path.read_text(encoding="utf-8")
        assert "{step5_failure_signal}" in tmpl, (
            "Step 6.1 prompt must render the normalised failure_signal block"
        )

    def test_step6_formatted_prompt_contains_synthesised_signal(self, tmp_path):
        """When Step 5 omits failure_signal, Step 6's *formatted* prompt
        carries the orchestrator-synthesised block, not just raw output."""
        from pathlib import Path as _Path
        from pdd.preprocess import preprocess

        prompt_path = (
            _Path(__file__).resolve().parent.parent
            / "pdd"
            / "prompts"
            / "agentic_checkup_step6_1_fix_LLM.prompt"
        )
        worktree_prompt = prompt_path.read_text(encoding="utf-8")

        captured_prompts: List[str] = []

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, "FAILED tests/test_x.py - AssertionError", 0.1, "model")
            if step_num == 6.1:
                # Re-substitute the worktree's prompt source against the
                # orchestrator's live context. This exercises the same
                # ``preprocess`` + format-map path the orchestrator uses,
                # without depending on which pdd package the resolver picks.
                pre = preprocess(
                    worktree_prompt,
                    recursive=True,
                    double_curly_brackets=True,
                    exclude=list(context.keys()),
                )
                captured_prompts.append(pre.format_map(context))
                return (True, "FILES_MODIFIED: pdd/main.py", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            commit_push_return=(True, "Pushed 1 file"),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        assert captured_prompts, "Step 6.1 must have run"
        rendered = captured_prompts[0]
        assert "```failure_signal" in rendered, (
            "Formatted Step 6 prompt must contain the synthesised failure_signal block"
        )
        assert "orchestrator-note" in rendered, (
            "Synthesised block must announce itself in the formatted prompt"
        )


class TestIssue1215Round3DiffSizeGate:
    """Round-3 Finding 5: pre-push diff sanity gate refuses oversized fixes."""

    def test_oversized_diff_without_expansion_is_refused(self, tmp_path, monkeypatch):
        """A push that would add > limit lines without EXPANSION_ITEMS justification is refused."""
        # Force a tiny limit so we don't have to fabricate thousands of lines.
        monkeypatch.setenv("PDD_CHECKUP_DIFF_LOC_LIMIT", "5")

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 6.1:
                return (True, "FILES_MODIFIED: pdd/main.py", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        # Pretend the worktree shows 100 added lines on the oversized
        # file. Round-9: the gate now consumes per-path counts via
        # _diff_size_added_lines_by_path.
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10], \
             patch(
                 "pdd.agentic_checkup_orchestrator._diff_size_added_lines_by_path",
                 return_value={"pdd/main.py": 100},
             ):
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_not_called()
        assert success is False
        assert "diff size guard" in (msg or "").lower()
        assert "100" in (msg or "")

    def test_oversized_diff_with_valid_expansion_allowed(self, tmp_path, monkeypatch):
        """A justified EXPANSION_ITEMS bypasses the size gate (operator opt-in)."""
        monkeypatch.setenv("PDD_CHECKUP_DIFF_LOC_LIMIT", "5")

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 6.1:
                return (
                    True,
                    "FILES_MODIFIED: pdd/main.py\n"
                    "EXPANSION_ITEMS: pdd/main.py — rewrite required because the "
                    "module's public interface changed and every caller needs "
                    "the new signature.\n",
                    0.1,
                    "model",
                )
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            commit_push_return=(True, "Pushed 1 file"),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10], \
             patch(
                 "pdd.agentic_checkup_orchestrator._diff_size_added_lines_by_path",
                 return_value={"pdd/main.py": 100},
             ):
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        push_mock.assert_called_once()

    def test_oversized_diff_with_unrelated_expansion_path_is_refused(
        self, tmp_path, monkeypatch
    ):
        """Codex round-4 Finding 4: an EXPANSION_ITEMS marker that names a
        valid-but-unrelated path must NOT bypass the size gate.

        Negative regression for the hole where ``has_valid_expansion``
        flipped to True the moment EXPANSION_ITEMS listed any justified
        path, even one that did not cover the file actually contributing
        to the oversized diff.
        """
        monkeypatch.setenv("PDD_CHECKUP_DIFF_LOC_LIMIT", "5")

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 6.1:
                # The worktree shows pdd/main.py is dirty, but the fixer
                # lists pdd/helpers.py under EXPANSION_ITEMS — a valid,
                # justified, but UNRELATED path. The size gate must still
                # refuse because the oversized changed path (pdd/main.py)
                # is not covered by the marker.
                return (
                    True,
                    "FILES_MODIFIED: pdd/main.py\n"
                    "EXPANSION_ITEMS: pdd/helpers.py — needs a small "
                    "tweak because the helpers module exports a constant "
                    "that the new main.py implementation relies on.\n",
                    0.1,
                    "model",
                )
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            # In-scope file per PR metadata (so the scope guard passes)
            # but the diff is oversized and the expansion list does NOT
            # cover this path.
            git_changed_files=["pdd/main.py"],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10], \
             patch(
                 "pdd.agentic_checkup_orchestrator._diff_size_added_lines_by_path",
                 return_value={"pdd/main.py": 100},
             ):
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_not_called()
        assert success is False
        # Refusal must specifically mention that the marker did not cover
        # the oversized changed path.
        assert "diff size guard" in (msg or "").lower()
        assert "did not cover" in (msg or "").lower(), msg
        assert "pdd/main.py" in (msg or ""), msg


class TestIssue1215Round5Step5LogicalOutcome:
    """Round-5 Finding 1: derive Step 5 cleanliness from the failure_signal
    status, not from provider success. A provider-success result that
    embeds ``status: fail`` must NOT skip the fixer."""

    def test_provider_success_with_fail_status_runs_fixer(self, tmp_path):
        """Provider returns success=True; failure_signal.status=fail —
        Step 6.1 MUST still be invoked.

        Codex round-5 evidence: ``_run_single_step`` returning
        ``success=True`` plus ``failure_signal.status: fail`` invoked
        ``[1,2,3,4,5,7]`` and never called Step 6 on the broken code.
        """
        steps_invoked: List[float] = []
        step5_payload = (
            "Ran tests (provider call succeeded).\n"
            "```failure_signal\n"
            "command: pytest -q\n"
            "exit_code: 1\n"
            "status: fail\n"
            "failing_ids: tests/test_main.py::test_x\n"
            "artifact_path: inline\n"
            "output: |\n"
            "  E   AssertionError: expected 1, got 2\n"
            "  FAILED tests/test_main.py::test_x\n"
            "```\n"
        )

        def step_side_effect(step_num, name, context, **kwargs):
            steps_invoked.append(step_num)
            if step_num == 5:
                return (True, step5_payload, 0.1, "model")
            if step_num == 6.1:
                return (True, "FILES_MODIFIED: pdd/main.py", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            commit_push_return=(True, "Pushed 1 file"),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        assert 6.1 in steps_invoked, (
            "Step 6.1 must run when Step 5 reports status: fail even on "
            f"provider success; invoked={steps_invoked}"
        )

    def test_provider_success_with_pass_status_skips_fixer(self, tmp_path):
        """A clean Step 5 (status: pass) on the provider-success path
        keeps the old optimisation: skip the fixer when 3/4/5 are clean."""
        steps_invoked: List[float] = []
        step5_payload = (
            "Tests passed.\n"
            "```failure_signal\n"
            "command: pytest -q\n"
            "exit_code: 0\n"
            "status: pass\n"
            "failing_ids: \n"
            "artifact_path: inline\n"
            "output: |\n"
            "```\n"
        )

        def step_side_effect(step_num, name, context, **kwargs):
            steps_invoked.append(step_num)
            if step_num == 5:
                return (True, step5_payload, 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=[],
            commit_push_return=(True, "No changes to push."),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        assert 6.1 not in steps_invoked, (
            f"Clean Step 5 must skip Step 6 on a clean PR run; invoked={steps_invoked}"
        )


class TestIssue1215Round5Step5SecretScrubbingAlwaysOn:
    """Round-5 Finding 2: scrub Step 5 output on EVERY result, not just
    provider failures. A provider-success result with a token in the
    failure_signal output must not leak to context, step_outputs, or
    GitHub step comments."""

    def test_token_scrubbed_when_provider_succeeds_but_tests_fail(self, tmp_path):
        """Provider succeeds, failure_signal.status=fail, output contains a
        token — token must not appear in context['step5_output'],
        context['step5_failure_signal'], or any captured comment body."""
        secret_token = "ghp_" + "B" * 36
        step5_payload = (
            "```failure_signal\n"
            "command: pytest -q\n"
            "exit_code: 1\n"
            "status: fail\n"
            "failing_ids: tests/test_main.py::test_x\n"
            "artifact_path: inline\n"
            "output: |\n"
            f"  curl -H 'Authorization: token {secret_token}' https://api.example/test\n"
            "  FAILED tests/test_main.py::test_x\n"
            "```\n"
        )
        captured_step6_contexts: List[Dict] = []
        captured_comment_bodies: List[str] = []

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (True, step5_payload, 0.1, "model")
            if step_num == 6.1:
                captured_step6_contexts.append(dict(context))
                return (True, "FILES_MODIFIED: pdd/main.py", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        def fake_post_step_comment(*, body, **kwargs):
            captured_comment_bodies.append(body)
            return True

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            commit_push_return=(True, "Pushed 1 file"),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10], \
             patch(
                 "pdd.agentic_checkup_orchestrator.post_step_comment_once",
                 side_effect=fake_post_step_comment,
             ):
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        assert captured_step6_contexts, "Step 6.1 must run after Step 5 logical failure"
        ctx = captured_step6_contexts[0]
        assert secret_token not in ctx.get("step5_output", ""), (
            "Token leaked into context['step5_output'] — provider-success path "
            "is not scrubbed."
        )
        assert secret_token not in ctx.get("step5_failure_signal", ""), (
            "Token leaked into the normalised failure_signal block passed to Step 6."
        )
        joined_comments = "\n".join(captured_comment_bodies)
        assert secret_token not in joined_comments, (
            "Token leaked into a captured per-step GitHub comment body."
        )


class TestIssue1215Round5ExpansionItemsPerPathJustification:
    """Round-5 Finding 3: each EXPANSION_ITEMS path must carry its OWN
    causal justification. A justified marker citing one path no longer
    whitelists unrelated paths listed by other markers."""

    def test_parse_returns_only_justified_paths_in_second_slot(self):
        text = (
            "EXPANSION_ITEMS: plugins/unjustified.py\n"
            "EXPANSION_ITEMS: plugins/justified.py — broken by core.py change\n"
        )
        paths, justified_paths = _parse_expansion_items(text)
        assert paths == {"plugins/unjustified.py", "plugins/justified.py"}
        assert justified_paths == {"plugins/justified.py"}

    def test_scope_guard_refuses_unjustified_sibling(self, tmp_path):
        """A fixer modifying an unjustified EXPANSION_ITEMS path is refused
        even when a sibling marker IS justified."""
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 6.1:
                # Two markers — only the second is justified. The fixer
                # modifies the unjustified one, which must be refused.
                return (
                    True,
                    "FILES_MODIFIED: plugins/unjustified.py\n"
                    "EXPANSION_ITEMS: plugins/unjustified.py\n"
                    "EXPANSION_ITEMS: plugins/justified.py — needed because "
                    "the PR's core change altered the interface this plugin "
                    "consumes.\n",
                    0.1,
                    "model",
                )
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["plugins/unjustified.py"],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_not_called()
        assert success is False
        assert "scope guard" in (msg or "").lower()
        assert "plugins/unjustified.py" in (msg or "")


class TestIssue1215Round5ArtifactSecretBoundary:
    """Round-5 Finding 4: scrub the FULL artifact body before truncation,
    and scrub the artifact path itself before echoing it in the truncation
    note."""

    def test_token_straddling_byte_cutoff_is_scrubbed(self, tmp_path, monkeypatch):
        """A ghp_ token straddling the byte cutoff must be scrubbed —
        truncating first would leave a recognisable ``ghp_AB...`` fragment
        that no longer matches the regex."""
        from pdd.agentic_checkup_orchestrator import _read_failure_signal_artifact

        # Tighten the cap so we don't have to write a 256KB file.
        monkeypatch.setattr(
            "pdd.agentic_checkup_orchestrator._ARTIFACT_OUTPUT_MAX_BYTES",
            64,
        )
        wt = tmp_path / "wt"
        wt.mkdir()
        # 60 bytes of padding then a 40-char ghp_ token. The cutoff at 64
        # bytes falls inside the token, so naive truncate-then-scrub would
        # leak a recognisable prefix.
        padding = "a" * 60
        token = "ghp_" + "C" * 36
        artifact_full = wt / "log.txt"
        artifact_full.write_text(padding + token + "\ntail line\n", encoding="utf-8")

        result = _read_failure_signal_artifact("log.txt", wt)
        assert result is not None
        # The raw token, even any 8+ char prefix recognisable as a token,
        # must not appear in the returned string.
        assert token not in result, (
            "Full token leaked; scrub did not run on the full body before truncation."
        )
        assert "ghp_" + "C" * 4 not in result, (
            "Recognisable ghp_ fragment leaked across the truncation boundary."
        )
        # Truncation note must be emitted because the scrubbed body is
        # still > 64 bytes.
        assert "orchestrator-note" in result

    def test_token_in_artifact_path_is_scrubbed(self, tmp_path, monkeypatch):
        """A ghp_ token embedded in the artifact_path value must not be
        echoed back unredacted in the truncation note."""
        from pdd.agentic_checkup_orchestrator import _read_failure_signal_artifact

        monkeypatch.setattr(
            "pdd.agentic_checkup_orchestrator._ARTIFACT_OUTPUT_MAX_BYTES",
            16,
        )
        wt = tmp_path / "wt"
        wt.mkdir()
        # Create a directory whose name contains a token.
        leaky_dir_name = "ghp_" + "D" * 36
        leaky_dir = wt / leaky_dir_name
        leaky_dir.mkdir()
        artifact_full = leaky_dir / "log.txt"
        # Body large enough to trigger truncation note.
        artifact_full.write_text("x" * 200, encoding="utf-8")

        rel_path = f"{leaky_dir_name}/log.txt"
        result = _read_failure_signal_artifact(rel_path, wt)
        assert result is not None
        assert "orchestrator-note" in result, (
            "Truncation note must fire — the artifact exceeds the byte cap."
        )
        # The token must not survive in the truncation note's path echo.
        assert "ghp_" + "D" * 36 not in result, (
            "Raw token in artifact_path leaked into the truncation note."
        )


class TestIssue1215Round6ExpansionItemsTrailingProse:
    """Round-6 Finding 1: trailing prose (e.g. a closing "All done." line)
    must NOT count as a per-marker justification. Only inline reasons,
    bullets/indented continuations, explicit justification prefixes, lines
    mentioning the marker's paths, or lines with causal keywords qualify."""

    def test_unrelated_trailing_prose_does_not_justify(self):
        text = (
            "EXPANSION_ITEMS: plugins/x.py\n"
            "All done.\n"
        )
        paths, justified_paths = _parse_expansion_items(text)
        assert paths == {"plugins/x.py"}
        assert justified_paths == set(), (
            "Trailing 'All done.' must not satisfy the per-marker "
            "justification requirement."
        )

    def test_bullet_continuation_with_causal_keyword_justifies(self):
        # Bullets alone no longer qualify (round-7) — but a bullet line
        # carrying a causal keyword still does.
        text = (
            "EXPANSION_ITEMS: plugins/x.py\n"
            "- needed because the cascading import error broke the build\n"
        )
        _, justified_paths = _parse_expansion_items(text)
        assert justified_paths == {"plugins/x.py"}

    def test_indented_continuation_with_path_mention_justifies(self):
        # Indented prose alone no longer qualifies (round-7) — but an
        # indented line that mentions the marker path still does.
        text = (
            "EXPANSION_ITEMS: plugins/x.py\n"
            "  test imports plugins/x.py which the PR change broke\n"
        )
        _, justified_paths = _parse_expansion_items(text)
        assert justified_paths == {"plugins/x.py"}

    def test_indented_padding_alone_does_not_justify(self):
        # Round-7 Finding 1: arbitrary indented prose without a causal
        # signal must not satisfy the justification requirement.
        text = (
            "EXPANSION_ITEMS: plugins/unrelated/x.py\n"
            "  All done.\n"
        )
        paths, justified_paths = _parse_expansion_items(text)
        assert paths == {"plugins/unrelated/x.py"}
        assert justified_paths == set(), (
            "Indented padding without a causal signal must not justify."
        )

    def test_bullet_padding_alone_does_not_justify(self):
        # Round-7 Finding 1: bare bullets carrying no semantic content
        # must not whitelist the marker path either.
        text = (
            "EXPANSION_ITEMS: plugins/unrelated/x.py\n"
            "- All done.\n"
        )
        paths, justified_paths = _parse_expansion_items(text)
        assert paths == {"plugins/unrelated/x.py"}
        assert justified_paths == set(), (
            "Bullet-only padding without a causal signal must not justify."
        )

    def test_prefix_marker_does_justify(self):
        text = (
            "EXPANSION_ITEMS: plugins/x.py\n"
            "Justification: shared util needs the same signature change\n"
        )
        _, justified_paths = _parse_expansion_items(text)
        assert justified_paths == {"plugins/x.py"}

    def test_line_mentioning_path_does_justify(self):
        text = (
            "EXPANSION_ITEMS: plugins/x.py\n"
            "Updating plugins/x.py was required by the new interface\n"
        )
        _, justified_paths = _parse_expansion_items(text)
        assert justified_paths == {"plugins/x.py"}

    def test_causal_keyword_does_justify(self):
        text = (
            "EXPANSION_ITEMS: plugins/x.py\n"
            "Refactor needed because the upstream signature changed\n"
        )
        _, justified_paths = _parse_expansion_items(text)
        assert justified_paths == {"plugins/x.py"}

    def test_scope_guard_refuses_when_only_prose_padding(self, tmp_path):
        """End-to-end: a bare marker followed by closing prose is refused
        by the pre-push scope guard (no per-path justification means no
        bypass)."""
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 6.1:
                return (
                    True,
                    "FILES_MODIFIED: plugins/unrelated/x.py\n"
                    "EXPANSION_ITEMS: plugins/unrelated/x.py\n"
                    "All done.\n",
                    0.1,
                    "model",
                )
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["plugins/unrelated/x.py"],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_not_called()
        assert success is False
        assert "scope guard" in (msg or "").lower()


class TestIssue1215Round6Step5LogicalFailureVisibility:
    """Round-6 Finding 2: a provider-success Step 5 whose embedded
    failure_signal declares status: fail must (a) print failure detail to
    the user, (b) flip step_outputs['5'] to a FAILED: prefix so the
    downstream causal-connection check actually runs."""

    def test_causal_guard_runs_on_logical_failure(self, tmp_path):
        """Provider success + failure_signal status:fail must engage the
        causal-connection check — a fixer touching a file with zero
        causal overlap is refused."""
        step5_logical_fail_output = (
            "Ran pytest, captured failure_signal below.\n"
            "```failure_signal\n"
            "command: pytest -k test_main\n"
            "exit_code: 1\n"
            "status: fail\n"
            "failing_ids: tests/test_main.py::test_x\n"
            "artifact_path: inline\n"
            "output: assertion failed\n"
            "```\n"
        )

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                # Provider succeeded but the signal block declares
                # status: fail.
                return (True, step5_logical_fail_output, 0.1, "model")
            if step_num == 6.1:
                # Fixer modifies a file that has zero overlap with the PR's
                # changed-file set (pdd/main.py) and zero overlap with the
                # failure paths (tests/test_main.py). No EXPANSION_ITEMS.
                return (
                    True,
                    "FILES_MODIFIED: pdd/unrelated_module.py\n",
                    0.1,
                    "model",
                )
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/unrelated_module.py"],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_not_called()
        assert success is False
        # Causal-connection check fires only when step_outputs["5"]
        # starts with "FAILED:" — its message names the unrelated file.
        assert "causal" in (msg or "").lower() or "scope" in (msg or "").lower()
        assert "pdd/unrelated_module.py" in (msg or "")


class TestIssue1215Round6FixerInvokedResume:
    """Round-6 Finding 3: a resume that skips past Step 6 must still
    recognise the fixer ran in a prior iteration — otherwise the
    clean-run side-effect guard wrongly refuses the fixer's dirty files."""

    def test_resume_with_persisted_step6_output_does_not_refuse_dirty_files(
        self, tmp_path
    ):
        """When workflow state carries persisted 6_1 output AND the
        resume start_step is past Step 6, ``fixer_invoked`` must already
        be True so dirty fixer files reach the scope/causal checks rather
        than the side-effect refusal."""
        wt = tmp_path / "wt"
        wt.mkdir(exist_ok=True)

        # Simulate a workflow state where Steps 3..6 already completed in
        # a previous run; only Step 7 still has to run. The orchestrator's
        # state-identity guard requires mode/pr_number/pr_owner/pr_repo/
        # pr_head_sha to match the current invocation before cached step
        # outputs are honoured — without those, the resume path discards
        # the cache and runs from scratch (which would still defeat the
        # check we're trying to make here).
        persisted_step_outputs = {
            "3": "clean",
            "4": "clean",
            "5": "clean",
            "6_1": "FILES_MODIFIED: pdd/main.py\n",
            "6_2": "verify-ok",
            "6_3": "review-ok",
        }
        persisted_state = {
            "mode": "pr",
            "pr_number": 200,
            "pr_owner": "o",
            "pr_repo": "r",
            "pr_head_sha": "abc123deadbeef",
            "last_completed_step": 6.3,
            "current_step": 7,
            "step_outputs": persisted_step_outputs,
            "context": {
                "files_to_stage": "pdd/main.py",
                "step5_output": "clean",
                "step6_1_output": "FILES_MODIFIED: pdd/main.py\n",
            },
            "total_cost": 0.0,
            "last_model_used": "model",
            "fix_verify_iteration": 1,
            "previous_fixes": "",
            "posted_step_comments": [],
            "changed_files": ["pdd/main.py"],
        }

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        meta = dict(_PR_META_REAL_API)
        patches = (
            patch(
                "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
                return_value=(wt, None),
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
                return_value=meta,
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._run_single_step",
                side_effect=step_side_effect,
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._git_changed_files",
                return_value=["pdd/main.py"],
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
                return_value=(True, "Pushed 1 file"),
            ),
            patch(
                "pdd.agentic_checkup_orchestrator.load_workflow_state",
                return_value=(persisted_state, "state.json"),
            ),
            patch(
                "pdd.agentic_checkup_orchestrator.save_workflow_state",
                return_value=None,
            ),
            patch("pdd.agentic_checkup_orchestrator.clear_workflow_state"),
            patch(
                "pdd.agentic_checkup_orchestrator._check_architecture_registry_edit_guard",
                return_value=None,
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._check_prompt_source_guard",
                return_value=None,
            ),
            patch("pdd.agentic_checkup_orchestrator.console"),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path, "use_github_state": True}
            )

        # The side-effect refusal would have fired on a False fixer_invoked
        # flag — assert it did NOT by checking the message and that push
        # was attempted (scope/causal/diff checks may still allow it).
        assert "clean-run side-effect guard" not in (msg or ""), (
            f"fixer_invoked was wrongly False on resume — refusal message: {msg!r}"
        )
        # If everything else is in order, the commit/push path should be
        # taken (pdd/main.py is in pr_file_set so scope check passes).
        push_mock.assert_called_once()
        assert success is True

    def test_manual_start_step_7_without_persisted_fixer_output_discards(
        self, tmp_path
    ):
        """Round-7 Finding 2: a manual --start-step 7 with NO persisted
        Step 6 output must still treat a dirty in-scope file as a clean-run
        side effect — the operator did not run the fixer, so the dirty file
        cannot be attributed to it or pushed.

        Round-8 Finding 1 follow-through: the live Step 5 mock emits a
        well-formed ``status: pass`` failure_signal so the fail-closed
        rule keeps the run on the clean path (otherwise Step 5 would be
        treated as logically failed and the fixer would run, masking the
        scenario we're testing)."""
        wt = tmp_path / "wt"
        (wt / "pdd").mkdir(parents=True, exist_ok=True)
        (wt / "pdd" / "main.py").write_text("side effect\n", encoding="utf-8")

        # State carries valid identity fields but NO 6_1/6_2/6_3 outputs —
        # so fixer_invoked must stay False even though start_step > 6.
        persisted_state = {
            "mode": "pr",
            "pr_number": 200,
            "pr_owner": "o",
            "pr_repo": "r",
            "pr_head_sha": "abc123deadbeef",
            "last_completed_step": 5,
            "current_step": 7,
            "step_outputs": {
                "3": "clean",
                "4": "clean",
                # Round-8 Finding 1: cached Step 5 must carry the
                # structured failure_signal block for fail-closed parsing
                # to recognise it as logically clean on resume.
                "5": STEP5_CLEAN_OUTPUT,
            },
            "context": {
                "files_to_stage": "",
                "step5_output": STEP5_CLEAN_OUTPUT,
            },
            "total_cost": 0.0,
            "last_model_used": "model",
            "fix_verify_iteration": 1,
            "previous_fixes": "",
            "posted_step_comments": [],
            "changed_files": [],
        }

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (True, STEP5_CLEAN_OUTPUT, 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        meta = dict(_PR_META_REAL_API)
        patches = (
            patch(
                "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
                return_value=(wt, None),
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
                return_value=meta,
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._run_single_step",
                side_effect=step_side_effect,
            ),
            # A dirty file shows up in the worktree even though no fixer
            # step ran — simulates tooling/Step 7 side effects.
            patch(
                "pdd.agentic_checkup_orchestrator._git_changed_files",
                return_value=["pdd/main.py"],
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
                return_value=(True, "Pushed 1 file"),
            ),
            patch(
                "pdd.agentic_checkup_orchestrator.load_workflow_state",
                return_value=(persisted_state, "state.json"),
            ),
            patch(
                "pdd.agentic_checkup_orchestrator.save_workflow_state",
                return_value=None,
            ),
            patch("pdd.agentic_checkup_orchestrator.clear_workflow_state"),
            patch(
                "pdd.agentic_checkup_orchestrator._check_architecture_registry_edit_guard",
                return_value=None,
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._check_prompt_source_guard",
                return_value=None,
            ),
            patch("pdd.agentic_checkup_orchestrator.console"),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10], \
             patch(
                 "pdd.agentic_checkup_orchestrator._trusted_gate_git",
                 return_value=("git", os.environ.copy()),
             ), patch(
                 "pdd.agentic_checkup_orchestrator._git_changed_files",
                 side_effect=[["pdd/main.py"], []],
             ):
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path, "use_github_state": True}
            )

        push_mock.assert_not_called()
        assert success is True, msg
        assert not (wt / "pdd" / "main.py").exists()


class TestIssue1215Round8Step5MissingFailureSignal:
    """Round-8 Finding 1: a provider-success Step 5 with no/mangled
    `failure_signal` block must fail closed — the fixer must run rather
    than the run being declared clean on broken tests."""

    def test_provider_success_no_failure_signal_block_invokes_fixer(self, tmp_path):
        invoked = []

        def step_side_effect(step_num, name, context, **kwargs):
            invoked.append(step_num)
            if step_num == 5:
                # Provider succeeds but emits NO failure_signal block,
                # while reporting failing tests in prose.
                return (
                    True,
                    "Ran pytest. FAILED tests/test_main.py::test_x",
                    0.1,
                    "model",
                )
            if step_num == 6.1:
                return (True, "FILES_MODIFIED: pdd/main.py\n", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        # Fail-closed: missing block ⇒ logical failure ⇒ fixer runs.
        assert 6.1 in invoked, (
            "Missing failure_signal must NOT be treated as clean — "
            f"steps invoked: {invoked}"
        )

    def test_provider_success_unknown_status_invokes_fixer(self, tmp_path):
        invoked = []
        weird_status_output = (
            "Tests ran.\n"
            "```failure_signal\n"
            "command: pytest\n"
            "exit_code: 0\n"
            "status: maybe\n"
            "failing_ids: none\n"
            "artifact_path: inline\n"
            "output: |\n"
            "  42 passed\n"
            "```"
        )

        def step_side_effect(step_num, name, context, **kwargs):
            invoked.append(step_num)
            if step_num == 5:
                return (True, weird_status_output, 0.1, "model")
            if step_num == 6.1:
                return (True, "FILES_MODIFIED: pdd/main.py\n", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        assert 6.1 in invoked, (
            "Unrecognised status word must be treated as a logical failure "
            f"and trigger the fixer — steps invoked: {invoked}"
        )


class TestIssue1215Round8ScopeGuardLocalDiffFallback:
    """Round-8 Finding 2: when the GitHub PR files API is empty/error
    but the local merge-base diff names the PR's changed files, the
    scope guard must accept edits to those files."""

    def test_scope_guard_accepts_local_merge_base_diff(self, tmp_path):
        # API rows empty (simulating gh failure / rate limit); local
        # merge-base diff IS populated via pr_scope_changed_files in
        # context. The scope guard should union both.
        api_empty_meta: Dict = {
            **_PR_META_1212,
            "api_changed_files": "",
            "api_changed_files_full": "",
            "api_changed_files_error": "rate limited",
            "base_ref": "main",
            "base_local_ref": "refs/heads/pdd-pr-base/200",
        }

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 4:
                # Seed pr_scope_changed_files in context, mimicking what
                # _format_pr_changed_files_for_prompt would write before
                # Step 6 — the orchestrator already seeds this at the
                # PR-worktree setup stage, but for this isolated mock
                # we set it on the first step that has a context.
                context["pr_scope_changed_files"] = (
                    "Base: refs/heads/pdd-pr-base/200\n"
                    "- M: pdd/main.py\n"
                    "- A: pdd/new_helper.py"
                )
                return (True, "out-4", 0.0, "model")
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 6.1:
                # Fixer touches a file listed in the LOCAL diff but not
                # in any API row — must be accepted.
                return (True, "FILES_MODIFIED: pdd/new_helper.py\n", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/new_helper.py"],
            pr_metadata=api_empty_meta,
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        assert "scope guard" not in (msg or "").lower(), (
            f"Local merge-base diff path should be in scope; msg={msg!r}"
        )
        push_mock.assert_called_once()
        assert success is True


class TestIssue1215Round8ScopeGuardAcceptsStep5FailurePaths:
    """Round-8 Finding 3: the Step 6 prompt allows edits to failing test
    files and causally connected files. The scope guard must accept
    those without requiring an EXPANSION_ITEMS marker — the causal
    guard remains the backstop."""

    def test_scope_guard_accepts_test_file_named_in_step5_failure(self, tmp_path):
        # API metadata lists pdd/main.py as the PR change. The fixer
        # edits tests/test_main.py (NOT in pr_file_set) because Step 5
        # named it as the failing file. The old scope guard refused
        # this; round-8 must allow it on the failure-path source.
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (
                    False,
                    "FAILED: tests/test_main.py::test_x - AssertionError",
                    0.1,
                    "model",
                )
            if step_num == 6.1:
                # Fixer edits the failing test file directly — NO
                # EXPANSION_ITEMS marker.
                return (True, "FILES_MODIFIED: tests/test_main.py\n", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["tests/test_main.py"],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        assert "scope guard" not in (msg or "").lower(), (
            f"Step 5 failure-named test file must be in scope; msg={msg!r}"
        )
        push_mock.assert_called_once()
        assert success is True


STEP5_SKIPPED_OUTPUT = (
    "Tests did not run.\n"
    "```failure_signal\n"
    "command: pytest -q\n"
    "exit_code: 0\n"
    "status: skipped\n"
    "failing_ids: none\n"
    "artifact_path: inline\n"
    "output: |\n"
    "  pytest collected 0 tests (no tests run)\n"
    "```"
)


class TestIssue1215Round9Step5Skipped:
    """Round-9 Finding 1: a Step 5 ``status: skipped`` means tests did
    not run. The fixer must NOT trigger (no failure to act on), and the
    pre-push gate must refuse any dirty-file push (no verification)."""

    def test_skipped_status_does_not_invoke_fixer(self, tmp_path):
        invoked = []

        def step_side_effect(step_num, name, context, **kwargs):
            invoked.append(step_num)
            if step_num == 5:
                return (True, STEP5_SKIPPED_OUTPUT, 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=[],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        fixer_steps = [s for s in invoked if s in (6.1, 6.2, 6.3)]
        assert not fixer_steps, (
            "Step 5 'skipped' must not trigger the fixer — "
            f"invoked: {invoked}"
        )

    def test_skipped_status_refuses_push_of_dirty_files(self, tmp_path):
        # Even when a fixer DID somehow run and produced dirty files
        # (e.g. an earlier iteration before the skip happened, or a
        # tooling side-effect), the verification-skipped gate must
        # refuse the push because tests never validated the changes.
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (True, STEP5_SKIPPED_OUTPUT, 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            # An in-scope dirty file is present even though Step 5
            # skipped — the gate must still refuse.
            git_changed_files=["pdd/main.py"],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_not_called()
        assert success is False
        assert "verification skipped" in (msg or "").lower(), msg


class TestIssue1215Round9DiffSizeOversizedPathOnly:
    """Round-9 Finding 2: the diff-size gate must accept a small
    companion file (below OVERSIZED_PATH_ADDED_LOC_FLOOR) when the
    oversized file IS justified — the docs/prompt promise 'every
    oversized dirty path', not 'every dirty path'."""

    def test_small_companion_does_not_require_expansion_coverage(self, tmp_path, monkeypatch):
        # Default floor=50 lines. Big refactor on pdd/main.py (200
        # lines) IS justified; small companion tests/test_main.py (5
        # lines) is NOT — must still be allowed.
        monkeypatch.setenv("PDD_CHECKUP_DIFF_LOC_LIMIT", "100")

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 6.1:
                return (
                    True,
                    "FILES_MODIFIED: pdd/main.py, tests/test_main.py\n"
                    "EXPANSION_ITEMS: pdd/main.py — rewrite required because the "
                    "interface changed and the helper had to be refactored.\n",
                    0.1,
                    "model",
                )
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py", "tests/test_main.py"],
            commit_push_return=(True, "Pushed 2 files"),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10], \
             patch(
                 "pdd.agentic_checkup_orchestrator._diff_size_added_lines_by_path",
                 # pdd/main.py is over the per-path floor (50);
                 # tests/test_main.py is below it. Total = 205 > limit
                 # 100 — gate fires.
                 return_value={"pdd/main.py": 200, "tests/test_main.py": 5},
             ):
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_called_once()
        assert success is True, (
            "Small companion file must not block the push when the "
            f"oversized file is justified — msg={msg!r}"
        )

    def test_diffuse_overflow_with_no_oversized_path_still_requires_coverage(
        self, tmp_path, monkeypatch
    ):
        # Death-by-a-thousand-cuts: many small files together exceed
        # the limit but no single file is "oversized". Fallback to the
        # strict every-path rule.
        monkeypatch.setenv("PDD_CHECKUP_DIFF_LOC_LIMIT", "100")

        # All three paths are IN the PR's changed-file set (per
        # _PR_META_REAL_API) so the scope guard passes and the
        # diff-size gate is the one that fires.
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 6.1:
                # All 3 files are listed; only pdd/main.py is justified.
                return (
                    True,
                    "FILES_MODIFIED: pdd/main.py, pdd/new_feature.py, pdd/renamed.py\n"
                    "EXPANSION_ITEMS: pdd/main.py — needed because the PR "
                    "change reshaped the call graph.\n",
                    0.1,
                    "model",
                )
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=[
                "pdd/main.py", "pdd/new_feature.py", "pdd/renamed.py",
            ],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10], \
             patch(
                 "pdd.agentic_checkup_orchestrator._diff_size_added_lines_by_path",
                 # Each file is 40 lines (below the floor=50); total=120
                 # > limit=100. No single file is oversized → strict
                 # fallback applies and refuses because not every changed
                 # path is justified.
                 return_value={
                     "pdd/main.py": 40,
                     "pdd/new_feature.py": 40,
                     "pdd/renamed.py": 40,
                 },
             ):
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_not_called()
        assert success is False
        assert "diff size guard" in (msg or "").lower(), msg


class TestIssue1215Round10Step5SkippedEdgeCases:
    """Round-10: edge cases around the Step 5 verification-skipped gate.

    Finding 1 — provider returns success=False but the agent embedded
    ``status: skipped`` in its output. Fixer must NOT run; push must
    NOT happen.

    Finding 2 — ``status: skipped`` + clean worktree must NOT report
    success. Tests didn't run, so the checkup did not verify anything.

    Finding 3 — resume with persisted Step 5 skipped output but NO
    in-memory ``context['step5_verification_skipped']`` cache must
    still refuse push (the gate must re-derive from step_outputs).
    """

    def test_provider_failure_with_skipped_status_does_not_invoke_fixer(self, tmp_path):
        invoked = []

        # Note success=False on the provider call but the agent still
        # emitted a coherent ``status: skipped`` block.
        skipped_block = STEP5_SKIPPED_OUTPUT

        def step_side_effect(step_num, name, context, **kwargs):
            invoked.append(step_num)
            if step_num == 5:
                return (False, skipped_block, 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        fixer_steps = [s for s in invoked if s in (6.1, 6.2, 6.3)]
        assert not fixer_steps, (
            "Provider success=False + status:skipped must not run fixer — "
            f"invoked={invoked}"
        )
        push_mock.assert_not_called()
        assert success is False
        assert "verification skipped" in (msg or "").lower()

    def test_skipped_status_with_clean_worktree_does_not_report_success(self, tmp_path):
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (True, STEP5_SKIPPED_OUTPUT, 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        # Clean worktree (no fixer-produced changes).
        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=[],
            commit_push_return=(True, "No changes to push."),
            pr_metadata=dict(_PR_META_REAL_API),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_not_called()
        assert success is False, (
            "Clean worktree + status:skipped must NOT report success — "
            f"msg={msg!r}"
        )
        assert "verification skipped" in (msg or "").lower()

    def test_resume_with_skipped_step5_refuses_push_without_context_flag(self, tmp_path):
        """Cached step_outputs['5'] contains a skipped block, but
        ``context['step5_verification_skipped']`` was never persisted
        (mid-loop interruption). The gate must re-derive the truth from
        step_outputs and refuse the push."""
        wt = tmp_path / "wt"
        wt.mkdir(exist_ok=True)

        persisted_state = {
            "mode": "pr",
            "pr_number": 200,
            "pr_owner": "o",
            "pr_repo": "r",
            "pr_head_sha": "abc123deadbeef",
            "last_completed_step": 6.3,
            "current_step": 7,
            "step_outputs": {
                # Steps 1 and 2 must be present so the state-validation
                # loop doesn't truncate ``actual_last_success`` to 0 and
                # discard the cache (see the
                # state-correction-on-missing-keys path in
                # ``_run_agentic_checkup_orchestrator_inner``).
                "1": "out-1",
                "2": "out-2",
                "3": "clean",
                "4": "clean",
                "5": STEP5_SKIPPED_OUTPUT,
                # Persisted fixer outputs so fixer_invoked is True on
                # resume — without those the side-effect guard would
                # fire first and we'd never reach the skipped-gate.
                "6_1": "FILES_MODIFIED: pdd/main.py\n",
                "6_2": "verify-ok",
                "6_3": "review-ok",
            },
            # Crucially: no step5_verification_skipped key here.
            "context": {
                "files_to_stage": "pdd/main.py",
                "step5_output": STEP5_SKIPPED_OUTPUT,
                "step6_1_output": "FILES_MODIFIED: pdd/main.py\n",
            },
            "total_cost": 0.0,
            "last_model_used": "model",
            "fix_verify_iteration": 1,
            "previous_fixes": "",
            "posted_step_comments": [],
            "changed_files": ["pdd/main.py"],
        }

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        meta = dict(_PR_META_REAL_API)
        patches = (
            patch(
                "pdd.agentic_checkup_orchestrator._setup_pr_worktree",
                return_value=(wt, None),
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._fetch_pr_metadata",
                return_value=meta,
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._run_single_step",
                side_effect=step_side_effect,
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._git_changed_files",
                return_value=["pdd/main.py"],
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
                return_value=(True, "Pushed 1 file"),
            ),
            patch(
                "pdd.agentic_checkup_orchestrator.load_workflow_state",
                return_value=(persisted_state, "state.json"),
            ),
            patch(
                "pdd.agentic_checkup_orchestrator.save_workflow_state",
                return_value=None,
            ),
            patch("pdd.agentic_checkup_orchestrator.clear_workflow_state"),
            patch(
                "pdd.agentic_checkup_orchestrator._check_architecture_registry_edit_guard",
                return_value=None,
            ),
            patch(
                "pdd.agentic_checkup_orchestrator._check_prompt_source_guard",
                return_value=None,
            ),
            patch("pdd.agentic_checkup_orchestrator.console"),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path, "use_github_state": True}
            )

        push_mock.assert_not_called()
        assert success is False
        assert "verification skipped" in (msg or "").lower(), msg


class TestIssue1215Round10Step5StatusHelper:
    """Round-10: ``_step5_was_skipped`` re-derives state from a
    persisted Step 5 output, transparently handling the ``FAILED:``
    prefix that ``_handle_step_result`` prepends on failed steps."""

    def test_helper_recognises_skipped_in_failed_prefixed_output(self):
        from pdd.agentic_checkup_orchestrator import _step5_was_skipped

        prefixed = "FAILED: " + STEP5_SKIPPED_OUTPUT
        assert _step5_was_skipped(prefixed) is True

    def test_helper_returns_false_for_pass_status(self):
        from pdd.agentic_checkup_orchestrator import _step5_was_skipped

        assert _step5_was_skipped(STEP5_CLEAN_OUTPUT) is False

    def test_helper_returns_false_for_empty_output(self):
        from pdd.agentic_checkup_orchestrator import _step5_was_skipped

        assert _step5_was_skipped("") is False
        assert _step5_was_skipped("No structured block here at all.") is False


# Step 5 failure block declaring ``status: fail`` for the F1 stale-signal test.
STEP5_FAIL_OUTPUT = (
    "Tests failed.\n"
    "```failure_signal\n"
    "command: pytest -q\n"
    "exit_code: 1\n"
    "status: fail\n"
    "failing_ids: tests/test_main.py::test_iter1_only\n"
    "artifact_path: inline\n"
    "output: |\n"
    "  E   AssertionError: iteration-1 failure that must not survive\n"
    "  FAILED tests/test_main.py::test_iter1_only\n"
    "```"
)


class TestExternalReviewPR1215StaleSignalAndCleanup:
    """External review (PR #1215) follow-up:

    * Finding 1 — ``context['step5_failure_signal']`` is written only on the
      failing Step 5 path and never cleared, so a later iteration with a clean
      Step 5 can still drive the fixer with the previous failure block.
    * Finding 2 — the terminal success path discards ``clear_workflow_state``'s
      bool, so a failed remote-state clear is silently ignored and the next run
      can replay stale completed state.
    * Finding 3 — the provider-success/logical-failure branch hides the Step 5
      failure detail behind ``if not quiet``, leaving quiet automation with no
      concrete failing-test context.
    """

    def test_stale_step5_signal_cleared_when_later_iteration_is_clean(self, tmp_path):
        """FAILS_ON_CURRENT_CODE: iteration 1 fails Step 5, iteration 2 has a
        clean Step 5 but the fixer still runs (Step 3 dirty); the stale
        iteration-1 ``failure_signal`` block must NOT reach Step 6."""
        captured_iter2_step6: List[Dict] = []

        def step_side_effect(step_num, name, context, **kwargs):
            iteration = context.get("fix_verify_iteration", "1")
            if step_num == 3:
                # iter1 clean, iter2 dirty so the all-clean fixer skip does
                # NOT apply and Step 6 runs with iteration-2's clean Step 5.
                if iteration == "2":
                    return (False, "FAILED: build step regressed", 0.1, "model")
                return (True, "out-3", 0.0, "model")
            if step_num == 5:
                if iteration == "1":
                    return (False, STEP5_FAIL_OUTPUT, 0.1, "model")
                return (True, STEP5_CLEAN_OUTPUT, 0.1, "model")
            if step_num == 6.1:
                if iteration == "2":
                    captured_iter2_step6.append(dict(context))
                return (True, "FILES_MODIFIED: pdd/main.py", 0.1, "model")
            if step_num == 7:
                # iter1: not yet fixed -> loop continues to iteration 2.
                if iteration == "1":
                    return (True, "Issues remain.", 0.1, "model")
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            commit_push_return=(True, "Pushed 1 file"),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        assert captured_iter2_step6, "Step 6.1 must run in iteration 2"
        ctx = captured_iter2_step6[0]
        assert ctx.get("step5_failure_signal", "") == "", (
            "Iteration-2 Step 6 received a stale Step 5 failure_signal from "
            "iteration 1; it must be cleared once Step 5 is clean. Got: "
            f"{ctx.get('step5_failure_signal', '')!r}"
        )
        assert ctx.get("step5_failure_signal_missing", "") == "", (
            "step5_failure_signal_missing must also be cleared on a clean "
            "Step 5 iteration."
        )

    def test_success_path_warns_when_clear_workflow_state_unconfirmed(self, tmp_path):
        """FAILS_ON_CURRENT_CODE: the terminal success path must surface a
        warning when ``clear_workflow_state`` could not confirm the remote
        clear, while still returning success."""
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (True, STEP5_CLEAN_OUTPUT, 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=[],
        )
        # Replace the clear_workflow_state patch (index 7) with one that
        # reports an unconfirmed remote clear.
        with patches[0], patches[1], patches[2], patches[3], patches[4] as push_mock, \
             patches[5], patches[6], \
             patch(
                 "pdd.agentic_checkup_orchestrator.clear_workflow_state",
                 return_value=False,
             ), \
             patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**_PR_ARGS_1212, "cwd": tmp_path}
            )

        push_mock.assert_not_called()
        # The checkup itself succeeded — the cleanup miss is a warning, not a
        # verdict flip.
        assert success is True, msg
        assert "cleanup" in (msg or "").lower(), (
            "Terminal success path must append a workflow-state cleanup "
            f"warning when the remote clear is unconfirmed. Got: {msg!r}"
        )

    def test_completed_state_not_replayed_when_clear_failed(self, tmp_path):
        """FAILS_ON_CURRENT_CODE: a completed --no-fix --pr run whose terminal
        clear_workflow_state failed remotely leaves resumable state behind. The
        next run must re-verify (re-execute Step 5/Step 7) rather than skipping
        every step and replaying the cached Step 7 verdict as a clean result.

        Trap guard: the cached state's pr_head_sha MATCHES the current head, so
        the identity validator does NOT discard it — the completed-state guard
        is the only thing that can prevent the replay."""
        from unittest.mock import patch as _patch

        wt = tmp_path / "wt"
        wt.mkdir()
        stable_metadata = {
            "clone_url": "https://github.com/o/r.git",
            "head_ref": "change/test",
            "head_owner": "o",
            "head_repo": "r",
            "head_sha": "deadbeef0000",
        }

        per_run_calls: List[List] = []

        def make_run_step(sink):
            def run_step(step_num, _name, _ctx, **_kw):
                sink.append(step_num)
                if step_num == 5:
                    return (True, STEP5_CLEAN_OUTPUT, 0.0, "fake")
                if step_num == 7:
                    return (True, ALL_ISSUES_FIXED, 0.0, "fake")
                return (True, f"out-{step_num}", 0.0, "fake")
            return run_step

        common_args = dict(
            issue_url="https://github.com/o/r/issues/99",
            issue_content="stub",
            repo_owner="o",
            repo_name="r",
            issue_number=99,
            issue_title="stub",
            architecture_json="{}",
            pddrc_content="",
            cwd=tmp_path,
            verbose=False,
            quiet=True,
            no_fix=True,
            timeout_adder=0.0,
            # use_github_state=False keeps load/save against the REAL local
            # state file so the completed state persists between runs.
            use_github_state=False,
            pr_url="https://github.com/o/r/pull/200",
            pr_owner="o",
            pr_repo="r",
            pr_number=200,
        )

        # clear_workflow_state is a no-op returning False — simulates a failed
        # remote clear that leaves the saved state behind. load/save are REAL.
        for _run in range(2):
            sink: List = []
            per_run_calls.append(sink)
            with (
                _patch("pdd.agentic_checkup_orchestrator._setup_pr_worktree", return_value=(wt, None)),
                _patch("pdd.agentic_checkup_orchestrator._fetch_pr_metadata", return_value=stable_metadata),
                _patch("pdd.agentic_checkup_orchestrator.clear_workflow_state", return_value=False),
                _patch("pdd.agentic_checkup_orchestrator._run_single_step", side_effect=make_run_step(sink)),
            ):
                success, _msg, _cost, _model = run_agentic_checkup_orchestrator(**common_args)
            assert success is True, _msg

        # Run 1 verified normally. Run 2 must NOT be a stale-state replay — it
        # must re-execute Step 5 and Step 7 instead of skipping every step.
        assert 5 in per_run_calls[1] and 7 in per_run_calls[1], (
            "Second run replayed completed cached state without re-verifying "
            f"(steps executed on run 2: {sorted(set(per_run_calls[1]))}). A "
            "completed run's state must be discarded on load when its terminal "
            "cleanup did not remove it."
        )

    def test_step7_no_duplicate_per_step_comment_in_pr_mode(self, tmp_path):
        """FAILS_ON_CURRENT_CODE: in PR mode the orchestrator owns the single
        canonical Step 7 report (_post_pr_mode_final_report); _handle_step_result
        must NOT also post a per-step Step 7 issue comment, or the issue thread
        gets duplicate Step 7 reporting (prompt contract: 'Step 7 must not post
        GitHub comments in PR mode')."""
        from unittest.mock import patch as _patch

        posted_keys: List[int] = []

        def fake_post_once(*_args, step_num=None, **_kwargs):
            posted_keys.append(step_num)

        def step_side_effect(step_num, name, context, **kwargs):
            # Step 5 fails so the fixer + Step 7 verify path runs end-to-end.
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 6.1:
                return (True, "FILES_MODIFIED: pdd/main.py", 0.1, "model")
            if step_num == 7:
                return (
                    True,
                    "<step_report>Step 7 verified.</step_report>\n" + ALL_ISSUES_FIXED,
                    0.1,
                    "model",
                )
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            commit_push_return=(True, "Pushed 1 file"),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], \
             patches[10], \
             _patch(
                 "pdd.agentic_checkup_orchestrator.post_step_comment_once",
                 side_effect=fake_post_once,
             ):
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        # _step_comment_key projects step 7 to (iteration*10000 + 70), so a
        # Step 7 per-step comment is any posted key with key % 10000 == 70.
        step7_keys = [k for k in posted_keys if k is not None and k % 10000 == 70]
        assert not step7_keys, (
            "Step 7 must not post a per-step issue comment in PR mode — the "
            "orchestrator's canonical final report already covers Step 7. "
            f"Saw Step 7 comment key(s): {step7_keys}"
        )

    def test_provider_success_logical_failure_detail_visible_in_quiet(self, tmp_path):
        """FAILS_ON_CURRENT_CODE: when Step 5 reports provider success but its
        ``failure_signal`` block declares ``status: fail``, the failing-test
        detail must be printed even under ``quiet=True`` (matching the
        unconditional print on the provider-failure path)."""
        step5_output = (
            "Provider call returned success.\n"
            "```failure_signal\n"
            "command: pytest -q\n"
            "exit_code: 1\n"
            "status: fail\n"
            "failing_ids: tests/test_main.py::test_quiet_path\n"
            "artifact_path: inline\n"
            "output: |\n"
            "  E   AssertionError: quiet-mode failure detail\n"
            "  FAILED tests/test_main.py::test_quiet_path\n"
            "```"
        )

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                # Provider SUCCESS, but the block declares a logical failure.
                return (True, step5_output, 0.1, "model")
            if step_num == 6.1:
                return (True, "FILES_MODIFIED: pdd/main.py", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            commit_push_return=(True, "Pushed 1 file"),
        )
        # _PR_ARGS_1212 sets quiet=True.
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], \
             patches[10] as mc:
            run_agentic_checkup_orchestrator(**{**_PR_ARGS_1212, "cwd": tmp_path})

        all_printed = " ".join(
            str(arg) for call_obj in mc.print.call_args_list for arg in call_obj.args
        )
        assert (
            "quiet-mode failure detail" in all_printed
            or "test_quiet_path" in all_printed
        ), (
            "Step 5 provider-success/logical-failure detail must be printed "
            "even in quiet mode so automation sees the failing-test context."
        )


class TestNumstatRenameParsing:
    """Issue #1212 follow-up: the diff-size probe must resolve git's
    ``git diff --numstat`` rename rows (``old => new`` and the brace form
    ``dir/{old => new}/f.py``) to the post-rename path. The earlier code
    only stripped ``" -> "`` — a shape numstat never emits — so renamed
    files were keyed by the raw ``old => new`` string and could never be
    matched to a justified EXPANSION_ITEMS entry by the diff-size gate.
    """

    @pytest.mark.parametrize(
        "raw,expected",
        [
            ("old.py => new.py", "new.py"),
            ("sub/deep.py => deep2.py", "deep2.py"),
            ("dir/{old => new}/f.py", "dir/new/f.py"),
            ("{old => new}", "new"),
            ("pkg/{a/b => c}/x.py", "pkg/c/x.py"),
            ("plain.py", "plain.py"),
            ("old.py -> new.py", "new.py"),
        ],
    )
    def test_numstat_rename_dest_forms(self, raw: str, expected: str) -> None:
        from pdd.agentic_checkup_orchestrator import _numstat_rename_dest

        assert _numstat_rename_dest(raw) == expected

    def test_diff_size_probe_keys_rename_by_post_rename_path(self, tmp_path: Path) -> None:
        """End-to-end against a real git repo: a renamed-and-edited file is
        recorded under its destination path (not ``old => new``)."""
        from pdd.agentic_checkup_orchestrator import _diff_size_added_lines_by_path

        def run(*args: str) -> None:
            subprocess.run(
                args, cwd=tmp_path, check=True, capture_output=True
            )

        run("git", "init", "-q")
        run("git", "config", "user.email", "t@t.com")
        run("git", "config", "user.name", "t")
        (tmp_path / "to_rename.py").write_text("orig\nline\nhere\n")
        run("git", "add", "-A")
        run("git", "commit", "-qm", "init")
        run("git", "mv", "to_rename.py", "renamed.py")
        (tmp_path / "renamed.py").write_text("orig\nline\nhere\nADDED\n")

        per_path = _diff_size_added_lines_by_path(tmp_path)
        assert per_path is not None
        assert "renamed.py" in per_path, per_path
        assert per_path["renamed.py"] == 1, per_path
        assert not any("=>" in key for key in per_path), per_path


# ---------------------------------------------------------------------------
# Issue #1292: _step7_passed must drop the issue_aligned gate in no-issue
# PR mode (review the PR on its own merits), while keeping it for PR+issue.
# ---------------------------------------------------------------------------


class TestStep7PassedMeritReview:
    """The Step 7 verdict gate under #1292's optional-issue PR mode."""

    MERIT_VERDICT = (
        '```json\n'
        '{"success": true, "message": "ok", "issues": [], "changed_files": []}\n'
        '```'
    )
    CRITICAL_VERDICT = (
        '```json\n'
        '{"success": true, "message": "bug", '
        '"issues": [{"severity": "critical", "fixed": false, '
        '"description": "null deref", "module": "x.py"}]}\n'
        '```'
    )
    TARGETED_OUT_OF_DIFF_VERDICT = (
        '```json\n'
        '{"success": true, '
        '"message": "Verification scope: targeted — full suite not run. '
        'Project-wide build issues remain but are outside PR scope.", '
        '"issue_aligned": true, '
        '"issues": [{"severity": "critical", "fixed": false, '
        '"description": "tsc fails because src is missing", '
        '"module": "frontend", "file": "frontend/"}], '
        '"changed_files": ["docs/checkup.md"]}\n'
        '```'
    )
    TARGETED_OUT_OF_DIFF_EXPLICITLY_NONBLOCKING_VERDICT = (
        '```json\n'
        '{"success": true, '
        '"message": "Verification scope: targeted — full suite not run.", '
        '"issue_aligned": true, '
        '"issues": [{"severity": "critical", "fixed": false, '
        '"description": "pre-existing tsc baseline failure", '
        '"module": "frontend", "file": "frontend/", '
        '"scope": "out-of-scope", '
        '"out_of_scope_reason": "pre-existing baseline failure outside this PR diff"}], '
        '"changed_files": ["docs/checkup.md"]}\n'
        '```'
    )
    TARGETED_OUT_OF_DIFF_NONBLOCKING_NO_REASON_VERDICT = (
        '```json\n'
        '{"success": true, '
        '"message": "Verification scope: targeted — full suite not run.", '
        '"issue_aligned": true, '
        '"issues": [{"severity": "critical", "fixed": false, '
        '"description": "frontend/src/ missing; TS18003 no inputs found", '
        '"module": "frontend", "file": "frontend/tsconfig.json", '
        '"scope": "out-of-scope"}], '
        '"changed_files": ["README.md"]}\n'
        '```'
    )
    TARGETED_BLOCKING_FALSE_NO_REASON_VERDICT = (
        '```json\n'
        '{"success": true, '
        '"message": "Verification scope: targeted — full suite not run.", '
        '"issue_aligned": true, '
        '"issues": [{"severity": "critical", "fixed": false, '
        '"description": "pre-existing baseline failure", '
        '"module": "frontend", "file": "frontend/tsconfig.json", '
        '"blocking": false}], '
        '"changed_files": ["README.md"]}\n'
        '```'
    )
    FULL_ATTEMPT_OUT_OF_SCOPE_NONBLOCKING_VERDICT = (
        '```json\n'
        '{"success": true, '
        '"message": "Verification scope: full suite attempted — Python passed; '
        'frontend TS18003 is pre-existing and outside the PR diff.", '
        '"issue_aligned": true, '
        '"issues": [{"severity": "critical", "fixed": false, '
        '"description": "frontend/src/ missing; TS18003 no inputs found", '
        '"module": "frontend", "file": "frontend/tsconfig.json", '
        '"scope": "out-of-scope", "blocking": false}], '
        '"changed_files": ["README.md"]}\n'
        '```'
    )
    TARGETED_CHANGED_FILE_CRITICAL_VERDICT = (
        '```json\n'
        '{"success": true, '
        '"message": "Verification scope: targeted — full suite not run.", '
        '"issue_aligned": true, '
        '"issues": [{"severity": "critical", "fixed": false, '
        '"description": "package is invalid", '
        '"module": "frontend", "file": "frontend/package.json"}], '
        '"changed_files": ["frontend/package.json"]}\n'
        '```'
    )
    # An in-scope PR critical with only a *generic* ``reason`` field (ordinary
    # explanatory text, not a non-blocking declaration) must still block.
    TARGETED_IN_SCOPE_CRITICAL_GENERIC_REASON_VERDICT = (
        '```json\n'
        '{"success": true, '
        '"message": "Verification scope: targeted — full suite not run.", '
        '"issue_aligned": true, '
        '"issues": [{"severity": "critical", "fixed": false, '
        '"description": "introduced token leak", '
        '"module": "auth", "file": "auth.py", '
        '"scope": "pr-diff", "in_scope": true, '
        '"reason": "introduced token leak"}], '
        '"changed_files": ["auth.py"]}\n'
        '```'
    )
    # A critical that lives in the PR diff (its file is a changed file) with
    # only a blocking:false flag and NO out-of-scope signal must still block —
    # a self-reported non-blocking flag cannot wave through a PR-introduced
    # critical (#1574 review, fail-closed).
    TARGETED_CHANGED_FILE_BLOCKING_FALSE_VERDICT = (
        '```json\n'
        '{"success": true, '
        '"message": "Verification scope: targeted — full suite not run.", '
        '"issue_aligned": true, '
        '"issues": [{"severity": "critical", "fixed": false, '
        '"description": "PR-introduced token leak", '
        '"module": "auth", "file": "auth.py", '
        '"blocking": false}], '
        '"changed_files": ["auth.py"]}\n'
        '```'
    )

    def test_issue_aligned_required_when_issue_present(self):
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, reason = _step7_passed(
            self.MERIT_VERDICT, pr_mode=True, has_issue=True
        )
        assert not passed
        assert "issue_aligned" in reason

    def test_issue_aligned_dropped_when_no_issue(self):
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, reason = _step7_passed(
            self.MERIT_VERDICT, pr_mode=True, has_issue=False
        )
        assert passed, reason

    def test_merit_review_still_gates_unfixed_critical(self):
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, reason = _step7_passed(
            self.CRITICAL_VERDICT, pr_mode=True, has_issue=False
        )
        assert not passed
        assert "critical" in reason.lower()

    def test_has_issue_defaults_true_preserves_legacy_behavior(self):
        """Omitting has_issue must behave like today's PR+issue gate."""
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, _ = _step7_passed(self.MERIT_VERDICT, pr_mode=True)
        assert not passed  # issue_aligned still required by default

    def test_targeted_pr_blocks_out_of_diff_critical_without_structured_reason(self):
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, reason = _step7_passed(
            self.TARGETED_OUT_OF_DIFF_VERDICT,
            pr_mode=True,
            has_issue=True,
            pr_test_scope="targeted",
        )
        assert not passed
        assert "critical" in reason.lower()

    def test_targeted_pr_blocks_in_scope_critical_with_generic_reason(self):
        """A generic ``reason`` field must not bypass an in-scope PR critical.

        Regression for the #1574 review: a critical with ``scope: "pr-diff"``,
        ``in_scope: true`` and only an explanatory ``reason`` (no non-blocking
        flag/scope/``*_reason``) must still block the PR.
        """
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, reason = _step7_passed(
            self.TARGETED_IN_SCOPE_CRITICAL_GENERIC_REASON_VERDICT,
            pr_mode=True,
            has_issue=True,
            pr_test_scope="targeted",
        )
        assert not passed
        assert "critical" in reason.lower()

    def test_targeted_pr_allows_explicit_nonblocking_out_of_scope_critical(self):
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, reason = _step7_passed(
            self.TARGETED_OUT_OF_DIFF_EXPLICITLY_NONBLOCKING_VERDICT,
            pr_mode=True,
            has_issue=True,
            pr_test_scope="targeted",
        )
        assert passed, reason

    def test_targeted_pr_allows_out_of_scope_critical_without_reason(self):
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, reason = _step7_passed(
            self.TARGETED_OUT_OF_DIFF_NONBLOCKING_NO_REASON_VERDICT,
            pr_mode=True,
            has_issue=True,
            pr_test_scope="targeted",
        )
        assert passed, reason

    def test_targeted_pr_allows_blocking_false_critical_without_reason(self):
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, reason = _step7_passed(
            self.TARGETED_BLOCKING_FALSE_NO_REASON_VERDICT,
            pr_mode=True,
            has_issue=True,
            pr_test_scope="targeted",
        )
        assert passed, reason

    def test_full_pr_scope_allows_explicit_nonblocking_out_of_scope_critical(self):
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, reason = _step7_passed(
            self.FULL_ATTEMPT_OUT_OF_SCOPE_NONBLOCKING_VERDICT,
            pr_mode=True,
            has_issue=True,
            pr_test_scope="full",
        )
        assert passed, reason

    def test_targeted_pr_blocks_changed_file_critical_with_blocking_false(self):
        """A blocking:false flag must not wave through a PR-introduced critical.

        Fail-closed regression (#1574 review): a critical whose file is in the
        PR diff blocks even when tagged ``blocking: false``, because there is no
        out-of-scope signal and the finding touches a changed file.
        """
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, reason = _step7_passed(
            self.TARGETED_CHANGED_FILE_BLOCKING_FALSE_VERDICT,
            pr_mode=True,
            has_issue=True,
            pr_test_scope="targeted",
        )
        assert not passed
        assert "critical" in reason.lower()

    def test_full_pr_scope_blocks_changed_file_critical_with_blocking_false(self):
        """The fail-closed rule also holds in full PR scope."""
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, reason = _step7_passed(
            self.TARGETED_CHANGED_FILE_BLOCKING_FALSE_VERDICT,
            pr_mode=True,
            has_issue=True,
            pr_test_scope="full",
        )
        assert not passed
        assert "critical" in reason.lower()

    def test_targeted_pr_still_blocks_changed_file_critical(self):
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, reason = _step7_passed(
            self.TARGETED_CHANGED_FILE_CRITICAL_VERDICT,
            pr_mode=True,
            has_issue=True,
            pr_test_scope="targeted",
        )
        assert not passed
        assert "package is invalid" in reason

    def test_full_pr_scope_still_blocks_critical_without_nonblocking_signal(self):
        from pdd.agentic_checkup_orchestrator import _step7_passed

        passed, reason = _step7_passed(
            self.TARGETED_OUT_OF_DIFF_VERDICT,
            pr_mode=True,
            has_issue=True,
            pr_test_scope="full",
        )
        assert not passed
        assert "critical" in reason.lower()


class TestNoIssuePrModePosting:
    """#1292: in no-issue PR mode the PR is the only comment thread.

    Per-step progress posts (`post_step_comment_once`) and the duplicate
    issue-thread final report (`post_step_comment`) are suppressed; exactly
    one canonical report lands on the PR via `post_pr_comment`. With a real
    issue, the legacy dual-thread behaviour is preserved.
    """

    def _run(self, tmp_path, *, has_issue: bool):
        from unittest.mock import patch as _patch

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, "FAILED: tests/test_main.py::test_x", 0.1, "model")
            if step_num == 6.1:
                return (True, "FILES_MODIFIED: pdd/main.py", 0.1, "model")
            if step_num == 7:
                return (
                    True,
                    "<step_report>ok</step_report>\n" + ALL_ISSUES_FIXED,
                    0.1,
                    "model",
                )
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _pr_patches_1212(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
            commit_push_return=(True, "Pushed 1 file"),
        )
        args = {**_PR_ARGS_1212, "use_github_state": True, "cwd": tmp_path}
        if not has_issue:
            # run_agentic_checkup aliases the thread to the PR and blanks the
            # issue context when there is no source issue.
            args.update(
                issue_url="",
                issue_content="",
                issue_title="",
                issue_number=args["pr_number"],
            )

        per_step: List = []
        final_issue: List = []
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], \
             patches[10], \
             _patch(
                 "pdd.agentic_checkup_orchestrator.post_step_comment_once",
                 side_effect=lambda *a, **k: per_step.append(k.get("step_num")) or True,
             ), \
             _patch(
                 "pdd.agentic_checkup_orchestrator.post_step_comment",
                 side_effect=lambda *a, **k: final_issue.append(1) or True,
             ), \
             _patch(
                 "pdd.agentic_checkup_orchestrator.post_pr_comment",
                 return_value=True,
             ) as ppc:
            run_agentic_checkup_orchestrator(**args)
        return per_step, final_issue, ppc

    def test_no_issue_suppresses_progress_and_dup_final_report(self, tmp_path):
        per_step, final_issue, ppc = self._run(tmp_path, has_issue=False)
        # Exactly one canonical report, posted to the PR thread.
        assert ppc.call_count == 1, f"expected 1 PR comment, got {ppc.call_count}"
        # The issue-thread final report is skipped (it would duplicate the PR post).
        assert final_issue == [], (
            f"issue-thread final report must be skipped with no issue, "
            f"saw {len(final_issue)}"
        )
        # No per-step progress comments — they would flood the PR thread.
        assert per_step == [], (
            f"per-step progress posts must be suppressed with no issue, saw {per_step}"
        )

    def test_with_issue_keeps_progress_and_dual_final_report(self, tmp_path):
        per_step, final_issue, ppc = self._run(tmp_path, has_issue=True)
        # Behaviour unchanged: per-step progress posts to the issue thread...
        assert per_step, "with a source issue, per-step progress comments must still post"
        # ...and the final report posts to BOTH the PR and the issue thread.
        assert ppc.call_count == 1
        assert final_issue, "with a source issue, the issue-thread final report must still post"


class TestSetupWorktreeStaleBranch:
    """Regression for: checkup fails when a stale ``checkup/issue-*`` branch
    already exists. A crashed/cleaned-up prior run can leave the branch
    registered to a worktree directory that no longer exists; ``git branch -D``
    then refuses ("checked out at <gone path>") and the subsequent
    ``git worktree add -b`` fails with "a branch named ... already exists",
    failing the whole checkup. ``_setup_worktree`` now prunes stale worktree
    registrations first, and — when the branch still cannot be deleted — reuses
    it via a forced worktree add instead of hard-failing (issue #1281 contract).
    """

    @staticmethod
    def _init_repo(path: Path):
        def git(*args):
            return subprocess.run(
                ["git", *args], cwd=path, capture_output=True, text=True
            )
        git("init", "-q")
        git("config", "user.email", "t@x")
        git("config", "user.name", "t")
        (path / "f.txt").write_text("x\n")
        git("add", ".")
        git("commit", "-q", "-m", "init")
        return git

    def test_stale_branch_from_removed_worktree_is_recreated(self, tmp_path):
        import shutil
        from pdd.agentic_checkup_orchestrator import _setup_worktree

        git = self._init_repo(tmp_path)
        # Branch left registered to a worktree dir that is then removed out of band.
        stale = tmp_path / "old-wt"
        git("worktree", "add", "-q", "-b", "checkup/issue-7", str(stale), "HEAD")
        shutil.rmtree(stale)

        wt, err = _setup_worktree(tmp_path, issue_number=7, quiet=True, resume_existing=False)
        assert err is None, err
        assert wt is not None and wt.exists()

    def test_plain_leftover_branch_is_recreated(self, tmp_path):
        from pdd.agentic_checkup_orchestrator import _setup_worktree

        git = self._init_repo(tmp_path)
        git("branch", "checkup/issue-3")  # leftover ref, not checked out anywhere

        wt, err = _setup_worktree(tmp_path, issue_number=3, quiet=True, resume_existing=False)
        assert err is None, err
        assert wt is not None and wt.exists()

    def test_branch_still_checked_out_recovers_via_forced_reuse(self, tmp_path):
        # When the branch cannot be deleted because it is still checked out in
        # another worktree, checkup must NOT hard-fail: it reuses the existing
        # branch via a forced worktree add (issue #1281 / #1299 contract:
        # "_delete_branch failure does not hard fail").
        from pdd.agentic_checkup_orchestrator import _setup_worktree

        git = self._init_repo(tmp_path)
        live = tmp_path / "live-wt"
        git("worktree", "add", "-q", "-b", "checkup/issue-9", str(live), "HEAD")

        wt, err = _setup_worktree(tmp_path, issue_number=9, quiet=True, resume_existing=False)
        assert err is None, err
        assert wt is not None and wt.exists()
        # The checkup worktree is checked out on the reused branch.
        head = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            cwd=wt, capture_output=True, text=True,
        ).stdout.strip()
        assert head == "checkup/issue-9", head


class TestCompanionSourceOfTruthPaths2047:
    """``_companion_source_of_truth_paths`` admits owning prompts of PR-diff code (#2047)."""

    def test_admits_owning_prompt_and_arch_for_pr_code(self, monkeypatch) -> None:
        import pdd.agentic_checkup_orchestrator as orch

        monkeypatch.setattr(
            orch,
            "_load_prompt_source_map",
            lambda _wt: {
                "pdd/foo.py": "pdd/prompts/foo_python.prompt",
                "pdd/bar.py": "pdd/prompts/bar_python.prompt",
            },
        )
        # Only foo.py is in the PR diff -> only foo's prompt is admitted.
        out = orch._companion_source_of_truth_paths(Path("/x"), {"pdd/foo.py"})
        assert out == {"pdd/prompts/foo_python.prompt", "architecture.json"}

    def test_unrelated_prompt_not_admitted(self, monkeypatch) -> None:
        import pdd.agentic_checkup_orchestrator as orch

        monkeypatch.setattr(
            orch,
            "_load_prompt_source_map",
            lambda _wt: {"pdd/foo.py": "pdd/prompts/foo_python.prompt"},
        )
        # PR touches only an unregistered file -> no companion prompt admitted,
        # so an arbitrary prompt edit still trips the scope guard.
        out = orch._companion_source_of_truth_paths(Path("/x"), {"pdd/unrelated.py"})
        assert out == set()

    def test_no_registry_returns_empty(self, monkeypatch) -> None:
        import pdd.agentic_checkup_orchestrator as orch

        monkeypatch.setattr(orch, "_load_prompt_source_map", lambda _wt: None)
        assert orch._companion_source_of_truth_paths(Path("/x"), {"pdd/foo.py"}) == set()
