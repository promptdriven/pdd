"""Reproduction tests for GitHub issue #1212.

pdd checkup --pr hides test failures, lets fixer push unrelated code, never converges.

Root causes (per issue analysis):
  Bug 1 — Step 5 failure detail is not surfaced to the user (only generic warning logged).
  Bug 2 — Step 6 fixer has no scope guard; can create files outside the PR's changed-file set.
  Bug 3 — Step 7 verifier is non-discriminating; passes without causal-connection check.
  Bug 5 — Fixer (steps 6.1/6.2/6.3) always runs even when Step 5 is clean.

Tests marked FAILS_ON_CURRENT_CODE assert the CORRECT/expected behaviour.
They will FAIL on the current buggy code and PASS once the bug is fixed.
Tests marked PASSES_ON_CURRENT_CODE confirm existing correct behaviour
that should not regress.

See: https://github.com/promptdriven/pdd/issues/1212
"""
from __future__ import annotations

from pathlib import Path
from typing import Dict, List, Optional
from unittest.mock import MagicMock, call, patch

import pytest

from pdd.agentic_checkup_orchestrator import run_agentic_checkup_orchestrator

# ---------------------------------------------------------------------------
# Shared constants (mirrors test_agentic_checkup_orchestrator.py)
# ---------------------------------------------------------------------------

STEP7_VERDICT_JSON = (
    '```json\n'
    '{"success": true, "message": "ok", "issue_aligned": true, '
    '"issues": [], "changed_files": []}\n'
    '```'
)
ALL_ISSUES_FIXED = f"All Issues Fixed\n{STEP7_VERDICT_JSON}"

STABLE_PR_METADATA = {
    "clone_url": "https://github.com/o/r.git",
    "head_ref": "change/fix",
    "head_owner": "o",
    "head_repo": "r",
    "head_sha": "abc123deadbeef",
    # PR's original changed files — this is what Step 5 / Step 7 use for scope
    "api_changed_files": "- M: pdd/main.py\n- M: tests/test_main.py",
    "api_changed_files_full": "- M: pdd/main.py\n- M: tests/test_main.py",
}

PR_ARGS = {
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


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_pr_mode_patches(
    tmp_path: Path,
    *,
    step_side_effect,
    git_changed_files: Optional[List[str]] = None,
    commit_push_return=(True, "No changes to commit"),
    pr_metadata: Optional[Dict] = None,
):
    """Return a list of patchers for a PR-fix-mode orchestrator run.

    Yields (mock_run_single_step, mock_commit_push, mock_console) inside
    ``with _make_pr_mode_patches(...) as (step_mock, push_mock, console_mock)``.
    """
    wt = tmp_path / "wt"
    wt.mkdir()
    meta = pr_metadata if pr_metadata is not None else dict(STABLE_PR_METADATA)

    return (
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
            return_value=git_changed_files or [],
        ),
        patch(
            "pdd.agentic_checkup_orchestrator._commit_and_push_if_changed",
            return_value=commit_push_return,
        ),
        patch("pdd.agentic_checkup_orchestrator.load_workflow_state", return_value=(None, None)),
        patch("pdd.agentic_checkup_orchestrator.save_workflow_state", return_value=None),
        patch("pdd.agentic_checkup_orchestrator.clear_workflow_state"),
        patch("pdd.agentic_checkup_orchestrator._check_architecture_registry_edit_guard",
              return_value=None),
        patch("pdd.agentic_checkup_orchestrator._check_prompt_source_guard", return_value=None),
        patch("pdd.agentic_checkup_orchestrator.console"),
    )


# ---------------------------------------------------------------------------
# Bug 1 — Step 5 failure signal propagation
# ---------------------------------------------------------------------------


class TestBug1Step5FailureSignalPropagation:
    """Bug 1: Step 5 failure output must flow to Step 6's context and user-visible logs."""

    def test_step5_failure_output_in_step6_context(self, tmp_path):
        """Step 5 failure output IS stored in context and passed to Step 6's prompt.

        PASSES_ON_CURRENT_CODE: context["step5_output"] is correctly set to the raw
        step 5 output (including failure text), so Step 6's prompt receives it.
        This partial fix is already present; this test must not regress.
        """
        step5_failure_text = "FAILED: test_foo.py::test_bar - AssertionError: got None"
        captured_step6_contexts = []

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, step5_failure_text, 0.1, "model")
            if step_num == 6.1:
                # Capture the context Step 6 sees
                captured_step6_contexts.append(dict(context))
                return (True, "FILES_MODIFIED: pdd/main.py", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _make_pr_mode_patches(tmp_path, step_side_effect=step_side_effect)
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**PR_ARGS, "cwd": tmp_path})

        assert captured_step6_contexts, "Step 6.1 should have been invoked"
        ctx = captured_step6_contexts[0]
        # Step 5 failure text must reach Step 6's context
        assert "step5_output" in ctx
        # The failure text should be prefixed with FAILED: because success=False
        assert "FAILED:" in ctx["step5_output"]
        assert "test_foo.py" in ctx["step5_output"]

    def test_step5_failure_logged_visibly_not_only_as_warning(self, tmp_path):
        """When Step 5 fails, its actual failure content should be logged to the console.

        FAILS_ON_CURRENT_CODE: Currently the orchestrator only prints a generic yellow
        warning "Warning: Step 5 reported failure, but proceeding as no hard stop
        condition met." The actual pytest output / failure detail is never shown.
        Expected: the actual failure output is also printed so operators can see what
        tests failed without having to dig through internal state.
        """
        step5_failure_text = (
            "FAILED tests/test_main.py::test_critical_path - AssertionError\n"
            "short test summary info\n"
            "FAILED tests/test_main.py::test_critical_path"
        )
        console_messages = []

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, step5_failure_text, 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _make_pr_mode_patches(tmp_path, step_side_effect=step_side_effect)
        mock_console = patches[10]

        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], mock_console as mc:
            run_agentic_checkup_orchestrator(**{**PR_ARGS, "cwd": tmp_path})

        # Collect all text passed to console.print
        all_printed = " ".join(
            str(c) for call_obj in mc.print.call_args_list for c in call_obj.args
        )

        # The actual failure content (test IDs, FAILED lines) must appear in the log,
        # not just the generic warning message.
        # This assertion FAILS on current code because only the generic warning is logged.
        assert "test_critical_path" in all_printed or "FAILED tests" in all_printed, (
            "Step 5 failure detail (failing test IDs/paths) must be printed to the console "
            "so operators can see what failed. Currently only a generic warning is shown."
        )


# ---------------------------------------------------------------------------
# Bug 2 — Step 6 fixer scope guard
# ---------------------------------------------------------------------------


class TestBug2FixerScopeGuard:
    """Bug 2: Step 6 fixer must be constrained to the PR's existing changed-file set."""

    def test_fixer_out_of_scope_files_rejected_before_push(self, tmp_path):
        """Fixer files outside the PR's changed-file set must be rejected before push.

        FAILS_ON_CURRENT_CODE: The orchestrator currently has no scope guard comparing
        `_git_changed_files(worktree)` against `pr_metadata["api_changed_files"]`.
        The fixer can create 6866 lines of unrelated plugin code and it gets pushed.

        Expected behavior: when `_git_changed_files()` returns files that are NOT in the
        PR's original `api_changed_files`, the orchestrator must refuse the push and
        return an error indicating the scope violation.

        Acceptance criterion from issue #1212:
          "A test asserts that a Step 6 fixer producing files outside the PR's existing
          changed-file set is rejected (or routed through an explicit expansion path)
          before commit."
        """
        # PR originally changed only pdd/main.py and tests/test_main.py
        # The fixer created 14 unrelated security plugin files
        out_of_scope_files = [
            "plugins/security-guidance/README.md",
            "plugins/security-guidance/rules/xss.yaml",
            "plugins/security-guidance/rules/sqli.yaml",
        ]

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _make_pr_mode_patches(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=out_of_scope_files,  # fixer touched out-of-scope files
        )
        mock_push = patches[4]

        with patches[0], patches[1], patches[2], patches[3], mock_push as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**PR_ARGS, "cwd": tmp_path}
            )

        # The orchestrator must NOT push when out-of-scope files were added.
        # On current code, push IS called because there is no scope guard.
        push_mock.assert_not_called(), (
            "push must not be called when the fixer introduced files outside the "
            f"PR's changed-file set. Out-of-scope files: {out_of_scope_files}"
        )
        # The failure message should mention the scope issue
        assert success is False, (
            "The orchestrator should return failure when out-of-scope files are found"
        )

    def test_fixer_scope_guard_allows_in_scope_files(self, tmp_path):
        """Fixer changes that stay within the PR's changed-file set are allowed.

        PASSES_ON_CURRENT_CODE (positive case): When the fixer only modifies files
        already in the PR's api_changed_files, the push should proceed normally.
        This is the positive counterpart to test_fixer_out_of_scope_files_rejected.
        """
        # PR originally changed pdd/main.py and tests/test_main.py
        # Fixer only modified those same files — fully in scope
        in_scope_files = ["pdd/main.py", "tests/test_main.py"]

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _make_pr_mode_patches(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=in_scope_files,
            commit_push_return=(True, "Pushed 2 files to PR branch"),
        )
        mock_push = patches[4]

        with patches[0], patches[1], patches[2], patches[3], mock_push as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**PR_ARGS, "cwd": tmp_path}
            )

        # In-scope changes should be pushed (positive case)
        push_mock.assert_called_once(), (
            "In-scope fixer changes (files already in PR) should be committed and pushed"
        )


# ---------------------------------------------------------------------------
# Bug 3 — Step 7 non-discriminating verifier
# ---------------------------------------------------------------------------


class TestBug3Step7NonDiscriminatingVerifier:
    """Bug 3: Step 7 must verify causal connection between fixer diff and Step 5 failure."""

    def test_step7_context_contains_step5_failure_and_fixer_files(self, tmp_path):
        """Step 7 context must include both Step 5 failure output and fixer changed files.

        PASSES_ON_CURRENT_CODE (mechanical plumbing): The context flowing to Step 7
        already contains step5_output (FAILED: prefix) and files_to_stage (from
        FILES_CREATED/FILES_MODIFIED parsing). This plumbing is already correct.
        This test ensures it does not regress.
        """
        step5_failure = (
            "FAILED pdd/main.py::test_import - ImportError: cannot import name 'foo'"
        )
        captured_step7_contexts = []

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, step5_failure, 0.1, "model")
            if step_num == 6.1:
                return (True, "FILES_MODIFIED: pdd/main.py", 0.1, "model")
            if step_num == 7:
                captured_step7_contexts.append(dict(context))
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _make_pr_mode_patches(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=["pdd/main.py"],
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**PR_ARGS, "cwd": tmp_path})

        assert captured_step7_contexts, "Step 7 should have been invoked"
        ctx = captured_step7_contexts[0]
        # Step 5 failure output must be in Step 7's context (raw output, no FAILED: prefix)
        assert "step5_output" in ctx
        # The raw step5 output contains the failure text
        assert "pdd/main.py" in ctx["step5_output"]
        assert "test_import" in ctx["step5_output"]
        # Fixer's changed files must be in Step 7's context (via files_to_stage)
        assert "pdd/main.py" in ctx.get("files_to_stage", "")

    def test_orchestrator_allows_push_when_fixer_diff_unrelated_to_step5_failure(
        self, tmp_path
    ):
        """Orchestrator currently pushes even when fixer diff has no overlap with step5 failure.

        FAILS_ON_CURRENT_CODE: This test documents Bug 3 — the orchestrator has no
        causal-connection gate. When the fixer's changed files are completely unrelated
        to the paths mentioned in the Step 5 failure output, the push proceeds anyway.

        Expected behavior: the orchestrator should refuse the push (or Step 7 should
        fail) when the fixer diff does not touch any file related to the Step 5 failure
        signal.

        Acceptance criterion from issue #1212:
          "A test asserts that Step 7 fails the run if the fixer diff does not touch any
          file related to the Step 5 failure signal."
        """
        step5_failure = (
            "FAILED pdd/main.py::test_critical_path - AssertionError\n"
            "FAILED pdd/main.py::test_edge_case - AttributeError"
        )
        # The fixer touched only unrelated files — ZERO overlap with pdd/main.py
        unrelated_fixer_files = ["plugins/security-guidance/README.md"]

        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (False, step5_failure, 0.1, "model")
            if step_num == 6.1:
                return (True, "FILES_CREATED: plugins/security-guidance/README.md", 0.1, "model")
            if step_num == 7:
                # Step 7 approves blindly — no causal connection verification
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _make_pr_mode_patches(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=unrelated_fixer_files,
        )
        mock_push = patches[4]

        with patches[0], patches[1], patches[2], patches[3], mock_push as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            success, msg, _, _ = run_agentic_checkup_orchestrator(
                **{**PR_ARGS, "cwd": tmp_path}
            )

        # The orchestrator SHOULD refuse the push when fixer files have no overlap
        # with the Step 5 failure paths. On current code, push IS called — this FAILS.
        push_mock.assert_not_called(), (
            "Orchestrator must not push when the fixer's changed files "
            f"({unrelated_fixer_files}) have no overlap with the Step 5 failure "
            f"paths ({step5_failure!r}). Currently push is called with no causal "
            "connection check, allowing 6866-line unrelated commits to land on PRs."
        )
        assert success is False, (
            "Run must fail when fixer diff is causally disconnected from Step 5 failure"
        )


# ---------------------------------------------------------------------------
# Bug 5 — Fixer always runs; clean runs push commits
# ---------------------------------------------------------------------------


class TestBug5CleanRunConvergence:
    """Bug 5: Clean runs must produce zero commits so the loop has a finish line."""

    def test_clean_step5_skips_fixer_steps(self, tmp_path):
        """When Step 5 reports no failures (success=True), Steps 6.1/6.2/6.3 must be skipped.

        FAILS_ON_CURRENT_CODE: The fix-verify loop always runs all steps including
        6.1 (fix), 6.2 (regression tests), 6.3 (e2e tests) regardless of Step 5's
        outcome. With no concrete failure to fix, the fixer hallucinates changes.

        Expected: if Step 5 succeeds (no test failures found), the loop should skip
        the fixer steps and proceed directly to Step 7 for verification only.

        Acceptance criterion from issue #1212:
          "A clean pdd checkup --pr against a PR with no real issues produces no commit
          and no push."
        """
        invoked_steps = []

        def step_side_effect(step_num, name, context, **kwargs):
            invoked_steps.append(step_num)
            if step_num == 5:
                # Step 5 is clean — no test failures
                return (True, "All tests passed. 42 passed, 0 failed.", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        patches = _make_pr_mode_patches(tmp_path, step_side_effect=step_side_effect)

        with patches[0], patches[1], patches[2], patches[3], patches[4], \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**PR_ARGS, "cwd": tmp_path})

        # Steps 6.1/6.2/6.3 must NOT run when Step 5 is clean.
        # On current code, they ARE invoked — this assertion will FAIL.
        fixer_steps_invoked = [s for s in invoked_steps if s in (6.1, 6.2, 6.3)]
        assert not fixer_steps_invoked, (
            f"Fixer steps {fixer_steps_invoked} were invoked even though Step 5 "
            "reported no failures. When Step 5 is clean, the fix steps must be skipped "
            "to prevent the fixer from hallucinating unrelated changes."
        )

    def test_clean_run_produces_no_commit_or_push(self, tmp_path):
        """A clean checkup run (all steps pass, no failures) must produce zero push.

        FAILS_ON_CURRENT_CODE: The orchestrator calls `_commit_and_push_if_changed`
        after Step 7 passes, regardless of whether any changes were actually made.
        This causes clean runs to either push empty commits or push hallucinated fixer
        output, making it impossible to reach a stable "no-op" state.

        Expected: when Step 5 passes cleanly and the fixer runs but makes no meaningful
        changes, `_commit_and_push_if_changed` must either not be called or must
        observe that no files changed and produce no commit.

        Acceptance criterion from issue #1212:
          "A clean pdd checkup --pr against a PR with no real issues produces no commit
          and no push."
        """
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (True, "All tests passed, no failures.", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        # Worktree has NO uncommitted changes (clean state)
        patches = _make_pr_mode_patches(
            tmp_path,
            step_side_effect=step_side_effect,
            git_changed_files=[],  # No files changed in worktree
        )
        mock_push = patches[4]

        with patches[0], patches[1], patches[2], patches[3], mock_push as push_mock, \
             patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
            run_agentic_checkup_orchestrator(**{**PR_ARGS, "cwd": tmp_path})

        # On a clean run, push must not be called.
        # On current code, `_commit_and_push_if_changed` IS called unconditionally
        # after Step 7 approves — this assertion will FAIL on current code.
        push_mock.assert_not_called(), (
            "_commit_and_push_if_changed must not be called on a clean run "
            "(no actual changes in the worktree). Currently it is called "
            "unconditionally after Step 7 passes."
        )

    def test_repeated_clean_runs_stay_stable(self, tmp_path):
        """Consecutive clean runs must each produce zero commits (convergence property).

        FAILS_ON_CURRENT_CODE: Each run finds something to push because the fixer
        always runs and the push gate has no stable success condition. After the first
        run pushes hallucinated content, the next run finds new things to hallucinate.

        Expected: a run after the initial clean run produces no new commits.
        (Simulated by running orchestrator twice with distinct worktrees and asserting
        push is not called in either run.)
        """
        def step_side_effect(step_num, name, context, **kwargs):
            if step_num == 5:
                return (True, "All tests passed, 0 failed.", 0.1, "model")
            if step_num == 7:
                return (True, ALL_ISSUES_FIXED, 0.1, "model")
            return (True, f"out-{step_num}", 0.0, "model")

        push_call_counts = []

        for run_num in range(2):
            # Each run gets its own worktree subdirectory to avoid FileExistsError
            run_dir = tmp_path / f"run{run_num}"
            run_dir.mkdir()
            patches = _make_pr_mode_patches(
                run_dir,
                step_side_effect=step_side_effect,
                git_changed_files=[],
            )
            mock_push = patches[4]
            with patches[0], patches[1], patches[2], patches[3], mock_push as push_mock, \
                 patches[5], patches[6], patches[7], patches[8], patches[9], patches[10]:
                run_agentic_checkup_orchestrator(**{**PR_ARGS, "cwd": run_dir})
            push_call_counts.append(push_mock.call_count)

        # Both runs must produce zero pushes (stable / idempotent)
        assert push_call_counts == [0, 0], (
            f"Expected [0, 0] push calls across two clean runs, got {push_call_counts}. "
            "Clean runs must be idempotent — each run must produce zero commits."
        )
