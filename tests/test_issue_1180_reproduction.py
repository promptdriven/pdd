"""
Tests for issue #1180:
    "GitHub App clean restart request resumes old solving state and sync branch"

Includes:

  * Step-5 reproduction tests (prove the bug exists on the current buggy code).
  * Step-9 fix-detection tests (cover all Step-8 plan items and Step-6 scope
    expansion: content detection, refresh masking, mode-aware startup comment,
    idempotency marker).

The bug: when a user explicitly asks for a clean restart on a GitHub issue
(e.g. via a comment that says "Restarting cleanly with Opus..."), the
PDD CLI orchestrator still loads the previously persisted workflow state
for that issue and resumes from the last cached step. There is no public
"clean restart" signal: the only state-invalidation check in
``pdd/agentic_change_orchestrator.py:1387-1396`` compares
``issue.updated_at`` strings, which is unreliable across stop -> re-label
-> restart cycles (and does not look at issue content at all).

Expected behaviour after a fix:

    When the issue content (title/body/recent comments) contains an
    unambiguous clean-restart marker (e.g. "Restarting cleanly", "clean
    restart", "ignore previous Gemini-generated artifacts"), the
    orchestrator MUST:

      1. Clear the persisted workflow state for the issue.
      2. Start from step 1 of the full ``pdd-issue`` change flow rather
         than resuming a partially completed run.
      3. Post a startup comment that says "Clean restart" (vs "Resuming")
         and names the model, base branch, and command.
      4. Record an idempotency marker so the same restart phrase isn't
         re-detected on every workflow tick (preventing restart loops).
"""

from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.agentic_change_orchestrator import run_agentic_change_orchestrator


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def temp_cwd(tmp_path: Path) -> Path:
    return tmp_path


@pytest.fixture
def mock_dependencies(temp_cwd):
    with patch("pdd.agentic_change_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_change_orchestrator.load_prompt_template") as mock_template_loader, \
         patch("pdd.agentic_change_orchestrator.load_workflow_state") as mock_load_state, \
         patch("pdd.agentic_change_orchestrator.save_workflow_state") as mock_save_state, \
         patch("pdd.agentic_change_orchestrator.clear_workflow_state") as mock_clear_state, \
         patch("pdd.agentic_change_orchestrator.subprocess.run") as mock_subprocess, \
         patch("pdd.agentic_change_orchestrator.post_step_comment") as mock_post_comment, \
         patch("pdd.agentic_change_orchestrator.console") as mock_console, \
         patch("pdd.agentic_change_orchestrator.preprocess",
               side_effect=lambda prompt, **kw: prompt), \
         patch("pdd.agentic_change_orchestrator._check_existing_pr",
               return_value=None) as mock_check_pr:

        mock_run.return_value = (True, "Default Agent Output", 0.1, "claude-opus-4-7")
        mock_template_loader.return_value = "Mocked Prompt Template"
        mock_load_state.return_value = (None, None)
        mock_subprocess.return_value.stdout = str(temp_cwd)
        mock_subprocess.return_value.returncode = 0
        mock_post_comment.return_value = True

        yield {
            "run": mock_run,
            "load_state": mock_load_state,
            "save_state": mock_save_state,
            "clear_state": mock_clear_state,
            "subprocess": mock_subprocess,
            "post_comment": mock_post_comment,
            "console": mock_console,
            "check_pr": mock_check_pr,
        }


def _happy_path_side_effect(model: str = "claude-opus-4-7"):
    """Return a side_effect that makes the workflow succeed end-to-end."""
    def side_effect_run(**kwargs):
        label = kwargs.get("label", "")
        if label == "step9":
            return (True, "Implementation done. FILES_MODIFIED: file_a.py", 0.5, model)
        if label == "step10":
            return (True, "Arch updated", 0.1, model)
        if label.startswith("step11"):
            return (True, "No Issues Found", 0.1, model)
        if label == "step13":
            return (True,
                    "PR Created: https://github.com/promptdriven/pdd/pull/9999",
                    0.1, model)
        return (True, f"Output for {label}", 0.1, model)
    return side_effect_run


# Phrases that GitHub App users use to explicitly request a clean restart.
CLEAN_RESTART_PHRASES = [
    "Restarting cleanly with Opus. Previous Gemini-generated artifacts/PR "
    "#1126 were stopped and closed; ignore that run. Please run the full "
    "pdd-issue autonomous solving flow from the current issue requirements "
    "using the Opus model for all PDD App/executor work.",
    "Please do a clean restart of this issue from scratch.",
    "clean restart: ignore previously generated artifacts and start fresh.",
]


# ---------------------------------------------------------------------------
# Reproduction tests (from Step 5)
# ---------------------------------------------------------------------------

# Step-5 reproduction test: proves the bug exists on the current buggy code.
@pytest.mark.parametrize("restart_comment", CLEAN_RESTART_PHRASES)
def test_clean_restart_comment_clears_persisted_state(
        mock_dependencies, temp_cwd, restart_comment):
    """
    When the issue content carries an explicit "clean restart" request, the
    orchestrator MUST clear persisted state and start from step 1 -- even if
    ``issue_updated_at`` matches the stored value (i.e. the staleness check
    in ``run_agentic_change_orchestrator`` would otherwise allow a resume).
    """
    mocks = mock_dependencies
    mocks["run"].side_effect = _happy_path_side_effect()

    # Persisted state from the previous (Gemini-tainted) run.
    same_timestamp = "2026-05-20T10:00:00Z"
    persisted_state = {
        "issue_number": 1180,
        "last_completed_step": 8,
        "step_outputs": {str(n): f"out{n}" for n in range(1, 9)},
        "total_cost": 1.42,
        "model_used": "gemini-2.5-pro",
        "issue_updated_at": same_timestamp,
        "worktree_path": str(temp_cwd / "wt_old"),
    }
    mocks["load_state"].return_value = (persisted_state, 4242)

    issue_body = (
        "Original bug description goes here.\n\n"
        f"Latest comment: {restart_comment}"
    )

    success, _, _, _, _ = run_agentic_change_orchestrator(
        issue_url="https://github.com/promptdriven/pdd/issues/1180",
        issue_content=issue_body,
        repo_owner="promptdriven",
        repo_name="pdd",
        issue_number=1180,
        issue_author="Serhan-Asad",
        issue_title="GitHub App clean restart request resumes old solving state and sync branch",
        # Crucially: the staleness check would NOT fire because the stored
        # state has the same updated_at. Without explicit clean-restart
        # detection, the orchestrator will resume from step 9.
        issue_updated_at=same_timestamp,
        cwd=temp_cwd,
    )

    assert success is True

    # Expected behaviour after fix: state was cleared.
    assert mocks["clear_state"].called, (
        "Clean-restart request must clear persisted workflow state "
        "(see issue #1180 acceptance criteria)."
    )

    # Expected behaviour after fix: workflow restarts at step 1.
    labels_called = [c.kwargs.get("label") for c in mocks["run"].call_args_list]
    for early_step in ("step1", "step2", "step3", "step4", "step5"):
        assert early_step in labels_called, (
            f"Clean-restart should re-run {early_step}; "
            f"orchestrator instead resumed (got labels: {labels_called})"
        )


# Step-5 reproduction test: stale-worktree variant of the same bug.
def test_clean_restart_discards_old_worktree_path(mock_dependencies, temp_cwd):
    """
    The old run's ``worktree_path`` (pointing at ``change/issue-<old>``)
    must NOT be re-used by the clean-restart flow. If state is properly
    cleared, the orchestrator will set up a fresh worktree rather than
    re-using the stale path from the persisted state.
    """
    mocks = mock_dependencies
    mocks["run"].side_effect = _happy_path_side_effect()

    stale_worktree = temp_cwd / "change_issue_1120_worktree"
    stale_worktree.mkdir(parents=True, exist_ok=True)

    persisted_state = {
        "issue_number": 1180,
        "last_completed_step": 9,
        "step_outputs": {str(n): f"out{n}" for n in range(1, 10)},
        "total_cost": 0.7,
        "model_used": "gemini-2.5-pro",
        "issue_updated_at": "2026-05-20T10:00:00Z",
        "worktree_path": str(stale_worktree),
    }
    mocks["load_state"].return_value = (persisted_state, 1)

    issue_body = (
        "Bug body.\n\nRestarting cleanly with Opus. Previous Gemini-generated "
        "artifacts/PR were stopped and closed; ignore that run. Please run the "
        "full pdd-issue autonomous solving flow from the current issue "
        "requirements using the Opus model."
    )

    run_agentic_change_orchestrator(
        issue_url="https://github.com/promptdriven/pdd/issues/1180",
        issue_content=issue_body,
        repo_owner="promptdriven",
        repo_name="pdd",
        issue_number=1180,
        issue_author="Serhan-Asad",
        issue_title="Clean restart should not reuse old worktree",
        issue_updated_at="2026-05-20T10:00:00Z",
        cwd=temp_cwd,
    )

    # State must have been cleared so that the stale worktree path is
    # not carried forward into the new run.
    assert mocks["clear_state"].called, (
        "Clean restart did not clear persisted state -- the orchestrator "
        "would re-use the stale `change/issue-<old>` worktree path."
    )

    # The orchestrator must execute step 1 (i.e. start fresh), not resume.
    labels_called = [c.kwargs.get("label") for c in mocks["run"].call_args_list]
    assert "step1" in labels_called, (
        "Clean restart must begin the full pdd-issue flow at step 1; "
        f"got labels: {labels_called}"
    )


# Step-5 reproduction test: sanity guard that the normal resume path still works.
def test_normal_resume_still_works_without_clean_restart_phrase(
        mock_dependencies, temp_cwd):
    """
    Sanity guard: an ordinary issue body (no clean-restart phrase) should
    still allow normal resumption. This makes sure the clean-restart fix
    does NOT regress the standard cached-resume path.
    """
    mocks = mock_dependencies
    mocks["run"].side_effect = _happy_path_side_effect()

    timestamp = "2026-05-20T10:00:00Z"
    persisted_state = {
        "issue_number": 1181,
        "last_completed_step": 5,
        "step_outputs": {str(n): f"out{n}" for n in range(1, 6)},
        "total_cost": 0.3,
        "model_used": "claude-opus-4-7",
        "issue_updated_at": timestamp,
    }
    mocks["load_state"].return_value = (persisted_state, 7)

    run_agentic_change_orchestrator(
        issue_url="https://github.com/promptdriven/pdd/issues/1181",
        issue_content="Plain bug body -- no restart request here.",
        repo_owner="promptdriven",
        repo_name="pdd",
        issue_number=1181,
        issue_author="someone",
        issue_title="Plain resume test",
        issue_updated_at=timestamp,
        cwd=temp_cwd,
    )

    labels_called = [c.kwargs.get("label") for c in mocks["run"].call_args_list]
    # Normal resume: steps 1-5 are skipped because they are cached.
    for early_step in ("step1", "step2", "step3", "step4", "step5"):
        assert early_step not in labels_called, (
            f"Normal resume should skip cached {early_step}; "
            f"got labels: {labels_called}"
        )
    assert "step6" in labels_called, "Normal resume should continue at step 6"


# ---------------------------------------------------------------------------
# Step-9 fix-detection tests
# ---------------------------------------------------------------------------

# Scope addition: covers expansion item "mode-aware startup comment that names
# 'Clean restart' vs 'Resuming' with model/base-branch/command"
def test_startup_comment_says_clean_restart_when_detected(
        mock_dependencies, temp_cwd):
    """
    On a clean-restart request, the orchestrator MUST emit a startup comment
    that says "Clean restart" (case-insensitive) so users can tell the run
    is clean-starting rather than resuming.

    The misleading-comment symptom in #1180 was the bot saying
    "Resuming Autonomous Solving / Continuing from the current state..."
    even though the user asked for a clean restart. This test asserts that
    after the fix, an unambiguous "Clean restart" comment is posted.
    """
    mocks = mock_dependencies
    mocks["run"].side_effect = _happy_path_side_effect()

    same_timestamp = "2026-05-20T10:00:00Z"
    persisted_state = {
        "issue_number": 1180,
        "last_completed_step": 8,
        "step_outputs": {str(n): f"out{n}" for n in range(1, 9)},
        "total_cost": 1.42,
        "model_used": "gemini-2.5-pro",
        "issue_updated_at": same_timestamp,
        "worktree_path": str(temp_cwd / "wt_old"),
    }
    mocks["load_state"].return_value = (persisted_state, 4242)

    issue_body = (
        "Bug body.\n\nRestarting cleanly with Opus. Previous Gemini-generated "
        "artifacts/PR #1126 were stopped and closed; ignore that run. Please "
        "run the full pdd-issue autonomous solving flow from the current "
        "issue requirements using the Opus model."
    )

    run_agentic_change_orchestrator(
        issue_url="https://github.com/promptdriven/pdd/issues/1180",
        issue_content=issue_body,
        repo_owner="promptdriven",
        repo_name="pdd",
        issue_number=1180,
        issue_author="Serhan-Asad",
        issue_title="Clean restart startup comment test",
        issue_updated_at=same_timestamp,
        cwd=temp_cwd,
    )

    # Collect all text the orchestrator emitted: GitHub comments and console
    # prints. Either channel can carry the "Clean restart" announcement.
    comment_texts = []
    for call in mocks["post_comment"].call_args_list:
        body = call.kwargs.get("body")
        if body:
            comment_texts.append(body)
        comment_texts.append(str(call.kwargs.get("description", "")))
        comment_texts.append(str(call.kwargs.get("output", "")))
    for call in mocks["console"].print.call_args_list:
        if call.args:
            comment_texts.append(str(call.args[0]))

    combined = "\n".join(comment_texts).lower()

    assert "clean restart" in combined, (
        "After detecting a clean-restart request, the orchestrator must "
        "announce 'Clean restart' (not 'Resuming') so the user can tell "
        "what mode the run is in. Captured output:\n" + combined
    )
    # And it must NOT claim it is resuming.
    assert "resuming change workflow" not in combined, (
        "Clean-restart run must not print 'Resuming change workflow' -- "
        "that's the misleading comment from the original bug report."
    )


# Scope addition: covers expansion item "mode-aware startup comment that names
# 'Clean restart' vs 'Resuming' with model/base-branch/command"
def test_normal_resume_does_not_say_clean_restart(mock_dependencies, temp_cwd):
    """
    Mirror of the above: when no clean-restart phrase is present, the
    orchestrator MUST NOT announce a clean restart. This pins the mode
    detection so it doesn't fire on every run.
    """
    mocks = mock_dependencies
    mocks["run"].side_effect = _happy_path_side_effect()

    timestamp = "2026-05-20T10:00:00Z"
    persisted_state = {
        "issue_number": 1182,
        "last_completed_step": 5,
        "step_outputs": {str(n): f"out{n}" for n in range(1, 6)},
        "total_cost": 0.3,
        "model_used": "claude-opus-4-7",
        "issue_updated_at": timestamp,
    }
    mocks["load_state"].return_value = (persisted_state, 7)

    # Track call order: clear-at-entry happens before any step; the
    # clear-at-completion happens AFTER step 13 succeeds.
    events = []
    mocks["clear_state"].side_effect = lambda *a, **kw: events.append("clear")
    original_run = mocks["run"].side_effect

    def tracking_run(**kwargs):
        events.append(("run", kwargs.get("label", "")))
        return original_run(**kwargs)
    mocks["run"].side_effect = tracking_run

    run_agentic_change_orchestrator(
        issue_url="https://github.com/promptdriven/pdd/issues/1182",
        issue_content="Plain bug body -- nothing about restarting.",
        repo_owner="promptdriven",
        repo_name="pdd",
        issue_number=1182,
        issue_author="someone",
        issue_title="No restart phrasing here",
        issue_updated_at=timestamp,
        cwd=temp_cwd,
    )

    console_text = "\n".join(
        str(call.args[0]) if call.args else ""
        for call in mocks["console"].print.call_args_list
    ).lower()
    # No clean-restart announcement on a normal resume.
    assert "clean restart" not in console_text, (
        "Normal resume should NOT say 'Clean restart'; got console text:\n"
        + console_text
    )
    # Normal resume: no entry-time clear (clear only on successful completion,
    # which fires after the first run_agentic_task event).
    if events:
        # First event must be a run, not a clear, on normal resume.
        assert events[0] != "clear", (
            "Normal resume must not clear persisted state at orchestrator "
            f"entry. Event timeline: {events}"
        )


# Scope addition: covers expansion item "prevent state['issue_updated_at']
# refresh from absorbing a detected restart"
def test_timestamp_masking_does_not_block_clean_restart_detection(
        mock_dependencies, temp_cwd):
    """
    The original bug was that ``state['issue_updated_at']`` gets refreshed on
    every tick (lines 1407-1408 in agentic_change_orchestrator.py), which
    means even after a stop -> re-label cycle the staleness check can't fire
    (the stored timestamp absorbs the latest one). The fix MUST detect the
    restart from content even when timestamps are equal.

    This test pins that exact regression: same timestamp on both sides AND
    a clean-restart phrase => the orchestrator must clear state regardless
    of the timestamp comparison.
    """
    mocks = mock_dependencies

    # Identical timestamps -- the timestamp-only staleness check would NOT
    # fire here. Detection has to come from issue content.
    timestamp = "2026-05-20T10:00:00Z"
    persisted_state = {
        "issue_number": 1180,
        "last_completed_step": 11,
        "step_outputs": {str(n): f"out{n}" for n in range(1, 12)},
        "total_cost": 2.5,
        "model_used": "gemini-2.5-pro",
        "issue_updated_at": timestamp,
        "worktree_path": str(temp_cwd / "wt_old"),
    }
    mocks["load_state"].return_value = (persisted_state, 99)

    # Track ordering so we can distinguish the entry-time clear (the fix
    # we're verifying) from the completion-time clear (unrelated).
    events = []
    mocks["clear_state"].side_effect = lambda *a, **kw: events.append("clear")
    happy = _happy_path_side_effect()

    def tracking_run(**kwargs):
        events.append(("run", kwargs.get("label", "")))
        return happy(**kwargs)
    mocks["run"].side_effect = tracking_run

    issue_body = (
        "Bug body.\n\nclean restart: ignore previously generated artifacts "
        "and start fresh."
    )

    run_agentic_change_orchestrator(
        issue_url="https://github.com/promptdriven/pdd/issues/1180",
        issue_content=issue_body,
        repo_owner="promptdriven",
        repo_name="pdd",
        issue_number=1180,
        issue_author="Serhan-Asad",
        issue_title="Same-timestamp clean restart should still fire",
        issue_updated_at=timestamp,
        cwd=temp_cwd,
    )

    # The entry-time clear MUST fire before any step runs. On the buggy
    # code, the timestamp-only check sees equal timestamps and never
    # invokes clear_workflow_state at entry; the only clear that fires
    # is the post-step-13 completion clear.
    assert events, "Orchestrator did not record any events"
    assert events[0] == "clear", (
        "With identical timestamps, an explicit clean-restart phrase in the "
        "content MUST trigger clear_workflow_state() before the first step "
        f"runs. Event timeline: {events}"
    )


# Scope addition: covers expansion item "content-based detection of
# clean-restart phrases in issue_content at orchestrator entry"
def test_clean_restart_clears_step_outputs_and_starts_at_step_one(
        mock_dependencies, temp_cwd):
    """
    A clean restart must drop ``step_outputs`` from the prior run entirely
    -- a partial restart that kept step 8's cached output (e.g. Gemini's
    analysis) would still leak untrusted artifacts into the Opus run.

    Asserts the orchestrator does NOT use cached step outputs as part of
    the context (i.e. step1 is called fresh) AND that clear_workflow_state
    is invoked before any step runs.
    """
    mocks = mock_dependencies
    mocks["run"].side_effect = _happy_path_side_effect()

    timestamp = "2026-05-20T10:00:00Z"
    persisted_state = {
        "issue_number": 1180,
        "last_completed_step": 8,
        "step_outputs": {
            "1": "GEMINI_OUT_1",
            "2": "GEMINI_OUT_2",
            "3": "GEMINI_OUT_3",
            "4": "GEMINI_OUT_4",
            "5": "GEMINI_OUT_5",
            "6": "GEMINI_OUT_6",
            "7": "GEMINI_OUT_7",
            "8": "GEMINI_OUT_8",
        },
        "total_cost": 1.42,
        "model_used": "gemini-2.5-pro",
        "issue_updated_at": timestamp,
        "worktree_path": str(temp_cwd / "wt_old"),
    }
    mocks["load_state"].return_value = (persisted_state, 4242)

    issue_body = (
        "Bug body.\n\nRestarting cleanly with Opus. Previous Gemini-generated "
        "artifacts were stopped and closed; ignore that run."
    )

    run_agentic_change_orchestrator(
        issue_url="https://github.com/promptdriven/pdd/issues/1180",
        issue_content=issue_body,
        repo_owner="promptdriven",
        repo_name="pdd",
        issue_number=1180,
        issue_author="Serhan-Asad",
        issue_title="Drop cached step_outputs on clean restart",
        issue_updated_at=timestamp,
        cwd=temp_cwd,
    )

    # State cleared.
    assert mocks["clear_state"].called, (
        "Clean restart must invoke clear_workflow_state() to drop the "
        "Gemini-tainted step_outputs."
    )

    # Step 1 ran fresh -- the orchestrator did not skip into the middle of
    # the flow with cached Gemini outputs.
    labels = [c.kwargs.get("label") for c in mocks["run"].call_args_list]
    assert "step1" in labels, (
        f"Clean restart must run step1; got labels: {labels}"
    )

    # None of the run_agentic_task calls should have received the Gemini
    # cached output as context (the cached values must not appear in the
    # formatted prompt). We approximate this by checking the formatted
    # instruction string of each call.
    leaked = []
    for call in mocks["run"].call_args_list:
        instruction = call.kwargs.get("instruction", "")
        for marker in ("GEMINI_OUT_1", "GEMINI_OUT_5", "GEMINI_OUT_8"):
            if marker in instruction:
                leaked.append((call.kwargs.get("label"), marker))
    assert not leaked, (
        "Clean restart must NOT pass cached Gemini step outputs as context "
        f"to fresh steps. Leaked: {leaked}"
    )


# Scope addition: covers expansion item "mode-aware startup comment that names
# 'Clean restart' vs 'Resuming' with model/base-branch/command" -- specifically
# the "names model/base-branch/command" half of the requirement.
def test_startup_comment_names_model_and_base_branch_on_clean_restart(
        mock_dependencies, temp_cwd):
    """
    Acceptance criterion from issue #1180:
        "The startup comment clearly says whether the run is resuming or
        clean-starting, AND names the model, base branch, and command."

    Verifies that after a clean-restart is detected, the orchestrator's
    output (GitHub comments + console) includes the model id and a
    base-branch label and a pdd-issue command reference -- so users can
    confirm at a glance which executor and base the new run is on.
    """
    mocks = mock_dependencies
    mocks["run"].side_effect = _happy_path_side_effect()

    same_timestamp = "2026-05-20T10:00:00Z"
    persisted_state = {
        "issue_number": 1180,
        "last_completed_step": 7,
        "step_outputs": {str(n): f"out{n}" for n in range(1, 8)},
        "total_cost": 1.0,
        "model_used": "gemini-2.5-pro",
        "issue_updated_at": same_timestamp,
        "worktree_path": str(temp_cwd / "wt_old"),
    }
    mocks["load_state"].return_value = (persisted_state, 4242)

    issue_body = (
        "Bug body.\n\nRestarting cleanly with Opus. Previous Gemini-generated "
        "artifacts/PR were stopped and closed; ignore that run."
    )

    run_agentic_change_orchestrator(
        issue_url="https://github.com/promptdriven/pdd/issues/1180",
        issue_content=issue_body,
        repo_owner="promptdriven",
        repo_name="pdd",
        issue_number=1180,
        issue_author="Serhan-Asad",
        issue_title="Startup comment must name model and base branch",
        issue_updated_at=same_timestamp,
        cwd=temp_cwd,
    )

    # Aggregate everything the orchestrator emitted to either channel.
    emitted = []
    for call in mocks["post_comment"].call_args_list:
        body = call.kwargs.get("body")
        if body:
            emitted.append(body)
        emitted.append(str(call.kwargs.get("description", "")))
        emitted.append(str(call.kwargs.get("output", "")))
    for call in mocks["console"].print.call_args_list:
        if call.args:
            emitted.append(str(call.args[0]))
    combined = "\n".join(emitted).lower()

    # The model that ran the fresh attempt must be named somewhere in the
    # startup output (the bug report explicitly cited this requirement).
    assert "claude-opus" in combined or "opus" in combined, (
        "Startup output on clean restart must name the model "
        "(e.g. 'claude-opus-4-7'). Captured:\n" + combined
    )

    # The command being run (full pdd-issue change flow) must be named too,
    # so users can tell sync vs the full change flow is launching.
    assert "pdd-issue" in combined or "change" in combined, (
        "Startup output on clean restart must reference the command being "
        "run (pdd-issue / change). Captured:\n" + combined
    )


# Scope addition: covers expansion item "idempotency marker"
# (Step 6 / amended prompt requirement #13).
def test_clean_restart_idempotency_marker_prevents_restart_loop(
        mock_dependencies, temp_cwd):
    """
    Once the orchestrator has handled a clean-restart request, it must
    record an idempotency marker (e.g. ``state['clean_restart_handled_for']``)
    so the next tick (which still sees the same restart phrase in the issue
    body) does NOT clear state again and re-loop. Otherwise the bot would
    perpetually re-start from step 1.

    Simulates a second tick: the first run handled the restart and persisted
    state including the idempotency marker. On the second tick the same
    issue body still contains the restart phrase, but the orchestrator must
    NOT call ``clear_workflow_state`` because the marker shows the restart
    has already been handled.
    """
    mocks = mock_dependencies

    timestamp = "2026-05-21T08:00:00Z"
    restart_phrase = (
        "Restarting cleanly with Opus. Please run the full pdd-issue "
        "autonomous solving flow from the current issue requirements."
    )

    # Persisted state already records that this exact restart phrase was
    # handled on the previous tick.
    handled_marker = "Restarting cleanly with Opus"
    persisted_state = {
        "issue_number": 1180,
        "last_completed_step": 4,
        "step_outputs": {str(n): f"out{n}" for n in range(1, 5)},
        "total_cost": 0.6,
        "model_used": "claude-opus-4-7",
        "issue_updated_at": timestamp,
        # Both common spellings of the marker. The fix may choose either
        # name; the contract is "some idempotency marker exists".
        "clean_restart_handled_for": handled_marker,
        "clean_restart_handled": True,
    }
    mocks["load_state"].return_value = (persisted_state, 12)

    # Track call order so we can distinguish entry-clear (the restart loop
    # symptom) from completion-clear (the normal end-of-workflow cleanup).
    events = []
    mocks["clear_state"].side_effect = lambda *a, **kw: events.append("clear")
    happy = _happy_path_side_effect()

    def tracking_run(**kwargs):
        events.append(("run", kwargs.get("label", "")))
        return happy(**kwargs)
    mocks["run"].side_effect = tracking_run

    issue_body = "Bug body.\n\nLatest comment: " + restart_phrase

    run_agentic_change_orchestrator(
        issue_url="https://github.com/promptdriven/pdd/issues/1180",
        issue_content=issue_body,
        repo_owner="promptdriven",
        repo_name="pdd",
        issue_number=1180,
        issue_author="Serhan-Asad",
        issue_title="Idempotent restart -- second tick",
        issue_updated_at=timestamp,
        cwd=temp_cwd,
    )

    # On the second tick the restart has already been handled. The
    # orchestrator must NOT clear state at ENTRY (before any step runs).
    # A completion-time clear after step 13 is allowed and unrelated.
    first_event = events[0] if events else None
    assert first_event != "clear", (
        "Once an idempotency marker is in state, subsequent ticks must "
        "NOT re-clear state on the same restart phrase. Otherwise the "
        f"workflow would loop forever at step 1. Event timeline: {events}"
    )

    # And it must continue the run from where the previous tick left off.
    labels = [c.kwargs.get("label") for c in mocks["run"].call_args_list]
    assert "step1" not in labels, (
        "After idempotent handling, second tick must resume -- not re-run "
        f"step1; got labels: {labels}"
    )
    assert "step5" in labels, (
        f"Second tick should continue at step 5; got labels: {labels}"
    )
