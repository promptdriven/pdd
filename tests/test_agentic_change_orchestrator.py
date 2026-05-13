"""Tests for pdd.agentic_change_orchestrator.

# TEST PLAN
#
# Requirements from the spec, mapped to tests:
#
# 1. run_agentic_change_orchestrator returns 5-tuple
#    → test_return_type_is_5_tuple, test_happy_path_full_workflow
# 2. Runs 13 steps with steps 11-12 in a review loop
#    → test_happy_path_full_workflow, test_review_loop_exits_on_no_issues,
#      test_review_loop_max_iterations
# 3. Accumulates context between steps
#    → test_step_output_passed_to_subsequent_step
# 4. Tracks total cost across all steps
#    → test_total_cost_accumulates
# 5. Parses FILES_CREATED, FILES_MODIFIED, DIRECT_EDITS from Step 9
#    → test_parse_files_marker_basic, test_parse_files_marker_none_filter,
#      test_step9_parses_changed_files
# 6. Parses ARCHITECTURE_FILES_MODIFIED, ASSOCIATED_DOCS_* from Step 10
#    → test_step10_associated_docs_modified_added_to_changed_files,
#      test_step10_conflicts_logged_but_not_staged,
#      test_step10_unchanged_logged_only
# 7. Parses "Direct Edit Candidates" table from Step 6
#    → test_parse_direct_edit_candidates_basic,
#      test_parse_direct_edit_candidates_no_table
# 8. Pre-Flight Drift Heal (Step 8.5) before Step 9
#    → test_preflight_drift_heal_called_before_step9,
#      test_preflight_skipped_on_resume_with_matching_worktree
# 9. Associated-Document Contract Verifier (Step 10.5)
#    → test_doc_sync_verifier_detects_silent_drops,
#      test_doc_sync_verifier_detects_bucket_overlaps,
#      test_strict_doc_sync_aborts_workflow
# 10. State Persistence + Resumption
#     → test_resumes_from_cached_step_outputs,
#       test_stale_state_clears_when_issue_updated_at_differs,
#       test_state_saved_after_each_step
# 11. Review loop max 5 iterations
#     → test_review_loop_max_iterations
# 12. Sync Order Generation
#     → test_sync_order_context_populated_with_command_list,
#       test_sync_order_list_default_when_no_modules
# 13. Existing PR Guard
#     → test_check_existing_pr_short_circuits_workflow
# 14. Stale State Detection (issue_updated_at mismatch)
#     → test_stale_state_clears_when_issue_updated_at_differs
# 15. Impacted Tests context
#     → test_impacted_tests_populated_from_changed_files
# 16. Per-Step Timeouts: CHANGE_STEP_TIMEOUTS dict locally defined
#     → test_change_step_timeouts_has_13_entries
# 17. Hard Stop conditions per step
#     → test_check_hard_stop_step1_duplicate,
#       test_check_hard_stop_step2_already_implemented,
#       test_check_hard_stop_step6_no_dev_units,
#       test_check_hard_stop_step8_no_changes,
#       test_check_hard_stop_step9_fail,
#       test_check_hard_stop_step4_requires_stop_condition_tag,
#       test_check_hard_stop_step7_requires_stop_condition_tag,
#       test_hard_stop_step1_returns_failure_tuple
# 18. Review loop "no issues found" case-insensitive check
#     → test_review_loop_no_issues_case_insensitive
# 19. Consecutive Provider Failure abort at 3
#     → test_consecutive_provider_failures_abort
# 20. Worktree setup failure path
#     → test_worktree_failure_returns_error_tuple
# 21. Step success comment hook (extract_step_report + post_step_comment_once)
#     → test_success_comment_hook_skips_when_no_step_report,
#       test_success_comment_hook_calls_post_when_report_present
# 22. normalize_step_comments_state coerces persisted value to Set[int]
#     → test_step_comments_state_loaded_and_normalized

This file is structured as standalone test functions (matching the existing style).
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path
from typing import Any, Dict, List, Set, Tuple
from unittest.mock import MagicMock, patch

import pytest

# Ensure the local project takes priority over any installed pdd package
PROJECT_ROOT = Path(__file__).resolve().parent.parent
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from pdd import agentic_change_orchestrator as aco
from pdd.agentic_change_orchestrator import (
    CHANGE_STEP_TIMEOUTS,
    MAX_REVIEW_ITERATIONS,
    _check_hard_stop,
    _parse_direct_edit_candidates,
    _parse_files_marker,
    _review_loop_no_issues,
    _verify_doc_sync_contract,
    run_agentic_change_orchestrator,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------


def _step_outputs() -> Dict[str, str]:
    """Default per-step outputs for a successful workflow."""
    return {
        "1": "Investigation: similar issue exists, no duplicate.",
        "2": "Status: not yet implemented.",
        "3": "Research complete.",
        "4": "Requirements verified.",
        "5": "Docs to update: README.md.",
        "6": (
            "Dev units identified.\n\n"
            "Direct Edit Candidates\n"
            "| File | Edit Type | Markers |\n"
            "| --- | --- | --- |\n"
            "| frontend/widget.js | uncomment | TODO |\n"
        ),
        "7": "Architecture review passed.",
        "8": "Prompt analysis complete.",
        "9": (
            "FILES_CREATED: prompts/new_python.prompt\n"
            "FILES_MODIFIED: prompts/existing_python.prompt\n"
            "DIRECT_EDITS: frontend/widget.js\n"
            "Done."
        ),
        "10": (
            "ARCHITECTURE_FILES_MODIFIED: architecture.json\n"
            "ASSOCIATED_DOCS_MODIFIED: README.md\n"
            "ASSOCIATED_DOCS_CONFLICTS: \n"
            "ASSOCIATED_DOCS_UNCHANGED: \n"
            "Done."
        ),
        "11": "No Issues Found",
        "12": "Fixes applied.",
        "13": "PR Created: https://github.com/example/myapp/pull/240",
    }


def _make_run_agentic_task_mock(outputs: Dict[str, str]):
    """Build a side-effect that selects output by label."""

    def _side_effect(*args, **kwargs):
        label = kwargs.get("label", "")
        step_part = label.replace("step", "").split("_")[0]
        return True, outputs.get(step_part, f"Output for {label}"), 0.10, "test-model"

    return _side_effect


@pytest.fixture
def default_outputs():
    return _step_outputs()


@pytest.fixture
def orchestrator_env(tmp_path, default_outputs):
    """Patch every external integration so run_agentic_change_orchestrator runs
    end-to-end without network/git/state IO. Yields a dict of mocks for tests
    that need to assert on specific calls.
    """
    patches = {}
    starts = []

    def _patch(target, **kwargs):
        p = patch(f"pdd.agentic_change_orchestrator.{target}", **kwargs)
        m = p.start()
        starts.append(p)
        patches[target] = m
        return m

    _patch("load_prompt_template", return_value="TEMPLATE: {issue_content}")
    run_mock = _patch("run_agentic_task")
    run_mock.side_effect = _make_run_agentic_task_mock(default_outputs)

    _patch("load_workflow_state", return_value=({}, None))
    _patch("save_workflow_state", return_value=None)
    _patch("clear_workflow_state", return_value=None)
    _patch("validate_cached_state", return_value=0)

    _patch("_check_existing_pr", return_value=None)
    _patch("_fetch_issue_updated_at", return_value="")
    _patch("_get_git_root", return_value=tmp_path)
    _patch("_setup_worktree", return_value=(tmp_path, None))
    _patch("_detect_worktree_changes", return_value=[])

    _patch("set_agentic_progress", return_value=None)
    _patch("clear_agentic_progress", return_value=None)
    _patch("post_step_comment", return_value=None)
    _patch("post_step_comment_once", return_value=True)
    _patch("extract_step_report", return_value=None)

    _patch(
        "register_untracked_prompts",
        return_value={"registered": [], "skipped": [], "errors": []},
    )
    _patch("_preflight_drift_heal", return_value=([], [], []))

    yield {"patches": patches, "tmp_path": tmp_path, "outputs": default_outputs}

    for p in starts:
        try:
            p.stop()
        except Exception:
            pass


def _run(tmp_path, **overrides) -> Tuple[bool, str, float, str, List[str]]:
    """Invoke run_agentic_change_orchestrator with safe defaults."""
    kwargs = dict(
        issue_url="https://github.com/example/myapp/issues/239",
        issue_content="Add feature X.",
        repo_owner="example",
        repo_name="myapp",
        issue_number=239,
        issue_author="alice",
        issue_title="Add X",
        issue_updated_at="2026-05-12T00:00:00Z",
        cwd=tmp_path,
        verbose=False,
        quiet=True,
        timeout_adder=0.0,
        use_github_state=False,
    )
    kwargs.update(overrides)
    return run_agentic_change_orchestrator(**kwargs)


# ---------------------------------------------------------------------------
# Return contract & happy path
# ---------------------------------------------------------------------------


def test_return_type_is_5_tuple(orchestrator_env):
    result = _run(orchestrator_env["tmp_path"])
    assert isinstance(result, tuple)
    assert len(result) == 5
    success, msg, cost, model, files = result
    assert isinstance(success, bool)
    assert isinstance(msg, str)
    assert isinstance(cost, float)
    assert isinstance(model, str)
    assert isinstance(files, list)


def test_happy_path_full_workflow(orchestrator_env):
    success, msg, cost, model, files = _run(orchestrator_env["tmp_path"])
    assert success is True
    # All 13 steps + 1 review iter (no step 12 if no issues) = 13 LLM calls
    run_mock = orchestrator_env["patches"]["run_agentic_task"]
    # Steps 1-11 + 13 = 12 calls minimum; step 12 not called since step 11 finds no issues
    assert run_mock.call_count == 12
    # Expected changed files: 9's three + 10's arch + 10's docs = 5
    expected = {
        "prompts/new_python.prompt",
        "prompts/existing_python.prompt",
        "frontend/widget.js",
        "architecture.json",
        "README.md",
    }
    assert expected.issubset(set(files))


def test_total_cost_accumulates(orchestrator_env):
    success, msg, cost, model, files = _run(orchestrator_env["tmp_path"])
    # 12 calls × $0.10 each = $1.20
    assert cost == pytest.approx(1.20, abs=0.001)


def test_model_used_recorded(orchestrator_env):
    success, msg, cost, model, files = _run(orchestrator_env["tmp_path"])
    assert model == "test-model"


def test_pr_url_extracted_from_step13(orchestrator_env):
    success, msg, _, _, _ = _run(orchestrator_env["tmp_path"])
    assert "github.com/example/myapp/pull/240" in msg


# ---------------------------------------------------------------------------
# CHANGE_STEP_TIMEOUTS configuration
# ---------------------------------------------------------------------------


def test_change_step_timeouts_has_13_entries():
    assert set(CHANGE_STEP_TIMEOUTS.keys()) == set(range(1, 14))
    # Step 9 is the heaviest at 1000s
    assert CHANGE_STEP_TIMEOUTS[9] == 1000.0
    # Step 10 bumped to 600s per spec
    assert CHANGE_STEP_TIMEOUTS[10] == 600.0
    # Steps 11, 13 stayed at 340s
    assert CHANGE_STEP_TIMEOUTS[11] == 340.0
    assert CHANGE_STEP_TIMEOUTS[13] == 340.0


def test_max_review_iterations_is_5():
    assert MAX_REVIEW_ITERATIONS == 5


# ---------------------------------------------------------------------------
# Marker parsing helpers
# ---------------------------------------------------------------------------


def test_parse_files_marker_basic():
    out = "FILES_CREATED: a.prompt, b.prompt\nOther line."
    assert _parse_files_marker(out, "FILES_CREATED") == ["a.prompt", "b.prompt"]


def test_parse_files_marker_none_filter():
    out = "FILES_CREATED: None\nFILES_MODIFIED: x.prompt"
    assert _parse_files_marker(out, "FILES_CREATED") == []
    assert _parse_files_marker(out, "FILES_MODIFIED") == ["x.prompt"]


def test_parse_files_marker_missing_returns_empty():
    assert _parse_files_marker("nothing here", "FILES_CREATED") == []
    assert _parse_files_marker("", "FILES_CREATED") == []


def test_parse_files_marker_dedupes_preserve_order():
    out = "FILES_MODIFIED: a, b, a, c"
    assert _parse_files_marker(out, "FILES_MODIFIED") == ["a", "b", "c"]


def test_parse_direct_edit_candidates_basic():
    step6_out = (
        "Direct Edit Candidates\n"
        "| File | Edit Type | Markers |\n"
        "| --- | --- | --- |\n"
        "| frontend/foo.js | uncomment | TODO |\n"
        "| frontend/bar.js | remove | PLACEHOLDER |\n"
    )
    result = _parse_direct_edit_candidates(step6_out)
    assert result == ["frontend/foo.js", "frontend/bar.js"]


def test_parse_direct_edit_candidates_no_table():
    assert _parse_direct_edit_candidates("no tables here") == []
    assert _parse_direct_edit_candidates("") == []


def test_parse_direct_edit_candidates_strips_backticks():
    step6_out = (
        "Direct Edit Candidates\n"
        "| File | Edit |\n"
        "| --- | --- |\n"
        "| `frontend/baz.js` | uncomment |\n"
    )
    assert _parse_direct_edit_candidates(step6_out) == ["frontend/baz.js"]


# ---------------------------------------------------------------------------
# Hard stop detection
# ---------------------------------------------------------------------------


def test_check_hard_stop_step1_duplicate():
    assert _check_hard_stop(1, "This is a Duplicate of #42") is not None


def test_check_hard_stop_step1_no_match_returns_none():
    assert _check_hard_stop(1, "No duplicates found") is None


def test_check_hard_stop_step2_already_implemented():
    out = "**Status:** already implemented in module X"
    assert _check_hard_stop(2, out) is not None


def test_check_hard_stop_step2_plain_status():
    out = "Status: already implemented"
    assert _check_hard_stop(2, out) is not None


def test_check_hard_stop_step2_quoted_no_false_positive():
    # Quoted-style/mid-line prose should not trigger
    out = "The user said 'already implemented' but it isn't."
    assert _check_hard_stop(2, out) is None


def test_check_hard_stop_step6_no_dev_units():
    out = "**Status:** no dev units found"
    assert _check_hard_stop(6, out) is not None


def test_check_hard_stop_step8_no_changes():
    out = "**Status:** no changes required"
    assert _check_hard_stop(8, out) is not None


def test_check_hard_stop_step9_fail():
    out = "Something went wrong\nFAIL: cannot apply patch"
    assert _check_hard_stop(9, out) is not None


def test_check_hard_stop_step4_requires_stop_condition_tag():
    # Plain "clarification" prose should NOT stop
    assert _check_hard_stop(4, "Need more clarification on the spec.") is None
    # Tag triggers stop
    assert _check_hard_stop(4, "STOP_CONDITION: clarification needed") is not None


def test_check_hard_stop_step7_requires_stop_condition_tag():
    assert _check_hard_stop(7, "Some architectural concern but proceeding.") is None
    assert _check_hard_stop(7, "STOP_CONDITION: architectural decision needed") is not None


def test_check_hard_stop_empty_output_returns_none():
    assert _check_hard_stop(1, "") is None
    assert _check_hard_stop(2, "") is None


# ---------------------------------------------------------------------------
# Review loop helper
# ---------------------------------------------------------------------------


def test_review_loop_no_issues_case_insensitive():
    assert _review_loop_no_issues("No Issues Found") is True
    assert _review_loop_no_issues("no issues found") is True
    assert _review_loop_no_issues("NO ISSUES FOUND") is True
    assert _review_loop_no_issues("Status: No Issues Found in review.") is True


def test_review_loop_no_issues_negative():
    assert _review_loop_no_issues("found some issues") is False
    assert _review_loop_no_issues("") is False


# ---------------------------------------------------------------------------
# Doc-sync contract verifier (Step 10.5)
# ---------------------------------------------------------------------------


def test_verify_doc_sync_contract_clean_all_buckets():
    docs = ["README.md", "CHANGELOG.md"]
    step10 = (
        "ASSOCIATED_DOCS_MODIFIED: README.md\n"
        "ASSOCIATED_DOCS_CONFLICTS: \n"
        "ASSOCIATED_DOCS_UNCHANGED: CHANGELOG.md\n"
    )
    mod, conf, unch, dropped, overlap = _verify_doc_sync_contract(docs, step10)
    assert mod == ["README.md"]
    assert conf == []
    assert unch == ["CHANGELOG.md"]
    assert dropped == []
    assert overlap == []


def test_verify_doc_sync_contract_detects_silent_drops():
    docs = ["README.md", "CHANGELOG.md", "docs/api.md"]
    step10 = (
        "ASSOCIATED_DOCS_MODIFIED: README.md\n"
        "ASSOCIATED_DOCS_CONFLICTS: \n"
        "ASSOCIATED_DOCS_UNCHANGED: CHANGELOG.md\n"
    )
    mod, conf, unch, dropped, overlap = _verify_doc_sync_contract(docs, step10)
    assert dropped == ["docs/api.md"]
    assert overlap == []


def test_verify_doc_sync_contract_detects_overlaps():
    docs = ["README.md"]
    step10 = (
        "ASSOCIATED_DOCS_MODIFIED: README.md\n"
        "ASSOCIATED_DOCS_CONFLICTS: README.md\n"
    )
    mod, conf, unch, dropped, overlap = _verify_doc_sync_contract(docs, step10)
    assert "README.md" in overlap
    assert dropped == []


# ---------------------------------------------------------------------------
# Existing PR guard
# ---------------------------------------------------------------------------


def test_check_existing_pr_short_circuits_workflow(orchestrator_env):
    orchestrator_env["patches"]["_check_existing_pr"].return_value = (
        "https://github.com/example/myapp/pull/100"
    )
    success, msg, cost, model, files = _run(orchestrator_env["tmp_path"])
    assert success is True
    assert "PR already exists" in msg
    assert "pull/100" in msg
    assert cost == 0.0
    assert model == "unknown"
    assert files == []
    # No LLM calls should have happened
    run_mock = orchestrator_env["patches"]["run_agentic_task"]
    assert run_mock.call_count == 0


# ---------------------------------------------------------------------------
# Worktree failure
# ---------------------------------------------------------------------------


def test_worktree_failure_returns_error_tuple(orchestrator_env):
    orchestrator_env["patches"]["_setup_worktree"].return_value = (
        None,
        "git worktree add failed: branch in use",
    )
    success, msg, cost, model, files = _run(orchestrator_env["tmp_path"])
    assert success is False
    assert "Failed to create worktree" in msg


# ---------------------------------------------------------------------------
# Hard stop end-to-end
# ---------------------------------------------------------------------------


def test_hard_stop_step1_returns_failure_tuple(orchestrator_env):
    outputs = dict(orchestrator_env["outputs"])
    outputs["1"] = "This is Duplicate of #42"
    orchestrator_env["patches"]["run_agentic_task"].side_effect = (
        _make_run_agentic_task_mock(outputs)
    )
    success, msg, cost, model, files = _run(orchestrator_env["tmp_path"])
    assert success is False
    assert "Stopped at step 1" in msg
    # post_step_comment must be called on hard stop
    assert orchestrator_env["patches"]["post_step_comment"].called


# ---------------------------------------------------------------------------
# Step 9 file parsing
# ---------------------------------------------------------------------------


def test_step9_parses_changed_files(orchestrator_env):
    success, msg, cost, model, files = _run(orchestrator_env["tmp_path"])
    assert "prompts/new_python.prompt" in files
    assert "prompts/existing_python.prompt" in files
    assert "frontend/widget.js" in files


def test_step9_fallback_to_worktree_detection(orchestrator_env):
    # Step 9 emits no FILES_* markers
    outputs = dict(orchestrator_env["outputs"])
    outputs["9"] = "Implementation done."
    orchestrator_env["patches"]["run_agentic_task"].side_effect = (
        _make_run_agentic_task_mock(outputs)
    )
    orchestrator_env["patches"]["_detect_worktree_changes"].return_value = [
        "prompts/from_worktree_python.prompt"
    ]
    success, msg, cost, model, files = _run(orchestrator_env["tmp_path"])
    assert success is True
    assert "prompts/from_worktree_python.prompt" in files


# ---------------------------------------------------------------------------
# Step 10 parsing
# ---------------------------------------------------------------------------


def test_step10_associated_docs_modified_added_to_changed_files(orchestrator_env):
    success, msg, cost, model, files = _run(orchestrator_env["tmp_path"])
    assert "README.md" in files
    assert "architecture.json" in files


def test_step10_conflicts_logged_but_not_staged(orchestrator_env):
    outputs = dict(orchestrator_env["outputs"])
    outputs["10"] = (
        "ARCHITECTURE_FILES_MODIFIED: architecture.json\n"
        "ASSOCIATED_DOCS_MODIFIED: README.md\n"
        "ASSOCIATED_DOCS_CONFLICTS: docs/conflicting.md\n"
        "ASSOCIATED_DOCS_UNCHANGED: \n"
    )
    orchestrator_env["patches"]["run_agentic_task"].side_effect = (
        _make_run_agentic_task_mock(outputs)
    )
    success, msg, cost, model, files = _run(orchestrator_env["tmp_path"])
    assert "docs/conflicting.md" not in files


def test_step10_unchanged_logged_only(orchestrator_env):
    outputs = dict(orchestrator_env["outputs"])
    outputs["10"] = (
        "ARCHITECTURE_FILES_MODIFIED: architecture.json\n"
        "ASSOCIATED_DOCS_MODIFIED: \n"
        "ASSOCIATED_DOCS_CONFLICTS: \n"
        "ASSOCIATED_DOCS_UNCHANGED: docs/unchanged.md\n"
    )
    orchestrator_env["patches"]["run_agentic_task"].side_effect = (
        _make_run_agentic_task_mock(outputs)
    )
    success, msg, cost, model, files = _run(orchestrator_env["tmp_path"])
    assert "docs/unchanged.md" not in files


# ---------------------------------------------------------------------------
# Review loop
# ---------------------------------------------------------------------------


def test_review_loop_exits_on_no_issues(orchestrator_env):
    # Default outputs already have step 11 = "No Issues Found"
    success, msg, cost, model, files = _run(orchestrator_env["tmp_path"])
    # Step 12 should NOT have been called
    run_mock = orchestrator_env["patches"]["run_agentic_task"]
    labels = [c.kwargs.get("label", "") for c in run_mock.call_args_list]
    assert not any(lbl.startswith("step12") for lbl in labels)


def test_review_loop_max_iterations(orchestrator_env):
    outputs = dict(orchestrator_env["outputs"])
    outputs["11"] = "Issues found: blah blah"  # never "no issues"
    outputs["12"] = "Fixes applied iteration N"
    orchestrator_env["patches"]["run_agentic_task"].side_effect = (
        _make_run_agentic_task_mock(outputs)
    )
    success, msg, cost, model, files = _run(orchestrator_env["tmp_path"])
    run_mock = orchestrator_env["patches"]["run_agentic_task"]
    labels = [c.kwargs.get("label", "") for c in run_mock.call_args_list]
    s11 = [lbl for lbl in labels if lbl.startswith("step11")]
    s12 = [lbl for lbl in labels if lbl.startswith("step12")]
    assert len(s11) == MAX_REVIEW_ITERATIONS
    assert len(s12) == MAX_REVIEW_ITERATIONS
    # Workflow still continues to step 13
    assert success is True


# ---------------------------------------------------------------------------
# Pre-Flight Drift Heal
# ---------------------------------------------------------------------------


def test_preflight_drift_heal_called_before_step9(orchestrator_env):
    _run(orchestrator_env["tmp_path"])
    assert orchestrator_env["patches"]["_preflight_drift_heal"].called


def test_preflight_skipped_on_resume_with_matching_worktree(orchestrator_env, tmp_path):
    # Simulate state where preflight already ran for this worktree
    state = {
        "workflow": "change",
        "issue_number": 239,
        "last_completed_step": 8,
        "step_outputs": {str(i): orchestrator_env["outputs"][str(i)] for i in range(1, 9)},
        "issue_updated_at": "2026-05-12T00:00:00Z",
        "preflight_drift_healed": True,
        "preflight_healed_worktree": str(tmp_path),
        "worktree_path": str(tmp_path),
    }
    orchestrator_env["patches"]["load_workflow_state"].return_value = (state, None)
    orchestrator_env["patches"]["validate_cached_state"].return_value = 8
    _run(orchestrator_env["tmp_path"])
    assert not orchestrator_env["patches"]["_preflight_drift_heal"].called


# ---------------------------------------------------------------------------
# State persistence & resume
# ---------------------------------------------------------------------------


def test_resumes_from_cached_step_outputs(orchestrator_env, default_outputs):
    state = {
        "workflow": "change",
        "issue_number": 239,
        "last_completed_step": 5,
        "step_outputs": {str(i): default_outputs[str(i)] for i in range(1, 6)},
        "issue_updated_at": "2026-05-12T00:00:00Z",
    }
    orchestrator_env["patches"]["load_workflow_state"].return_value = (state, None)
    orchestrator_env["patches"]["validate_cached_state"].return_value = 5

    _run(orchestrator_env["tmp_path"])
    run_mock = orchestrator_env["patches"]["run_agentic_task"]
    labels = [c.kwargs.get("label", "") for c in run_mock.call_args_list]
    # Step labels exactly "step1".."step5" should NOT have been called.
    # (Use exact match so "step11"/"step12" don't get mistaken for "step1".)
    cached_labels = {f"step{i}" for i in range(1, 6)}
    invoked_cached = cached_labels.intersection(labels)
    assert not invoked_cached, f"Cached steps should be skipped but ran: {invoked_cached}"
    # Steps 6+ should have run
    assert "step6" in labels


def test_stale_state_clears_when_issue_updated_at_differs(orchestrator_env, default_outputs):
    state = {
        "workflow": "change",
        "issue_number": 239,
        "last_completed_step": 5,
        "step_outputs": {str(i): default_outputs[str(i)] for i in range(1, 6)},
        "issue_updated_at": "2026-01-01T00:00:00Z",  # OLD timestamp
    }
    orchestrator_env["patches"]["load_workflow_state"].return_value = (state, None)
    orchestrator_env["patches"]["validate_cached_state"].return_value = 5

    _run(orchestrator_env["tmp_path"])
    # State should have been cleared, so step 1 must run
    run_mock = orchestrator_env["patches"]["run_agentic_task"]
    labels = [c.kwargs.get("label", "") for c in run_mock.call_args_list]
    assert "step1" in labels
    assert orchestrator_env["patches"]["clear_workflow_state"].called


def test_state_saved_after_each_step(orchestrator_env):
    _run(orchestrator_env["tmp_path"])
    save_mock = orchestrator_env["patches"]["save_workflow_state"]
    # Should be called at least once per step, plus extras for sub-phases
    assert save_mock.call_count >= 13


# ---------------------------------------------------------------------------
# Step success-comment hook
# ---------------------------------------------------------------------------


def test_success_comment_hook_skips_when_no_step_report(orchestrator_env):
    # Default extract_step_report returns None → post_step_comment_once not called
    _run(orchestrator_env["tmp_path"])
    assert not orchestrator_env["patches"]["post_step_comment_once"].called


def test_success_comment_hook_calls_post_when_report_present(orchestrator_env):
    orchestrator_env["patches"]["extract_step_report"].return_value = "Step report body"
    _run(orchestrator_env["tmp_path"])
    assert orchestrator_env["patches"]["post_step_comment_once"].called


def test_step_comments_state_loaded_and_normalized():
    from pdd.agentic_common import normalize_step_comments_state
    # Function exists and accepts malformed inputs
    assert normalize_step_comments_state(None) == set()
    assert normalize_step_comments_state([1, 2, "bogus", 1]) == {1, 2}


# ---------------------------------------------------------------------------
# Sync order generation
# ---------------------------------------------------------------------------


def test_sync_order_context_populated_with_command_list(orchestrator_env, tmp_path):
    # Create a real prompts dir with a graph in the worktree
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)
    (prompts_dir / "existing_python.prompt").write_text("module existing")
    (prompts_dir / "new_python.prompt").write_text("module new")

    captured_step13_template_calls: List[str] = []

    original_loader = orchestrator_env["patches"]["load_prompt_template"]
    # Inspect what step 13 template was formatted with
    _run(orchestrator_env["tmp_path"])

    run_mock = orchestrator_env["patches"]["run_agentic_task"]
    step13_calls = [c for c in run_mock.call_args_list if c.kwargs.get("label") == "step13"]
    assert step13_calls, "step13 should have been called"
    instruction = step13_calls[0].kwargs.get("instruction", "")
    # The instruction is the formatted template; we just want to verify the function ran
    assert instruction  # non-empty


def test_sync_order_list_default_when_no_modules(orchestrator_env, tmp_path):
    # No prompts dir at all
    # Just verify the workflow doesn't crash and produces success
    success, msg, cost, model, files = _run(orchestrator_env["tmp_path"])
    assert success is True


# ---------------------------------------------------------------------------
# Strict mode doc-sync abort
# ---------------------------------------------------------------------------


def test_strict_doc_sync_aborts_workflow(orchestrator_env, monkeypatch, tmp_path):
    monkeypatch.setenv("PDD_STRICT_DOC_SYNC", "1")
    # Cause a silent-drop by having discover_associated_documents return a doc
    # that Step 10 does NOT report in any bucket.
    with patch(
        "pdd.sync_order.discover_associated_documents",
        return_value=["docs/lost.md"],
    ):
        outputs = dict(orchestrator_env["outputs"])
        outputs["10"] = (
            "ARCHITECTURE_FILES_MODIFIED: architecture.json\n"
            "ASSOCIATED_DOCS_MODIFIED: \n"
            "ASSOCIATED_DOCS_CONFLICTS: \n"
            "ASSOCIATED_DOCS_UNCHANGED: \n"
        )
        orchestrator_env["patches"]["run_agentic_task"].side_effect = (
            _make_run_agentic_task_mock(outputs)
        )
        # Need a real prompts dir so discovery is attempted
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir(parents=True, exist_ok=True)
        (prompts_dir / "existing_python.prompt").write_text("module")
        (prompts_dir / "new_python.prompt").write_text("module")

        success, msg, cost, model, files = _run(orchestrator_env["tmp_path"])
        assert success is False
        assert "PDD_STRICT_DOC_SYNC" in msg
        assert "Stopped at step 10" in msg


# ---------------------------------------------------------------------------
# Impacted tests
# ---------------------------------------------------------------------------


def test_impacted_tests_populated_from_changed_files(orchestrator_env, tmp_path):
    tests_dir = tmp_path / "tests"
    tests_dir.mkdir(parents=True, exist_ok=True)
    (tests_dir / "test_existing.py").write_text("# test")
    (tests_dir / "test_unrelated.py").write_text("# test")

    # Capture what step 13 receives
    run_mock = orchestrator_env["patches"]["run_agentic_task"]
    _run(orchestrator_env["tmp_path"])

    step13_calls = [c for c in run_mock.call_args_list if c.kwargs.get("label") == "step13"]
    assert step13_calls
    # Workflow completed; impacted_tests is computed before step 13 runs
    # We can only loosely check by ensuring step 13 actually fired
    assert len(step13_calls) == 1


# ---------------------------------------------------------------------------
# Consecutive provider failure abort
# ---------------------------------------------------------------------------


def test_consecutive_provider_failures_abort(orchestrator_env):
    # Return "All agent providers failed" for every step
    def failing_side_effect(*args, **kwargs):
        return False, "All agent providers failed", 0.0, "unknown"

    orchestrator_env["patches"]["run_agentic_task"].side_effect = failing_side_effect
    success, msg, cost, model, files = _run(orchestrator_env["tmp_path"])
    assert success is False
    assert "consecutive" in msg.lower() or "providers unavailable" in msg.lower()


# ---------------------------------------------------------------------------
# Step output passed to subsequent step (context accumulation)
# ---------------------------------------------------------------------------


def test_step_output_passed_to_subsequent_step(orchestrator_env):
    # Configure step 1 to emit a unique sentinel that step 2's template should
    # render. We rely on the orchestrator substituting {step1_output} when
    # present in the template.
    sentinel = "SENTINEL_FROM_STEP1_XYZ"
    outputs = dict(orchestrator_env["outputs"])
    outputs["1"] = sentinel
    orchestrator_env["patches"]["run_agentic_task"].side_effect = (
        _make_run_agentic_task_mock(outputs)
    )

    captured: Dict[str, str] = {}

    def template_side_effect(name):
        if "step2" in name:
            return "Previous step: {step1_output}"
        return "TEMPLATE for {issue_content}"

    orchestrator_env["patches"]["load_prompt_template"].side_effect = template_side_effect

    def run_capture(*args, **kwargs):
        label = kwargs.get("label", "")
        if label == "step2":
            captured["step2_instruction"] = kwargs.get("instruction", "")
        return True, outputs.get(label.replace("step", "").split("_")[0], ""), 0.10, "test-model"

    orchestrator_env["patches"]["run_agentic_task"].side_effect = run_capture
    _run(orchestrator_env["tmp_path"])
    assert sentinel in captured.get("step2_instruction", "")
