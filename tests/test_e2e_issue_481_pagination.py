"""
E2E Test for Issue #481: _find_state_comment() missing --paginate causes workflow
state loss on issues with 30+ comments.

This is a TRUE E2E test that exercises the full load_workflow_state() →
github_load_state() → _find_state_comment() call chain. Unlike the unit tests
in test_agentic_common.py which test _find_state_comment() in isolation, these
tests verify the complete user-facing behavior: when a user runs `pdd change`
(or any workflow) on an issue with 30+ comments and no local cache,
load_workflow_state() must find the GitHub-persisted state comment regardless
of which page it appears on.

The test mocks subprocess.run at the OS boundary to simulate GitHub API responses
(paginated vs non-paginated), but exercises all real Python code in between.

Bug: _find_state_comment() calls `gh api` without --paginate, so GitHub's API
returns only the first 30 comments. If the PDD_WORKFLOW_STATE comment is beyond
comment #30, it is invisible, causing complete workflow state loss.
"""

import json
import pytest
import tempfile
from pathlib import Path
from unittest.mock import patch, MagicMock

from pdd.agentic_common import (
    load_workflow_state,
    save_workflow_state,
    github_load_state,
    _find_state_comment,
    _serialize_state_comment,
    _build_state_marker,
    GITHUB_STATE_MARKER_START,
    GITHUB_STATE_MARKER_END,
)


def _make_comment(comment_id: int, body: str) -> dict:
    """Create a realistic GitHub API comment object."""
    return {
        "id": comment_id,
        "body": body,
        "user": {"login": "test-user"},
        "created_at": "2026-01-15T10:00:00Z",
        "updated_at": "2026-01-15T10:00:00Z",
    }


def _make_filler_comments(count: int, start_id: int = 1000) -> list:
    """Create N filler (non-state) comments to simulate a busy issue."""
    comments = []
    for i in range(count):
        comments.append(_make_comment(
            comment_id=start_id + i,
            body=f"Regular discussion comment #{i + 1}. This is not a state comment."
        ))
    return comments


def _make_state_comment(
    comment_id: int,
    workflow_type: str = "change",
    issue_number: int = 481,
    last_step: int = 8,
) -> dict:
    """Create a realistic PDD workflow state comment."""
    state = {
        "workflow": workflow_type,
        "issue_number": issue_number,
        "last_completed_step": last_step,
        "step_outputs": {str(i): f"Step {i} output" for i in range(1, last_step + 1)},
        "total_cost": 4.20,
        "model_used": "anthropic",
        "changed_files": [],
        "worktree_path": None,
        "github_comment_id": comment_id,
    }
    body = _serialize_state_comment(workflow_type, issue_number, state)
    return _make_comment(comment_id, body)


def _create_subprocess_mock(all_comments: list, has_paginate: bool = False):
    """
    Create a subprocess.run mock that simulates gh api behavior.

    Without --paginate: returns only the first 30 comments (GitHub API default).
    With --paginate: returns ALL comments.
    """
    def mock_subprocess_run(cmd, *args, **kwargs):
        result = MagicMock()

        # Only intercept `gh api` calls for issue comments
        if isinstance(cmd, list) and "gh" in cmd and "api" in cmd:
            # Check if this is a comments endpoint GET request
            is_comments_get = any(
                "comments" in str(c) and "issues" in str(c)
                for c in cmd
            ) and ("--method" not in cmd or cmd[cmd.index("--method") + 1] == "GET"
                   if "--method" in cmd else True)

            if is_comments_get:
                # Simulate GitHub API pagination behavior
                if "--paginate" in cmd:
                    # --paginate: return ALL comments
                    result.returncode = 0
                    result.stdout = json.dumps(all_comments)
                else:
                    # No --paginate: return only first 30 (GitHub default page size)
                    result.returncode = 0
                    result.stdout = json.dumps(all_comments[:30])
                return result

        # For non-matching commands, return a generic failure
        result.returncode = 1
        result.stdout = ""
        result.stderr = "not a gh api comments call"
        return result

    return mock_subprocess_run


@pytest.mark.e2e
class TestIssue481PaginationE2E:
    """
    E2E tests for Issue #481: Workflow state loss due to missing --paginate.

    These tests exercise the FULL call chain from load_workflow_state() through
    to the subprocess.run boundary, verifying user-facing behavior.
    """

    def test_state_comment_at_position_35_not_found_without_paginate(self):
        """
        E2E: State comment at position 35 (beyond 30-comment page) is NOT found.

        This is THE bug scenario:
        1. Issue has 40 comments (30 filler + state comment at position 35)
        2. _find_state_comment() calls gh api WITHOUT --paginate
        3. GitHub returns only the first 30 comments
        4. State comment (at position 35) is invisible
        5. load_workflow_state() returns None — workflow starts from scratch

        This test MUST FAIL on the current buggy code (proving the bug exists).
        """
        # Create 40 comments: 34 filler, then state at position 35, then 5 more filler
        filler_before = _make_filler_comments(34, start_id=1000)
        state_comment = _make_state_comment(
            comment_id=9999,
            workflow_type="change",
            issue_number=481,
            last_step=8,
        )
        filler_after = _make_filler_comments(5, start_id=2000)
        all_comments = filler_before + [state_comment] + filler_after  # 40 total

        mock_run = _create_subprocess_mock(all_comments)

        with tempfile.TemporaryDirectory() as tmpdir:
            cwd = Path(tmpdir)
            state_dir = cwd / ".pdd" / "change-state"
            state_dir.mkdir(parents=True, exist_ok=True)

            # Ensure NO local cache exists (forces GitHub-only lookup)
            local_file = state_dir / "change_state_481.json"
            assert not local_file.exists(), "Local cache must not exist for this test"

            with patch("pdd.agentic_common.subprocess.run", side_effect=mock_run), \
                 patch("pdd.agentic_common.shutil.which", return_value="/usr/bin/gh"):
                # Exercise the full call chain: load_workflow_state → github_load_state → _find_state_comment
                state, comment_id = load_workflow_state(
                    cwd=cwd,
                    issue_number=481,
                    workflow_type="change",
                    state_dir=state_dir,
                    repo_owner="promptdriven",
                    repo_name="pdd",
                    use_github_state=True,
                )

            # BUG ASSERTION: Without --paginate, the state comment at position 35
            # is invisible. load_workflow_state() returns None, causing a full restart.
            assert state is not None, (
                "BUG DETECTED (Issue #481): load_workflow_state() returned None because "
                "_find_state_comment() called 'gh api' without '--paginate'. "
                "The state comment at position 35 (beyond the 30-comment first page) "
                "was invisible. The workflow would restart from Step 1, wasting ~$4 in LLM costs. "
                "Fix: add '--paginate' to the gh api command in _find_state_comment()."
            )
            assert state["last_completed_step"] == 8
            assert comment_id == 9999

    def test_state_comment_within_first_page_found_even_without_paginate(self):
        """
        E2E: State comment within the first 30 comments IS found (baseline).

        This proves the function works correctly when pagination isn't needed,
        and that the test infrastructure itself is sound.
        """
        # State comment at position 5 — well within the first page
        filler_before = _make_filler_comments(4, start_id=1000)
        state_comment = _make_state_comment(
            comment_id=5555,
            workflow_type="change",
            issue_number=481,
            last_step=5,
        )
        filler_after = _make_filler_comments(10, start_id=2000)
        all_comments = filler_before + [state_comment] + filler_after  # 15 total

        mock_run = _create_subprocess_mock(all_comments)

        with tempfile.TemporaryDirectory() as tmpdir:
            cwd = Path(tmpdir)
            state_dir = cwd / ".pdd" / "change-state"
            state_dir.mkdir(parents=True, exist_ok=True)

            with patch("pdd.agentic_common.subprocess.run", side_effect=mock_run), \
                 patch("pdd.agentic_common.shutil.which", return_value="/usr/bin/gh"):
                state, comment_id = load_workflow_state(
                    cwd=cwd,
                    issue_number=481,
                    workflow_type="change",
                    state_dir=state_dir,
                    repo_owner="promptdriven",
                    repo_name="pdd",
                    use_github_state=True,
                )

            # Should work fine — state is on page 1
            assert state is not None, "State comment on page 1 should always be found"
            assert state["last_completed_step"] == 5
            assert comment_id == 5555

    def test_full_save_then_load_round_trip_with_pagination(self):
        """
        E2E: Full save → load round trip simulating cross-machine resume.

        Simulates the exact user scenario from the bug report:
        1. User runs pdd change, workflow saves state to GitHub (POST)
        2. User deletes local cache (or switches machines)
        3. User re-runs pdd change, load_workflow_state() must recover from GitHub
        4. BUG: If the state comment is beyond position 30, it's invisible
        """
        # Simulate an issue that accumulated 35 comments BEFORE the state save
        pre_existing_comments = _make_filler_comments(35, start_id=1000)

        # The state that will be "saved" to GitHub
        saved_state = {
            "workflow": "change",
            "issue_number": 481,
            "last_completed_step": 8,
            "step_outputs": {"1": "done", "2": "done", "3": "done", "4": "done",
                             "5": "done", "6": "done", "7": "done", "8": "done"},
            "total_cost": 4.20,
            "model_used": "anthropic",
            "changed_files": ["pdd/agentic_common.py"],
            "worktree_path": None,
            "github_comment_id": None,
        }

        # Build the state comment body as github_save_state would
        state_body = _serialize_state_comment("change", 481, saved_state)
        state_comment = _make_comment(comment_id=8888, body=state_body)

        # All comments: 35 pre-existing + 1 state = 36 total
        # State is at position 36 — BEYOND the 30-comment first page
        all_comments = pre_existing_comments + [state_comment]
        assert len(all_comments) == 36

        mock_run = _create_subprocess_mock(all_comments)

        with tempfile.TemporaryDirectory() as tmpdir:
            cwd = Path(tmpdir)
            state_dir = cwd / ".pdd" / "change-state"
            state_dir.mkdir(parents=True, exist_ok=True)

            # Step 1: No local cache (simulates "rm .pdd/change-state/*.json" or new machine)
            local_file = state_dir / "change_state_481.json"
            assert not local_file.exists()

            with patch("pdd.agentic_common.subprocess.run", side_effect=mock_run), \
                 patch("pdd.agentic_common.shutil.which", return_value="/usr/bin/gh"):
                # Step 2: load_workflow_state tries GitHub first, then falls back to local
                state, comment_id = load_workflow_state(
                    cwd=cwd,
                    issue_number=481,
                    workflow_type="change",
                    state_dir=state_dir,
                    repo_owner="promptdriven",
                    repo_name="pdd",
                    use_github_state=True,
                )

            # BUG: Without --paginate, state at position 36 is invisible.
            # load_workflow_state falls back to local, finds nothing, returns None.
            assert state is not None, (
                "BUG DETECTED (Issue #481): Cross-machine resume failed. "
                "load_workflow_state() could not find the GitHub state comment at "
                "position 36 (beyond the 30-comment first page) because "
                "_find_state_comment() does not use '--paginate'. "
                "The user would see 'Implementing change for issue #481' instead of "
                "'Resuming change workflow for issue #481 — Steps 1-8 already complete'. "
                "This wastes ~$4 in LLM costs and loses all workflow progress."
            )
            assert state["last_completed_step"] == 8
            assert state["changed_files"] == ["pdd/agentic_common.py"]

    def test_load_falls_back_to_local_cache_when_github_misses_due_to_pagination(self):
        """
        E2E: When GitHub lookup fails due to pagination, local cache is used as fallback.

        This test demonstrates the PARTIAL mitigation: if local cache exists,
        the user won't notice the bug. But when local cache is absent (new machine,
        deleted cache, CI), the bug causes complete state loss.
        """
        # State at position 35 — invisible without --paginate
        filler = _make_filler_comments(34, start_id=1000)
        state_comment = _make_state_comment(
            comment_id=7777, workflow_type="change",
            issue_number=481, last_step=6,
        )
        all_comments = filler + [state_comment] + _make_filler_comments(5, start_id=2000)

        mock_run = _create_subprocess_mock(all_comments)

        with tempfile.TemporaryDirectory() as tmpdir:
            cwd = Path(tmpdir)
            state_dir = cwd / ".pdd" / "change-state"
            state_dir.mkdir(parents=True, exist_ok=True)

            # Create local cache as if a previous run saved it
            local_state = {
                "workflow": "change",
                "issue_number": 481,
                "last_completed_step": 6,
                "step_outputs": {"1": "done"},
                "total_cost": 2.50,
            }
            local_file = state_dir / "change_state_481.json"
            with open(local_file, "w") as f:
                json.dump(local_state, f)

            with patch("pdd.agentic_common.subprocess.run", side_effect=mock_run), \
                 patch("pdd.agentic_common.shutil.which", return_value="/usr/bin/gh"):
                state, comment_id = load_workflow_state(
                    cwd=cwd,
                    issue_number=481,
                    workflow_type="change",
                    state_dir=state_dir,
                    repo_owner="promptdriven",
                    repo_name="pdd",
                    use_github_state=True,
                )

            # State is found — either from GitHub (if --paginate is fixed) or local cache.
            # Either way, the workflow resumes. But we can detect WHERE it came from:
            assert state is not None, "State should be found (from local cache or GitHub)"
            assert state["last_completed_step"] == 6

            # If the bug exists, comment_id will be None (loaded from local cache)
            # If the bug is fixed, comment_id will be 7777 (loaded from GitHub)
            if comment_id is None:
                # Bug still present — fell back to local cache
                # This is the "hidden" version of the bug: it works but only because
                # local cache happens to exist. Delete the cache and state is lost.
                pass
            else:
                assert comment_id == 7777  # Fixed — loaded from GitHub

    def test_exactly_30_comments_no_state_returns_none(self):
        """
        E2E: Issue with exactly 30 non-state comments returns None correctly.

        Verifies that load_workflow_state() correctly returns None when there
        genuinely is no state comment, even at the pagination boundary.
        """
        all_comments = _make_filler_comments(30, start_id=1000)
        mock_run = _create_subprocess_mock(all_comments)

        with tempfile.TemporaryDirectory() as tmpdir:
            cwd = Path(tmpdir)
            state_dir = cwd / ".pdd" / "change-state"
            state_dir.mkdir(parents=True, exist_ok=True)

            with patch("pdd.agentic_common.subprocess.run", side_effect=mock_run), \
                 patch("pdd.agentic_common.shutil.which", return_value="/usr/bin/gh"):
                state, comment_id = load_workflow_state(
                    cwd=cwd,
                    issue_number=481,
                    workflow_type="change",
                    state_dir=state_dir,
                    repo_owner="promptdriven",
                    repo_name="pdd",
                    use_github_state=True,
                )

            assert state is None, "No state comment exists, should return None"
            assert comment_id is None

    def test_multiple_workflow_types_state_beyond_page_1(self):
        """
        E2E: State comments for different workflow types (bug, change, architecture)
        all beyond page 1 — all must be found.

        This verifies the bug affects ALL orchestrators (change, bug, architecture),
        not just one.
        """
        # 32 filler comments + state comments for each workflow type
        filler = _make_filler_comments(32, start_id=1000)

        for workflow_type, step in [("change", 8), ("bug", 5), ("architecture", 11)]:
            state_comment = _make_state_comment(
                comment_id=6000 + hash(workflow_type) % 1000,
                workflow_type=workflow_type,
                issue_number=481,
                last_step=step,
            )
            all_comments = filler + [state_comment]

            mock_run = _create_subprocess_mock(all_comments)

            with tempfile.TemporaryDirectory() as tmpdir:
                cwd = Path(tmpdir)
                state_dir = cwd / ".pdd" / f"{workflow_type}-state"
                state_dir.mkdir(parents=True, exist_ok=True)

                with patch("pdd.agentic_common.subprocess.run", side_effect=mock_run), \
                     patch("pdd.agentic_common.shutil.which", return_value="/usr/bin/gh"):
                    state, comment_id = load_workflow_state(
                        cwd=cwd,
                        issue_number=481,
                        workflow_type=workflow_type,
                        state_dir=state_dir,
                        repo_owner="promptdriven",
                        repo_name="pdd",
                        use_github_state=True,
                    )

                assert state is not None, (
                    f"BUG (Issue #481): '{workflow_type}' workflow state at position 33 "
                    f"not found — _find_state_comment() missing --paginate. "
                    f"This affects ALL orchestrators, not just 'change'."
                )
                assert state["last_completed_step"] == step

    def test_state_at_position_31_boundary_not_found(self):
        """
        E2E: State comment at position 31 (just past the page boundary) is not found.

        The minimum reproduction case: exactly 30 filler + 1 state = 31 comments.
        Position 31 is on page 2 and invisible without --paginate.
        """
        filler = _make_filler_comments(30, start_id=1000)
        state_comment = _make_state_comment(
            comment_id=3131,
            workflow_type="change",
            issue_number=481,
            last_step=3,
        )
        all_comments = filler + [state_comment]  # 31 total
        assert len(all_comments) == 31

        mock_run = _create_subprocess_mock(all_comments)

        with tempfile.TemporaryDirectory() as tmpdir:
            cwd = Path(tmpdir)
            state_dir = cwd / ".pdd" / "change-state"
            state_dir.mkdir(parents=True, exist_ok=True)

            with patch("pdd.agentic_common.subprocess.run", side_effect=mock_run), \
                 patch("pdd.agentic_common.shutil.which", return_value="/usr/bin/gh"):
                state, comment_id = load_workflow_state(
                    cwd=cwd,
                    issue_number=481,
                    workflow_type="change",
                    state_dir=state_dir,
                    repo_owner="promptdriven",
                    repo_name="pdd",
                    use_github_state=True,
                )

            assert state is not None, (
                "BUG (Issue #481): State at position 31 (just past the 30-comment page "
                "boundary) is invisible. This is the MINIMUM reproduction case. "
                "Without '--paginate', gh api returns only 30 comments and the state "
                "comment at position 31 is on page 2."
            )
            assert state["last_completed_step"] == 3
            assert comment_id == 3131
