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

