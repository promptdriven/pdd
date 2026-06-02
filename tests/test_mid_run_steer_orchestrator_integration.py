"""Integration-style tests for mid-run steering orchestrator wiring (#1324).

Validates the step-boundary flow on top of the #1328 foundation:
  - steer cursor seeded at workflow start
  - human issue comments drained at step boundaries
  - ``run_agentic_task`` receives ``steers=``
  - idempotent resume (same comment_id not re-injected)
  - bot/state/progress comments are not steers

See ``docs/mid_run_steering_validation.md`` for the manual checklist.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from pdd.agentic_common import (
    GITHUB_STATE_MARKER_END,
    GITHUB_STATE_MARKER_START,
    SteerEntry,
    drain_issue_steers,
    ensure_issue_steer_cursor_seeded,
    run_agentic_task,
    seed_issue_steer_cursor,
)
from pdd.agentic_test_orchestrator import run_agentic_test_orchestrator


@pytest.fixture
def mock_cwd(tmp_path):
    return tmp_path


@pytest.fixture
def mock_shutil_which():
    with patch("pdd.agentic_common._find_cli_binary") as mock:
        yield mock


@pytest.fixture
def mock_subprocess_run():
    with patch("pdd.agentic_common._subprocess_run") as mock:
        yield mock


@pytest.fixture
def mock_test_orch_deps():
    """Minimal mocks for test orchestrator integration runs."""
    with patch("pdd.agentic_test_orchestrator.run_agentic_task") as mock_run, \
         patch("pdd.agentic_test_orchestrator.load_workflow_state") as mock_load, \
         patch("pdd.agentic_test_orchestrator.save_workflow_state") as mock_save, \
         patch("pdd.agentic_test_orchestrator.clear_workflow_state") as mock_clear, \
         patch("pdd.agentic_test_orchestrator.load_prompt_template") as mock_template, \
         patch("pdd.agentic_test_orchestrator._setup_worktree") as mock_wt, \
         patch("pdd.agentic_test_orchestrator.shutil") as mock_shutil, \
         patch("subprocess.run") as mock_subprocess:

        mock_load.return_value = (None, None)
        mock_save.return_value = None
        mock_template.return_value = "Issue: {issue_content}"
        mock_wt.return_value = (Path("/tmp/worktree"), None)
        mock_shutil.which.return_value = None
        mock_subprocess.return_value = MagicMock(stdout="main\n", returncode=0)

        yield {
            "run": mock_run,
            "load": mock_load,
            "save": mock_save,
            "clear": mock_clear,
            "template": mock_template,
        }


@pytest.fixture
def test_orch_args(tmp_path):
    return {
        "issue_url": "https://github.com/o/r/issues/1",
        "issue_content": "Add login tests.",
        "repo_owner": "owner",
        "repo_name": "repo",
        "issue_number": 1,
        "issue_author": "user",
        "issue_title": "Login tests",
        "cwd": tmp_path,
        "quiet": True,
        "use_github_state": False,
    }


def test_ensure_issue_steer_cursor_seeded_noop_when_resumed(mock_cwd):
  """Resumed state with a cursor must not re-seed."""
  state = {
      "last_steered_comment_id": "50",
      "steer_cursor_seeded": True,
  }
  with patch(
      "pdd.agentic_common.seed_issue_steer_cursor",
  ) as mock_seed:
      assert (
          ensure_issue_steer_cursor_seeded(
              "owner", "repo", 1, state, cwd=mock_cwd
          )
          is False
      )
      mock_seed.assert_not_called()


def test_drain_filters_bot_state_and_progress_comments(
    mock_cwd, mock_subprocess_run, mock_shutil_which
):
    """Bot, workflow-state, and step-progress comments must not become steers."""
    mock_shutil_which.return_value = "/bin/gh"
    comments = [
        {
            "id": 201,
            "user": {"login": "human", "type": "User"},
            "body": "Please use pytest markers",
            "created_at": "2026-06-02T10:00:00Z",
        },
        {
            "id": 202,
            "user": {"login": "pdd-bot", "type": "Bot"},
            "body": "Bot status",
            "created_at": "2026-06-02T10:01:00Z",
        },
        {
            "id": 203,
            "user": {"login": "human", "type": "User"},
            "body": f"{GITHUB_STATE_MARKER_START}\n{{}}\n{GITHUB_STATE_MARKER_END}",
            "created_at": "2026-06-02T10:02:00Z",
        },
        {
            "id": 204,
            "user": {"login": "human", "type": "User"},
            "body": "## Step 3/18: Triage\nDone.",
            "created_at": "2026-06-02T10:03:00Z",
        },
        {
            "id": 205,
            "user": {"login": "human", "type": "User"},
            "body": "PDD-INCREMENTAL-STATUS: running",
            "created_at": "2026-06-02T10:04:00Z",
        },
    ]
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps(comments)
    mock_subprocess_run.return_value.stderr = ""

    state = {
        "last_steered_comment_id": "200",
        "last_steer_at": "2026-06-01T00:00:00Z",
        "steer_cursor_seeded": True,
    }
    steers = drain_issue_steers("owner", "repo", 1, state, cwd=mock_cwd)

    assert len(steers) == 1
    assert steers[0].comment_id == "201"
    assert steers[0].body == "Please use pytest markers"


def test_env_steer_injected_once_on_resume(mock_cwd):
    """Same comment_id must not be injected again after cursor advances."""
    os.environ["PDD_STEER_JSON"] = json.dumps(
        [{"comment_id": "42", "author": "alice", "body": "First steer"}]
    )
    try:
        state: dict = {}
        first = drain_issue_steers("owner", "repo", 1, state, cwd=mock_cwd)
        second = drain_issue_steers("owner", "repo", 1, state, cwd=mock_cwd)
        assert len(first) == 1
        assert second == []
    finally:
        os.environ.pop("PDD_STEER_JSON", None)


def test_run_agentic_task_injects_steered_section(
    mock_cwd, mock_shutil_which, mock_subprocess_run
):
    """Drained steers appear in the prompt passed to the agentic runner."""
    steers = [
        SteerEntry(comment_id="7", author="bob", body="Focus on edge cases"),
    ]
    mock_shutil_which.return_value = "/bin/claude"
    os.environ["ANTHROPIC_API_KEY"] = "key"
    mock_subprocess_run.return_value.returncode = 0
    mock_subprocess_run.return_value.stdout = json.dumps(
        {"result": "ok", "total_cost_usd": 0.01, "is_error": False}
    )
    mock_subprocess_run.return_value.stderr = ""

    success, _, _, _ = run_agentic_task(
        "Do the step.",
        mock_cwd,
        quiet=True,
        label="integration",
        steers=steers,
    )
    assert success
    prompt_input = mock_subprocess_run.call_args.kwargs.get("input", "")
    assert "## Steered user input (mid-run)" in prompt_input
    assert "Focus on edge cases" in prompt_input
    assert "@bob (7)" in prompt_input


def test_test_orchestrator_e2e_seed_drain_inject_idempotent(
    mock_test_orch_deps, test_orch_args, mock_cwd, mock_subprocess_run, mock_shutil_which
):
    """Full wiring: seed at start → new comment → steers= at boundary → idempotent drain."""
    mocks = mock_test_orch_deps
    mock_shutil_which.return_value = "/bin/gh"

    baseline = [
        {
            "id": 100,
            "user": {"login": "reporter", "type": "User"},
            "body": "Original issue discussion",
            "created_at": "2026-06-01T09:00:00Z",
        },
    ]
    mid_run = {
        "id": 101,
        "user": {"login": "reporter", "type": "User"},
        "body": "Use pytest markers on all new tests",
        "created_at": "2026-06-02T10:00:00Z",
    }
    gh_calls = {"n": 0}

    def gh_side_effect(cmd, **_kwargs):
        gh_calls["n"] += 1
        payload = baseline if gh_calls["n"] == 1 else baseline + [mid_run]
        result = MagicMock()
        result.returncode = 0
        result.stdout = json.dumps(payload)
        result.stderr = ""
        return result

    mock_subprocess_run.side_effect = gh_side_effect

    steer_calls: list[list[SteerEntry] | None] = []

    def run_side_effect(*_args, **kwargs):
        steer_calls.append(kwargs.get("steers"))
        return (True, "Duplicate of #99", 0.1, "anthropic")

    mocks["run"].side_effect = run_side_effect

    os.environ.pop("PDD_STEER_JSON", None)
    success, msg, _, _, _ = run_agentic_test_orchestrator(**test_orch_args)

    assert success is False
    assert "duplicate" in msg.lower()
    assert mocks["run"].call_count == 1
    assert gh_calls["n"] >= 2

    step_steers = steer_calls[0]
    assert step_steers is not None
    assert len(step_steers) == 1
    assert step_steers[0].comment_id == "101"
    assert "pytest markers" in step_steers[0].body

    state_after = mocks["save"].call_args_list[-1][0][3]
    assert state_after["last_steered_comment_id"] == "101"

    second_drain = drain_issue_steers(
        "owner",
        "repo",
        1,
        dict(state_after),
        cwd=mock_cwd,
    )
    assert second_drain == []


def test_test_orchestrator_calls_seed_at_start(
    mock_test_orch_deps, test_orch_args
):
    """Workflow start must establish a steer cursor before step drains."""
    mocks = mock_test_orch_deps
    mocks["run"].side_effect = [
        (True, "Duplicate of #1", 0.1, "anthropic"),
    ]

    with patch(
        "pdd.agentic_test_orchestrator.ensure_issue_steer_cursor_seeded",
        return_value=True,
    ) as mock_ensure:
        run_agentic_test_orchestrator(**test_orch_args)
        mock_ensure.assert_called_once()
        args = mock_ensure.call_args[0]
        assert args[0:3] == ("owner", "repo", 1)
