import pytest
from unittest.mock import patch, MagicMock
from pathlib import Path

from pdd.checkup_review_loop import (
    parse_reviewers,
    run_checkup_review_loop,
    ReviewLoopContext,
    ReviewLoopConfig,
    _commit_and_push_if_changed,
)

# Test plan:
# 1. parse_reviewers: string input, list input, aliases, unknown dropping.
# 2. Config overrides: reviewers vs reviewer/fixer properties.
# 3. Role uniqueness: fast-fails if reviewer == fixer (except in review_only).
# 4. review_only mode: runs review, skips fix/push, returns correctly.
# 5. Full loop success: runs review -> fix -> verify(clean) -> exits.
# 6. use_github_state: true vs false.
# 7. push bot identity: _commit_and_push_if_changed sets correct git env.
# 8. Failed push aborts loop.

@pytest.fixture
def dummy_context():
    return ReviewLoopContext(
        pr_url="https://github.com/owner/repo/pull/1",
        pr_owner="owner",
        pr_repo="repo",
        pr_number=1,
        issue_url="https://github.com/owner/repo/issues/2",
        issue_owner="owner",
        issue_repo="repo",
        issue_number=2,
        issue_title="Example Issue",
        architecture_json="{}",
        pddrc_content="",
    )

def test_parse_reviewers():
    # Defaults/None
    assert parse_reviewers(None) == ()
    # Aliases and comma/space splitting
    assert parse_reviewers("chatgpt, anthropic   google") == ("codex", "claude", "gemini")
    assert parse_reviewers(["openai", "claude, unknown"]) == ("codex", "claude")

def test_role_uniqueness_fast_fail(dummy_context, tmp_path):
    config = ReviewLoopConfig(reviewer="codex", fixer="chatgpt", max_rounds=1)
    
    success, report, cost, model = run_checkup_review_loop(
        context=dummy_context,
        config=config,
        cwd=tmp_path,
        quiet=True,
    )
    
    assert success is True
    assert "must be different roles" in report
    assert "reviewer-status: codex=failed" in report

@patch("pdd.checkup_review_loop._post_final_report_to_github")
@patch("pdd.checkup_review_loop._invoke_agentic")
@patch("pdd.checkup_review_loop._setup_pr_worktree")
@patch("pdd.checkup_review_loop._fetch_pr_metadata")
def test_review_only_mode(mock_fetch, mock_setup, mock_invoke, mock_post, dummy_context, tmp_path):
    mock_setup.return_value = (tmp_path / "worktree", None)
    mock_fetch.return_value = ({}, None)
    mock_invoke.return_value = (True, '{"status": "clean", "findings": []}', 0.1, "test-model")
    
    config = ReviewLoopConfig(review_only=True)
    
    success, report, cost, model = run_checkup_review_loop(
        context=dummy_context,
        config=config,
        cwd=tmp_path,
        quiet=True,
    )
    
    assert success is True
    assert mock_invoke.call_count == 1
    # Check that cwd was worktree
    mock_invoke.assert_called_with(
        prompt=mock_invoke.call_args[1]["prompt"],
        role="codex",
        cwd=tmp_path / "worktree",
        label="checkup-review-r1-review-codex",
        verbose=False,
        quiet=True
    )
    mock_post.assert_called_once()
    assert "review-only mode" in report

@patch("pdd.checkup_review_loop._post_final_report_to_github")
@patch("pdd.checkup_review_loop._commit_and_push_if_changed")
@patch("pdd.checkup_review_loop._invoke_agentic")
@patch("pdd.checkup_review_loop._setup_pr_worktree")
@patch("pdd.checkup_review_loop._fetch_pr_metadata")
def test_full_loop_success(mock_fetch, mock_setup, mock_invoke, mock_push, mock_post, dummy_context, tmp_path):
    mock_setup.return_value = (tmp_path / "worktree", None)
    mock_fetch.return_value = ({}, None)
    mock_push.return_value = (True, "pushed")
    
    # 1. review: findings
    # 2. fix: success
    # 3. verify: clean
    mock_invoke.side_effect = [
        (True, '{"status": "findings", "findings": [{"severity": "critical", "location": "file.py:1", "finding": "bug", "required_fix": "fix it"}]}', 0.1, "test-model"),
        (True, '{"summary": "fixed", "changed_files": ["file.py"], "dispositions": {"critical|file.py:1|bug|fix it": "fixed"}, "rationales": {}}', 0.2, "test-model"),
        (True, '{"status": "clean", "findings": []}', 0.1, "test-model"),
    ]
    
    config = ReviewLoopConfig(max_rounds=2)
    
    success, report, cost, model = run_checkup_review_loop(
        context=dummy_context,
        config=config,
        cwd=tmp_path,
        quiet=True,
        use_github_state=False
    )
    
    assert success is True
    assert mock_invoke.call_count == 3
    assert mock_push.call_count == 1
    mock_post.assert_not_called()  # use_github_state=False
    assert "fresh-final-review: clean" in report
    
@patch("subprocess.run")
@patch("pdd.checkup_review_loop._fetch_pr_metadata")
@patch("pdd.checkup_review_loop.push_with_retry")
def test_commit_and_push_bot_identity(mock_push, mock_fetch, mock_run, tmp_path):
    mock_fetch.return_value = ({"clone_url": "url", "head_ref": "branch"}, None)
    # mock git status to return something
    mock_run.side_effect = [
        MagicMock(returncode=0, stdout=" M file.py\n", stderr=""), # status
        MagicMock(returncode=0, stdout="", stderr=""), # add
        MagicMock(returncode=0, stdout="", stderr=""), # commit
        MagicMock(returncode=0, stdout="", stderr=""), # remote remove
        MagicMock(returncode=0, stdout="", stderr=""), # remote add
        MagicMock(returncode=0, stdout="", stderr=""), # remote remove (finally)
    ]
    mock_push.return_value = (True, "msg")
    
    pushed, msg = _commit_and_push_if_changed(
        tmp_path, "owner", "repo", 1, commit_message="msg", quiet=True
    )
    
    assert pushed is True
    
    # Check commit environment
    commit_call = mock_run.call_args_list[2]
    assert commit_call[0][0][:2] == ["git", "commit"]
    env = commit_call[1]["env"]
    assert env["GIT_AUTHOR_NAME"] == "PDD Bot"
    assert env["GIT_AUTHOR_EMAIL"] == "pdd-bot@users.noreply.github.com"
    assert env["GIT_COMMITTER_NAME"] == "PDD Bot"
    assert env["GIT_COMMITTER_EMAIL"] == "pdd-bot@users.noreply.github.com"


def test_parse_reviewers_empty():
    assert parse_reviewers("") == ()
    assert parse_reviewers([]) == ()

@patch("pdd.checkup_review_loop._post_final_report_to_github")
@patch("pdd.checkup_review_loop._setup_pr_worktree")
@patch("pdd.checkup_review_loop._fetch_pr_metadata")
def test_setup_worktree_failure(mock_fetch, mock_setup, mock_post, dummy_context, tmp_path):
    mock_setup.return_value = (None, "git fetch failed")
    mock_fetch.return_value = ({}, None)
    
    config = ReviewLoopConfig(max_rounds=1)
    success, report, cost, model = run_checkup_review_loop(
        context=dummy_context, config=config, cwd=tmp_path, quiet=True
    )
    
    assert success is True
    assert "git fetch failed" in report

@patch("pdd.checkup_review_loop._post_final_report_to_github")
@patch("pdd.checkup_review_loop._invoke_agentic")
@patch("pdd.checkup_review_loop._setup_pr_worktree")
@patch("pdd.checkup_review_loop._fetch_pr_metadata")
def test_fallback_reviewer(mock_fetch, mock_setup, mock_invoke, mock_post, dummy_context, tmp_path):
    mock_setup.return_value = (tmp_path / "worktree", None)
    mock_fetch.return_value = ({}, None)
    
    # Primary fails -> fallback succeeds
    mock_invoke.side_effect = [
        (True, '{"status": "failed", "findings": []}', 0.1, "test-model"),
        (True, '{"status": "failed", "findings": []}', 0.1, "test-model"),
        (True, '{"status": "clean", "findings": []}', 0.1, "test-model"),
    ]
    
    config = ReviewLoopConfig(reviewer="codex", reviewer_fallback="gemini", max_rounds=1)
    
    success, report, cost, model = run_checkup_review_loop(
        context=dummy_context, config=config, cwd=tmp_path, quiet=True
    )
    
    assert success is True
    assert "reviewer-status: codex=failed" in report
    assert "gemini=clean" in report
    assert "fresh-final-review: clean" in report

@patch("pdd.checkup_review_loop._post_final_report_to_github")
@patch("pdd.checkup_review_loop._commit_and_push_if_changed")
@patch("pdd.checkup_review_loop._invoke_agentic")
@patch("pdd.checkup_review_loop._setup_pr_worktree")
@patch("pdd.checkup_review_loop._fetch_pr_metadata")
def test_push_failure_aborts(mock_fetch, mock_setup, mock_invoke, mock_push, mock_post, dummy_context, tmp_path):
    mock_setup.return_value = (tmp_path / "worktree", None)
    mock_fetch.return_value = ({}, None)
    mock_push.return_value = (False, "git push failed")
    
    mock_invoke.side_effect = [
        (True, '{"status": "findings", "findings": [{"severity": "critical", "location": "file.py:1", "finding": "bug", "required_fix": "fix it"}]}', 0.1, "test-model"),
        (True, '{"summary": "fixed", "changed_files": ["file.py"], "dispositions": {"critical|file.py:1|bug|fix it": "fixed"}, "rationales": {}}', 0.2, "test-model"),
    ]
    
    config = ReviewLoopConfig(max_rounds=1)
    
    success, report, cost, model = run_checkup_review_loop(
        context=dummy_context, config=config, cwd=tmp_path, quiet=True
    )
    
    assert success is True
    assert "push failed in round 1: git push failed" in report

@patch("subprocess.run")
def test_commit_and_push_no_changes(mock_run, tmp_path):
    # status returns nothing
    mock_run.return_value = MagicMock(returncode=0, stdout="", stderr="")
    
    pushed, msg = _commit_and_push_if_changed(
        tmp_path, "owner", "repo", 1, commit_message="msg", quiet=True
    )
    
    assert pushed is True
    assert "no changes to commit" in msg

