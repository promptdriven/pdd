from __future__ import annotations

import io
import subprocess
import zipfile
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.ci_validation import (
    _classify_check_result,
    _collect_failure_logs,
    _poll_required_checks,
    detect_ci_system,
    post_ci_failure_comment,
    run_ci_validation_loop,
)


def _build_log_zip(*, filename: str = "job.txt", body: str = "failure details") -> bytes:
    """Build an in-memory GitHub Actions log archive."""
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, "w") as archive:
        archive.writestr(filename, body)
    return buffer.getvalue()


def test_detect_ci_system_recognizes_common_configs(tmp_path: Path) -> None:
    """CI detection should key off standard repository config locations."""
    assert detect_ci_system(tmp_path) == "unknown"

    (tmp_path / ".github" / "workflows").mkdir(parents=True)
    assert detect_ci_system(tmp_path) == "github_actions"


def test_post_ci_failure_comment_uses_shared_helper(tmp_path: Path) -> None:
    """Failure summaries should be posted through post_pr_comment."""
    with patch("pdd.ci_validation.post_pr_comment", return_value=True) as mock_post:
        posted = post_ci_failure_comment(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            failures=["lint failed", "unit tests failed"],
            attempts=3,
            cwd=tmp_path,
        )

    assert posted is True
    kwargs = mock_post.call_args.kwargs
    assert kwargs["repo_owner"] == "owner"
    assert kwargs["repo_name"] == "repo"
    assert kwargs["pr_number"] == 42
    assert "CI validation exhausted its retry budget." in kwargs["body"]
    assert "Ran automated CI fix iterations: 3" in kwargs["body"]
    assert "lint failed" in kwargs["body"]


def test_poll_required_checks_waits_for_matching_head(tmp_path: Path) -> None:
    """Polling should ignore stale checks until GitHub reports the new PR head SHA."""
    check_result = subprocess.CompletedProcess(
        args=[],
        returncode=0,
        stdout='[{"name":"lint","state":"SUCCESS","bucket":"pass","link":"https://example.test/lint"}]',
        stderr="",
    )

    with patch("pdd.ci_validation._get_pr_head_sha", side_effect=["oldsha", "newsha"]), \
         patch("pdd.ci_validation._run_gh", return_value=check_result) as mock_run_gh, \
         patch("pdd.ci_validation.time.sleep", return_value=None), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0, 2.0]):
        status, checks = _poll_required_checks(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            cwd=tmp_path,
            expected_head_sha="newsha",
            quiet=True,
        )

    assert status == "passed"
    assert checks == [
        {
            "name": "lint",
            "state": "SUCCESS",
            "bucket": "pass",
            "link": "https://example.test/lint",
        }
    ]
    assert mock_run_gh.call_count == 1


def test_collect_failure_logs_uses_zip_api_fallback(tmp_path: Path) -> None:
    """If `gh run view --log-failed` is empty, the Actions zip API should be used."""
    payload = _build_log_zip(filename="job.txt", body="line 1\nline 2")
    binary_result = subprocess.CompletedProcess(args=[], returncode=0, stdout=payload, stderr=b"")

    with patch(
        "pdd.ci_validation._load_failed_runs",
        return_value=[{"databaseId": 99, "name": "lint", "workflowName": "lint"}],
    ), patch("pdd.ci_validation._fetch_failed_run_view_log", return_value=""), \
         patch("pdd.ci_validation._run_gh_bytes", return_value=binary_result):
        logs = _collect_failure_logs(
            repo_owner="owner",
            repo_name="repo",
            cwd=tmp_path,
            head_sha="sha123",
            failures=[{"name": "lint", "state": "FAILURE", "bucket": "fail", "link": "https://example.test/lint"}],
        )

    assert "job.txt" in logs
    assert "line 1" in logs


def test_collect_failure_logs_falls_back_to_links(tmp_path: Path) -> None:
    """When no run logs are available, the check URLs should be surfaced."""
    with patch("pdd.ci_validation._load_failed_runs", return_value=[]):
        logs = _collect_failure_logs(
            repo_owner="owner",
            repo_name="repo",
            cwd=tmp_path,
            head_sha="sha123",
            failures=[{"name": "lint", "state": "FAILURE", "bucket": "fail", "link": "https://example.test/lint"}],
        )

    assert "No failed run logs were available via `gh`." in logs
    assert "https://example.test/lint" in logs


def test_run_ci_validation_loop_skips_without_open_pr(tmp_path: Path) -> None:
    """The loop should succeed with an informational message when no PR is open."""
    with patch("pdd.ci_validation._find_open_pr_number", return_value=None):
        success, message, cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            issue_number=822,
            max_retries=1,
            step_template="unused",
            run_agentic_task_fn=lambda **_: (True, "CI_FIX_APPLIED", 0.0, "mock"),
            timeout=60.0,
            quiet=True,
        )

    assert success is True
    assert "No open PR found" in message
    assert cost == 0.0


def test_run_ci_validation_loop_returns_no_checks_when_ci_absent(tmp_path: Path) -> None:
    """The loop should not fail repositories that have no required CI checks."""
    with patch("pdd.ci_validation._find_open_pr_number", return_value=42), \
         patch("pdd.ci_validation._get_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._poll_required_checks", return_value=("no_checks", [])), \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            issue_number=822,
            max_retries=1,
            step_template="unused",
            run_agentic_task_fn=lambda **_: (True, "CI_FIX_APPLIED", 0.0, "mock"),
            timeout=60.0,
            quiet=True,
        )

    assert success is True
    assert message == "No CI checks detected"
    assert cost == 0.0


def test_run_ci_validation_loop_retries_and_commits_fix(tmp_path: Path) -> None:
    """A failing required check should trigger one fix attempt, commit, and repoll."""
    failing_checks = [
        {"name": "lint", "state": "FAILURE", "bucket": "fail", "link": "https://example.test/lint"}
    ]
    passing_checks = [
        {"name": "lint", "state": "SUCCESS", "bucket": "pass", "link": "https://example.test/lint"}
    ]
    captured: dict[str, object] = {}

    def fake_run_agentic_task(**kwargs: object) -> tuple[bool, str, float, str]:
        captured.update(kwargs)
        return True, "CI_FIX_APPLIED\nFILES_MODIFIED: pdd/ci_validation.py", 0.25, "mock-model"

    with patch("pdd.ci_validation._find_open_pr_number", return_value=42), \
         patch("pdd.ci_validation.detect_ci_system", return_value="github_actions"), \
         patch("pdd.ci_validation._get_head_sha", side_effect=["sha123", "sha456"]), \
         patch(
             "pdd.ci_validation._poll_required_checks",
             side_effect=[("failed", failing_checks), ("passed", passing_checks)],
         ), \
         patch("pdd.ci_validation._collect_failure_logs", return_value="flake8: unused import"), \
         patch("pdd.ci_validation._commit_ci_fix", return_value=(True, "Committed and pushed 1 CI fix file(s)")) as mock_commit, \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            issue_number=822,
            max_retries=2,
            step_template="Checks:\n{ci_check_results}\nLogs:\n{ci_failure_logs}",
            run_agentic_task_fn=fake_run_agentic_task,
            timeout=120.0,
            quiet=True,
        )

    assert success is True
    assert message == "Required CI checks passed"
    assert cost == pytest.approx(0.25)
    assert "flake8: unused import" in str(captured["instruction"])
    assert "bucket=fail" in str(captured["instruction"])
    assert captured["label"] == "ci_validation_attempt1"
    mock_commit.assert_called_once_with(
        cwd=tmp_path,
        repo_owner="owner",
        repo_name="repo",
        issue_number=822,
    )


def test_run_ci_validation_loop_requires_ci_fix_marker(tmp_path: Path) -> None:
    """A task output without CI_FIX_APPLIED should stop before commit/push."""
    failing_checks = [
        {"name": "lint", "state": "FAILURE", "bucket": "fail", "link": "https://example.test/lint"}
    ]

    with patch("pdd.ci_validation._find_open_pr_number", return_value=42), \
         patch("pdd.ci_validation._get_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._poll_required_checks", return_value=("failed", failing_checks)), \
         patch("pdd.ci_validation._collect_failure_logs", return_value="flake8: unused import"), \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True) as mock_comment, \
         patch("pdd.ci_validation._commit_ci_fix") as mock_commit, \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            issue_number=822,
            max_retries=2,
            step_template="Checks:\n{ci_check_results}\nLogs:\n{ci_failure_logs}",
            run_agentic_task_fn=lambda **_: (True, "No changes made", 0.1, "mock-model"),
            timeout=120.0,
            quiet=True,
        )

    assert success is False
    assert message == "CI fix task did not apply an actionable fix"
    assert cost == pytest.approx(0.1)
    mock_commit.assert_not_called()
    mock_comment.assert_called_once()


def test_run_ci_validation_loop_returns_failure_summary_after_retry_budget(tmp_path: Path) -> None:
    """Exhausting retries should return the remaining failure summary and comment on the PR."""
    failing_checks = [
        {"name": "lint", "state": "FAILURE", "bucket": "fail", "link": "https://example.test/lint"}
    ]

    with patch("pdd.ci_validation._find_open_pr_number", return_value=42), \
         patch("pdd.ci_validation._get_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._poll_required_checks", return_value=("failed", failing_checks)), \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True) as mock_comment, \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            issue_number=822,
            max_retries=0,
            step_template="unused",
            run_agentic_task_fn=lambda **_: (True, "CI_FIX_APPLIED", 0.0, "mock-model"),
            timeout=120.0,
            quiet=True,
        )

    assert success is False
    assert message == "- lint: bucket=fail, state=FAILURE, link=https://example.test/lint"
    assert cost == 0.0
    kwargs = mock_comment.call_args.kwargs
    assert kwargs["attempts"] == 0
    assert kwargs["failures"] == [message]


# ---------------------------------------------------------------------------
# Issue #1025: _classify_check_result unit tests
# ---------------------------------------------------------------------------


def test_classify_no_checks_exit_code_1_returns_failed() -> None:
    """Without stderr context, exit 1 + empty checks falls through to 'failed'."""
    assert _classify_check_result(1, []) == "failed"


def test_classify_failed_checks_exit_code_1_returns_failed() -> None:
    """Real failures with a 'fail' bucket must still be detected."""
    checks = [{"name": "lint", "state": "FAILURE", "bucket": "fail", "link": ""}]
    assert _classify_check_result(1, checks) == "failed"


def test_classify_passing_checks_exit_code_0_returns_passed() -> None:
    """Happy path: all checks in 'pass' bucket returns 'passed'."""
    checks = [{"name": "lint", "state": "SUCCESS", "bucket": "pass", "link": ""}]
    assert _classify_check_result(0, checks) == "passed"


def test_classify_empty_checks_exit_code_0_returns_passed() -> None:
    """Exit 0 with no checks falls through to 'passed' via returncode."""
    assert _classify_check_result(0, []) == "passed"


def test_classify_pending_checks_returns_pending() -> None:
    """Pending bucket detection is unchanged."""
    checks = [{"name": "build", "state": "IN_PROGRESS", "bucket": "pending", "link": ""}]
    assert _classify_check_result(8, checks) == "pending"


# ---------------------------------------------------------------------------
# Issue #1025: poller distinguishes "no required checks" from errors
# ---------------------------------------------------------------------------


def test_poll_returns_no_checks_when_gh_reports_no_required_checks(tmp_path: Path) -> None:
    """_poll_required_checks should return no_checks when gh exits 1 with empty stdout."""
    empty_result = subprocess.CompletedProcess(
        args=[],
        returncode=1,
        stdout="",
        stderr="no required checks reported on the 'fix/issue-1020' branch",
    )

    with patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._run_gh", return_value=empty_result), \
         patch("pdd.ci_validation.time.sleep", return_value=None), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0]):
        status, checks = _poll_required_checks(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            cwd=tmp_path,
            expected_head_sha="sha123",
            quiet=True,
        )

    assert status == "no_checks"
    assert checks == []


def test_poll_does_not_return_no_checks_on_auth_error(tmp_path: Path) -> None:
    """Auth/network errors (exit 1, empty stdout) must NOT be misclassified as no_checks."""
    auth_error_result = subprocess.CompletedProcess(
        args=[],
        returncode=1,
        stdout="",
        stderr="HTTP 401: Bad credentials (https://api.github.com/graphql)",
    )

    call_count = 0

    def counting_run_gh(*args: object, **kwargs: object) -> subprocess.CompletedProcess[str]:
        nonlocal call_count
        call_count += 1
        return auth_error_result

    # monotonic returns: 0 (loop start), 1 (first iter), 2 (second iter), 9999 (exceed MAX_POLL)
    with patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._run_gh", side_effect=counting_run_gh), \
         patch("pdd.ci_validation.time.sleep", return_value=None), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0, 2.0, 9999.0]):
        status, checks = _poll_required_checks(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            cwd=tmp_path,
            expected_head_sha="sha123",
            quiet=True,
        )

    # Should time out, NOT return "no_checks"
    assert status == "timeout"
    assert call_count >= 2, "Should have retried polling, not exited immediately"


def test_poll_returns_no_checks_on_resource_not_accessible(tmp_path: Path) -> None:
    """GitHub App tokens on fork repos may lack checks:read, returning
    'Resource not accessible by integration'. Should skip CI validation
    instead of polling until timeout."""
    inaccessible_result = subprocess.CompletedProcess(
        args=[],
        returncode=1,
        stdout="",
        stderr="GraphQL: Resource not accessible by integration (node.statusCheckRollup)",
    )

    with patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._run_gh", return_value=inaccessible_result), \
         patch("pdd.ci_validation.time.sleep", return_value=None), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0]):
        status, checks = _poll_required_checks(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            cwd=tmp_path,
            expected_head_sha="sha123",
            quiet=False,
        )

    assert status == "no_checks", (
        f"Expected 'no_checks' when GitHub App lacks checks:read, got '{status}'. "
        "Without this fix, CI polling times out after MAX_POLL_SECONDS."
    )
    assert checks == []


def test_ci_validation_loop_succeeds_without_fix_loop_when_no_required_checks(tmp_path: Path) -> None:
    """End-to-end: no required checks should succeed without ever calling the LLM fix task."""
    empty_result = subprocess.CompletedProcess(
        args=[],
        returncode=1,
        stdout="",
        stderr="no required checks reported on the 'fix/issue-1020' branch",
    )

    fix_was_called = False

    def fail_if_called(**kwargs: object) -> tuple[bool, str, float, str]:
        nonlocal fix_was_called
        fix_was_called = True
        return True, "CI_FIX_APPLIED", 0.0, "mock"

    with patch("pdd.ci_validation._find_open_pr_number", return_value=42), \
         patch("pdd.ci_validation._get_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._run_gh", return_value=empty_result), \
         patch("pdd.ci_validation.time.sleep", return_value=None), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0, 2.0, 3.0]):
        success, message, cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            issue_number=1025,
            max_retries=1,
            step_template="unused",
            run_agentic_task_fn=fail_if_called,
            timeout=60.0,
            quiet=True,
        )

    assert success is True
    assert message == "No CI checks detected"
    assert cost == 0.0
    assert not fix_was_called, "LLM fix loop should not be entered when no required checks exist"
