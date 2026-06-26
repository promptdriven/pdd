from __future__ import annotations

import io
import json
import subprocess
import zipfile
from pathlib import Path
from unittest.mock import patch

import pytest

from pdd.ci_validation import (
    _classify_check_result,
    _classify_external_ci_failure,
    _collect_failure_logs,
    _configured_manual_trigger_comment,
    _poll_check_runs_for_head,
    _poll_required_checks,
    detect_ci_system,
    post_ci_failure_comment,
    run_github_checks_gate,
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
    """Polling should wait for passing checks on the expected PR head SHA."""
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
    assert mock_run_gh.call_count == 2


def test_poll_required_checks_reads_terminal_failure_on_stale_live_head(tmp_path: Path) -> None:
    """A stale expected head must not hide terminal live-head check failures."""
    check_result = subprocess.CompletedProcess(
        args=[],
        returncode=1,
        stdout=(
            '[{"name":"unit tests","state":"FAILURE",'
            '"bucket":"fail","link":"https://example.test/tests"}]'
        ),
        stderr="",
    )

    with patch("pdd.ci_validation._get_pr_head_sha", return_value="livehead"), \
         patch("pdd.ci_validation._run_gh", return_value=check_result), \
         patch("pdd.ci_validation.time.sleep", return_value=None), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0]):
        status, checks = _poll_required_checks(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            cwd=tmp_path,
            expected_head_sha="stalehead",
            quiet=True,
        )

    assert status == "failed"
    assert checks == [
        {
            "name": "unit tests",
            "state": "FAILURE",
            "bucket": "fail",
            "link": "https://example.test/tests",
        }
    ]


def test_poll_required_checks_reports_stale_head_after_timeout(tmp_path: Path) -> None:
    """If the expected head never becomes live, return an actionable diagnostic."""
    check_result = subprocess.CompletedProcess(
        args=[],
        returncode=0,
        stdout='[{"name":"lint","state":"SUCCESS","bucket":"pass","link":"https://example.test/lint"}]',
        stderr="",
    )

    with patch("pdd.ci_validation._get_pr_head_sha", return_value="livehead"), \
         patch("pdd.ci_validation._run_gh", return_value=check_result), \
         patch("pdd.ci_validation.time.sleep", return_value=None), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0, 9999.0]):
        status, checks = _poll_required_checks(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            cwd=tmp_path,
            expected_head_sha="stalehead",
            quiet=True,
        )

    assert status == "stale_head"
    summary = checks[0]["state"]
    assert "PR #42 head did not match" in summary
    assert "stalehead" in summary
    assert "livehead" in summary
    assert "lint" in summary


def test_poll_required_checks_does_not_accept_action_required_on_stale_head(
    tmp_path: Path,
) -> None:
    """ACTION_REQUIRED on the wrong live head must not satisfy an expected-head poll."""
    check_result = subprocess.CompletedProcess(
        args=[],
        returncode=1,
        stdout=(
            '[{"name":"auto-heal-pr","state":"ACTION_REQUIRED",'
            '"bucket":"fail","link":"https://example.test/manual"}]'
        ),
        stderr="",
    )

    with patch("pdd.ci_validation._get_pr_head_sha", return_value="livehead"), \
         patch("pdd.ci_validation._run_gh", return_value=check_result), \
         patch("pdd.ci_validation.time.sleep", return_value=None), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0, 9999.0]):
        status, checks = _poll_required_checks(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            cwd=tmp_path,
            expected_head_sha="expectedhead",
            quiet=True,
        )

    assert status == "stale_head"
    summary = checks[0]["state"]
    assert "expectedhead" in summary
    assert "livehead" in summary
    assert "auto-heal-pr" in summary


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
    """The loop should not fail repositories that genuinely have no required CI checks.

    Under the issue #1587 fail-closed contract, a ``no_checks`` result from the
    ``--required`` poll is cross-checked against the live head's real check runs.
    Here that REST cross-check also reports ``no_checks`` (the repo truly has no
    CI), so the loop is still allowed to treat the PR as ready.
    """
    with patch("pdd.ci_validation._find_open_pr_number", return_value=42), \
         patch("pdd.ci_validation._get_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._poll_required_checks", return_value=("no_checks", [])), \
         patch("pdd.ci_validation._poll_check_runs_for_head", return_value=("no_checks", [])), \
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


def test_run_ci_validation_loop_ready_when_required_no_checks_but_head_passing(
    tmp_path: Path,
) -> None:
    """A ``no_checks`` rollup must not fail a PR whose live head checks all PASS.

    The issue #1587 cross-check exists for the case where ``gh pr checks
    --required`` cannot read the GraphQL ``statusCheckRollup`` (App token
    permissions). When the REST Checks API instead shows the live head's real
    check runs are all green, the PR is genuinely ready: the loop must return
    success and must NOT drive a fix loop against an already-passing PR.
    Falling through to the failure path here would be an over-correction of the
    original fail-open bug.
    """
    passing = [{"name": "build", "state": "SUCCESS", "bucket": "pass", "link": ""}]

    def fail_if_called(**_kwargs: object) -> tuple[bool, str, float, str]:
        raise AssertionError("fix loop must not run when live head checks pass")

    with patch("pdd.ci_validation._find_open_pr_number", return_value=42), \
         patch("pdd.ci_validation._get_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value="livehead0"), \
         patch("pdd.ci_validation._poll_required_checks", return_value=("no_checks", [])), \
         patch("pdd.ci_validation._poll_check_runs_for_head", return_value=("passed", passing)), \
         patch("pdd.ci_validation.post_ci_failure_comment") as mock_comment, \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            issue_number=1587,
            max_retries=2,
            step_template="unused",
            run_agentic_task_fn=fail_if_called,
            timeout=60.0,
            quiet=True,
        )

    assert success is True
    assert "passed on live PR head" in message
    assert "livehead" in message
    assert cost == 0.0
    mock_comment.assert_not_called()


def test_github_checks_gate_passes_all_checks_on_current_head(tmp_path: Path) -> None:
    """Final gate strict mode should pass only when real checks pass."""
    passing_checks = [
        {"name": "lint", "state": "SUCCESS", "bucket": "pass", "link": "https://example.test/lint"}
    ]
    captured: dict[str, object] = {}

    def fake_poll(*_args, **kwargs):  # noqa: ANN001
        captured.update(kwargs)
        return "passed", passing_checks

    with patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._poll_check_runs_for_head", side_effect=fake_poll), \
         patch("pdd.ci_validation._poll_required_checks") as mock_required_poll:
        success, message, head_sha = run_github_checks_gate(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            quiet=True,
        )

    assert success is True
    assert head_sha == "sha123"
    assert "passed on PR head sha123" in message
    assert captured["head_sha"] == "sha123"
    mock_required_poll.assert_not_called()


def test_github_checks_gate_fails_when_checks_missing(tmp_path: Path) -> None:
    """No checks is success for the legacy CI-fix loop, but failure for final gate."""
    with patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._poll_check_runs_for_head", return_value=("no_checks", [])):
        success, message, head_sha = run_github_checks_gate(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            quiet=True,
        )

    assert success is False
    assert head_sha == "sha123"
    assert "missing or unreadable" in message


def test_github_checks_gate_fails_when_any_check_skipped(tmp_path: Path) -> None:
    """Skipped GitHub checks are not full-suite evidence."""
    skipped_checks = [
        {"name": "full suite", "state": "SKIPPING", "bucket": "skipping", "link": ""}
    ]

    with patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._poll_check_runs_for_head", return_value=("passed", skipped_checks)):
        success, message, _head_sha = run_github_checks_gate(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            quiet=True,
        )

    assert success is False
    assert "skipped checks" in message


def test_github_checks_gate_fails_unknown_check_bucket(tmp_path: Path) -> None:
    """Unknown check states are not trustworthy full-suite evidence."""
    unknown_checks = [
        {"name": "full suite", "state": "SUCCESS", "bucket": "", "link": ""}
    ]

    with patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._poll_check_runs_for_head", return_value=("passed", unknown_checks)):
        success, message, _head_sha = run_github_checks_gate(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            quiet=True,
        )

    assert success is False
    assert "unknown check states" in message


def test_github_checks_gate_fails_action_required_check(tmp_path: Path) -> None:
    """Manual-action checks are inconclusive for fix, but fail the strict gate."""
    action_required_checks = [
        {
            "name": "manual trigger",
            "state": "ACTION_REQUIRED",
            "bucket": "action_required",
            "link": "https://example.test/manual",
        }
    ]

    with patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch(
             "pdd.ci_validation._poll_check_runs_for_head",
             return_value=("action_required", action_required_checks),
         ):
        success, message, head_sha = run_github_checks_gate(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            quiet=True,
        )

    assert success is False
    assert head_sha == "sha123"
    assert "manual action" in message
    assert "manual trigger" in message


def test_github_checks_gate_required_only_uses_required_pr_checks(tmp_path: Path) -> None:
    """The required-only legacy path still uses `gh pr checks --required`."""
    passing_checks = [
        {"name": "required lint", "state": "SUCCESS", "bucket": "pass", "link": ""}
    ]
    captured: dict[str, object] = {}

    def fake_poll(*_args, **kwargs):  # noqa: ANN001
        captured.update(kwargs)
        return "passed", passing_checks

    with patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._poll_required_checks", side_effect=fake_poll), \
         patch("pdd.ci_validation._poll_check_runs_for_head") as mock_check_runs_poll:
        success, message, head_sha = run_github_checks_gate(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            quiet=True,
            required_only=True,
        )

    assert success is True
    assert head_sha == "sha123"
    assert "required GitHub checks passed" in message
    assert captured["expected_head_sha"] == "sha123"
    assert captured["required_only"] is True
    mock_check_runs_poll.assert_not_called()


def test_poll_check_runs_for_head_passes_completed_success(tmp_path: Path) -> None:
    """Final gate can read real check runs without GraphQL statusCheckRollup."""
    payload = {
        "check_runs": [
            {
                "name": "full-suite",
                "status": "completed",
                "conclusion": "success",
                "html_url": "https://example.test/check",
            }
        ]
    }
    result = subprocess.CompletedProcess(args=[], returncode=0, stdout=json.dumps(payload), stderr="")

    with patch("pdd.ci_validation._run_gh_api", return_value=result) as mock_run, \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0]):
        status, checks = _poll_check_runs_for_head(
            repo_owner="owner",
            repo_name="repo",
            cwd=tmp_path,
            head_sha="sha123",
            quiet=True,
        )

    assert status == "passed"
    assert checks == [
        {
            "name": "full-suite",
            "state": "SUCCESS",
            "bucket": "pass",
            "link": "https://example.test/check",
        }
    ]
    assert mock_run.call_args.args[1] == ["repos/owner/repo/commits/sha123/check-runs?per_page=100"]


def test_poll_check_runs_for_head_fails_completed_failure(tmp_path: Path) -> None:
    """Failed check-run conclusions are hard final-gate failures."""
    payload = {
        "check_runs": [
            {
                "name": "full-suite",
                "status": "completed",
                "conclusion": "failure",
                "html_url": "https://example.test/check",
            }
        ]
    }
    result = subprocess.CompletedProcess(args=[], returncode=0, stdout=json.dumps(payload), stderr="")

    with patch("pdd.ci_validation._run_gh_api", return_value=result), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0]):
        status, checks = _poll_check_runs_for_head(
            repo_owner="owner",
            repo_name="repo",
            cwd=tmp_path,
            head_sha="sha123",
            quiet=True,
        )

    assert status == "failed"
    assert checks[0]["bucket"] == "fail"


def test_poll_check_runs_for_head_action_required_is_manual_action(
    tmp_path: Path,
) -> None:
    """REST action_required conclusions should not be normalized as code failures."""
    payload = {
        "check_runs": [
            {
                "name": "auto-heal-pr",
                "status": "completed",
                "conclusion": "action_required",
                "html_url": "https://example.test/manual-trigger",
            }
        ]
    }
    result = subprocess.CompletedProcess(args=[], returncode=0, stdout=json.dumps(payload), stderr="")

    with patch("pdd.ci_validation._run_gh_api", return_value=result), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0]):
        status, checks = _poll_check_runs_for_head(
            repo_owner="owner",
            repo_name="repo",
            cwd=tmp_path,
            head_sha="sha123",
            quiet=True,
        )

    assert status == "action_required"
    assert checks == [
        {
            "name": "auto-heal-pr",
            "state": "ACTION_REQUIRED",
            "bucket": "action_required",
            "link": "https://example.test/manual-trigger",
        }
    ]


def test_poll_check_runs_for_head_fails_unknown_conclusion(tmp_path: Path) -> None:
    """Unknown completed check conclusions are not passing evidence."""
    payload = {
        "check_runs": [
            {
                "name": "full-suite",
                "status": "completed",
                "conclusion": "unexpected_new_state",
                "html_url": "https://example.test/check",
            }
        ]
    }
    result = subprocess.CompletedProcess(args=[], returncode=0, stdout=json.dumps(payload), stderr="")

    with patch("pdd.ci_validation._run_gh_api", return_value=result), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0]):
        status, checks = _poll_check_runs_for_head(
            repo_owner="owner",
            repo_name="repo",
            cwd=tmp_path,
            head_sha="sha123",
            quiet=True,
        )

    assert status == "failed"
    assert checks[0]["bucket"] == ""


def test_poll_check_runs_for_head_pending_times_out(tmp_path: Path) -> None:
    """Pending check runs fail closed after the polling timeout."""
    payload = {
        "check_runs": [
            {
                "name": "full-suite",
                "status": "in_progress",
                "conclusion": None,
                "html_url": "https://example.test/check",
            }
        ]
    }
    result = subprocess.CompletedProcess(args=[], returncode=0, stdout=json.dumps(payload), stderr="")

    with patch("pdd.ci_validation._run_gh_api", return_value=result), \
         patch("pdd.ci_validation.time.sleep", return_value=None), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0, 9999.0]):
        status, checks = _poll_check_runs_for_head(
            repo_owner="owner",
            repo_name="repo",
            cwd=tmp_path,
            head_sha="sha123",
            quiet=True,
        )

    assert status == "timeout"
    assert checks[0]["bucket"] == "pending"


def test_poll_check_runs_for_head_reports_unreadable_permission_error(tmp_path: Path) -> None:
    """Unreadable REST check-runs are distinct from a real zero-check repo."""
    result = subprocess.CompletedProcess(
        args=[],
        returncode=1,
        stdout="",
        stderr="Resource not accessible by integration",
    )

    with patch("pdd.ci_validation._run_gh_api", return_value=result), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0]):
        status, checks = _poll_check_runs_for_head(
            repo_owner="owner",
            repo_name="repo",
            cwd=tmp_path,
            head_sha="sha123",
            quiet=True,
        )

    assert status == "unreadable"
    assert checks == []


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


def test_run_ci_validation_loop_inconclusive_for_missing_google_auth_secret(
    tmp_path: Path,
) -> None:
    """CI setup/auth failures are external action, not code-fix failures."""
    failing_checks = [
        {
            "name": "build_and_preview",
            "state": "FAILURE",
            "bucket": "fail",
            "link": "https://github.com/owner/repo/actions/runs/123",
        }
    ]
    logs = (
        "Run google-github-actions/auth@v2\n"
        "Error: google-github-actions/auth failed with: the GitHub Action "
        "workflow must specify exactly one of \"workload_identity_provider\" "
        "or \"credentials_json\"! If you are specifying input via secrets, "
        "ensure the secret is being injected into the environment."
    )
    fix_was_called = False

    def fail_if_called(**_kwargs: object) -> tuple[bool, str, float, str]:
        nonlocal fix_was_called
        fix_was_called = True
        return True, "CI_FIX_APPLIED", 0.0, "mock-model"

    with patch("pdd.ci_validation._find_open_pr_number", return_value=42), \
         patch("pdd.ci_validation._get_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._poll_required_checks", return_value=("failed", failing_checks)), \
         patch("pdd.ci_validation._collect_failure_logs", return_value=logs), \
         patch("pdd.ci_validation.post_pr_comment", return_value=True) as info_comment, \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True) as failure_comment, \
         patch("pdd.ci_validation._commit_ci_fix") as mock_commit, \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            issue_number=822,
            max_retries=2,
            step_template="unused",
            run_agentic_task_fn=fail_if_called,
            timeout=120.0,
            quiet=True,
        )

    assert success is True
    assert cost == 0.0
    assert "external ci setup" in message.lower()
    assert "inconclusive" in message.lower()
    assert not fix_was_called
    mock_commit.assert_not_called()
    failure_comment.assert_not_called()
    info_comment.assert_called_once()


def test_run_ci_validation_loop_does_not_hide_mixed_failure_with_external_logs(
    tmp_path: Path,
) -> None:
    """External setup logs must not mask another failed required check."""
    failing_checks = [
        {
            "name": "deploy preview",
            "state": "FAILURE",
            "bucket": "fail",
            "link": "https://github.com/owner/repo/actions/runs/123",
        },
        {
            "name": "unit tests",
            "state": "FAILURE",
            "bucket": "fail",
            "link": "https://github.com/owner/repo/actions/runs/456",
        },
    ]
    logs = (
        "Run google-github-actions/auth@v2\n"
        "Error: google-github-actions/auth failed with: the GitHub Action "
        "workflow must specify exactly one of \"workload_identity_provider\" "
        "or \"credentials_json\"."
    )
    fix_was_called = False

    def fake_fix(**_kwargs: object) -> tuple[bool, str, float, str]:
        nonlocal fix_was_called
        fix_was_called = True
        return True, "No code changes made", 0.1, "mock-model"

    with patch("pdd.ci_validation._find_open_pr_number", return_value=42), \
         patch("pdd.ci_validation._get_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._poll_required_checks", return_value=("failed", failing_checks)), \
         patch("pdd.ci_validation._collect_failure_logs", return_value=logs), \
         patch("pdd.ci_validation.post_pr_comment", return_value=True) as info_comment, \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True) as failure_comment, \
         patch("pdd.ci_validation._commit_ci_fix") as mock_commit, \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            issue_number=822,
            max_retries=1,
            step_template="Checks:\n{ci_check_results}\nLogs:\n{ci_failure_logs}",
            run_agentic_task_fn=fake_fix,
            timeout=120.0,
            quiet=True,
        )

    assert success is False
    assert message == "CI fix task did not apply an actionable fix"
    assert cost == pytest.approx(0.1)
    assert fix_was_called
    mock_commit.assert_not_called()
    info_comment.assert_not_called()
    failure_comment.assert_called_once()


def test_configured_manual_trigger_comment_matches_check_name(tmp_path: Path) -> None:
    """Per-check manual triggers should win over the global fallback comment."""
    (tmp_path / ".pddrc").write_text(
        'version: "1.0"\n'
        'ci:\n'
        '  manual_trigger_comment: "/fallback"\n'
        '  manual_triggers:\n'
        '    auto-heal-pr: "/gcbrun"\n'
        'contexts:\n'
        '  default:\n'
        '    paths: ["**"]\n'
        '    defaults: {}\n',
        encoding="utf-8",
    )
    checks = [
        {
            "name": "auto-heal-pr (prompt-driven-development-stg)",
            "state": "ACTION_REQUIRED",
            "bucket": "action_required",
            "link": "",
        }
    ]

    assert _configured_manual_trigger_comment(tmp_path, checks) == "/gcbrun"


def test_run_ci_validation_loop_posts_multiple_configured_manual_triggers(
    tmp_path: Path,
) -> None:
    """Multiple ACTION_REQUIRED checks should each get their configured trigger."""
    (tmp_path / ".pddrc").write_text(
        'version: "1.0"\n'
        'ci:\n'
        '  manual_triggers:\n'
        '    auto-heal-pr: "/gcbrun"\n'
        '    deploy-preview: "/deployrun"\n'
        'contexts:\n'
        '  default:\n'
        '    paths: ["**"]\n'
        '    defaults: {}\n',
        encoding="utf-8",
    )
    action_required = [
        {
            "name": "auto-heal-pr",
            "state": "ACTION_REQUIRED",
            "bucket": "action_required",
            "link": "https://example.test/manual",
        },
        {
            "name": "deploy-preview",
            "state": "ACTION_REQUIRED",
            "bucket": "action_required",
            "link": "https://example.test/deploy",
        },
    ]
    passing = [
        {
            "name": "auto-heal-pr",
            "state": "SUCCESS",
            "bucket": "pass",
            "link": "https://example.test/manual",
        },
        {
            "name": "deploy-preview",
            "state": "SUCCESS",
            "bucket": "pass",
            "link": "https://example.test/deploy",
        },
    ]
    fix_was_called = False

    def fail_if_called(**_kwargs: object) -> tuple[bool, str, float, str]:
        nonlocal fix_was_called
        fix_was_called = True
        return True, "CI_FIX_APPLIED", 0.0, "mock-model"

    with patch("pdd.ci_validation._find_open_pr_number", return_value=42), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch(
             "pdd.ci_validation._poll_required_checks",
             side_effect=[
                 ("action_required", action_required),
                 ("action_required", action_required),
                 ("passed", passing),
             ],
         ) as poll_checks, \
         patch("pdd.ci_validation.post_pr_comment", return_value=True) as info_comment, \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True) as failure_comment, \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            issue_number=1740,
            max_retries=2,
            step_template="unused",
            run_agentic_task_fn=fail_if_called,
            timeout=120.0,
            quiet=True,
        )

    assert success is True
    assert message == "Required CI checks passed"
    assert cost == 0.0
    assert not fix_was_called
    assert poll_checks.call_count == 3
    assert [call.kwargs["body"] for call in info_comment.call_args_list] == [
        "/gcbrun",
        "/deployrun",
    ]
    failure_comment.assert_not_called()


def test_run_ci_validation_loop_posts_configured_manual_trigger_then_repolls(
    tmp_path: Path,
) -> None:
    """A configured ACTION_REQUIRED trigger should be posted once before repolling."""
    (tmp_path / ".pddrc").write_text(
        'version: "1.0"\n'
        'ci:\n'
        '  manual_trigger_comment: "/gcbrun"\n'
        'contexts:\n'
        '  default:\n'
        '    paths: ["**"]\n'
        '    defaults: {}\n',
        encoding="utf-8",
    )
    action_required = [
        {
            "name": "auto-heal-pr (prompt-driven-development-stg)",
            "state": "ACTION_REQUIRED",
            "bucket": "action_required",
            "link": "https://example.test/manual",
        }
    ]
    passing = [
        {
            "name": "auto-heal-pr (prompt-driven-development-stg)",
            "state": "SUCCESS",
            "bucket": "pass",
            "link": "https://example.test/manual",
        }
    ]
    fix_was_called = False

    def fail_if_called(**_kwargs: object) -> tuple[bool, str, float, str]:
        nonlocal fix_was_called
        fix_was_called = True
        return True, "CI_FIX_APPLIED", 0.0, "mock-model"

    with patch("pdd.ci_validation._find_open_pr_number", return_value=42), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch(
             "pdd.ci_validation._poll_required_checks",
             side_effect=[("action_required", action_required), ("passed", passing)],
         ) as poll_checks, \
         patch("pdd.ci_validation.post_pr_comment", return_value=True) as info_comment, \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True) as failure_comment, \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            issue_number=1740,
            max_retries=2,
            step_template="unused",
            run_agentic_task_fn=fail_if_called,
            timeout=120.0,
            quiet=True,
        )

    assert success is True
    assert message == "Required CI checks passed"
    assert cost == 0.0
    assert not fix_was_called
    assert poll_checks.call_count == 2
    assert info_comment.call_args.kwargs["body"] == "/gcbrun"
    failure_comment.assert_not_called()


def test_run_ci_validation_loop_returns_failure_summary_after_retry_budget(tmp_path: Path) -> None:
    """Exhausting retries should return the remaining failure summary and comment on the PR."""
    failing_checks = [
        {"name": "lint", "state": "FAILURE", "bucket": "fail", "link": "https://example.test/lint"}
    ]

    with patch("pdd.ci_validation._find_open_pr_number", return_value=42), \
         patch("pdd.ci_validation._get_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._poll_required_checks", return_value=("failed", failing_checks)), \
         patch("pdd.ci_validation._collect_failure_logs", return_value="flake8: unused import"), \
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
# Codex round-4 Finding 1: expected_head_sha_override
#
# When the head being validated was pushed from a SEPARATE worktree, the
# loop must not compare the remote PR head to ``_get_head_sha(cwd)`` — that
# worktree's local HEAD is stale. The override forces the loop to wait for
# the exact remote head SHA the caller supplies.
# ---------------------------------------------------------------------------


def test_run_ci_validation_loop_uses_override_when_provided(tmp_path: Path) -> None:
    captured: dict[str, object] = {}

    def fake_poll(*_args, **kwargs):  # noqa: ANN001
        captured["expected_head_sha"] = kwargs.get("expected_head_sha")
        return "passed", []

    with patch("pdd.ci_validation._find_open_pr_number", return_value=42), \
         patch("pdd.ci_validation.detect_ci_system", return_value="github_actions"), \
         patch(
             "pdd.ci_validation._get_head_sha",
             return_value="stale_local_sha_should_not_be_used",
         ), \
         patch("pdd.ci_validation._poll_required_checks", side_effect=fake_poll), \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, _msg, _cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            issue_number=822,
            max_retries=0,
            step_template="unused",
            run_agentic_task_fn=lambda **_: (True, "CI_FIX_APPLIED", 0.0, "mock"),
            timeout=60.0,
            quiet=True,
            expected_head_sha_override="post_checkup_remote_sha",
        )

    assert success is True
    assert captured["expected_head_sha"] == "post_checkup_remote_sha", (
        "Override must reach _poll_required_checks instead of _get_head_sha(cwd) — "
        "otherwise the poll would wait for the stale local HEAD and burn the timeout"
    )


def test_run_ci_validation_loop_uses_live_pr_head_without_override(
    tmp_path: Path,
) -> None:
    captured: dict[str, object] = {}

    def fake_poll(*_args, **kwargs):  # noqa: ANN001
        captured["expected_head_sha"] = kwargs.get("expected_head_sha")
        return "passed", []

    with patch("pdd.ci_validation._find_open_pr_number", return_value=42), \
         patch("pdd.ci_validation.detect_ci_system", return_value="github_actions"), \
         patch("pdd.ci_validation._get_head_sha", return_value="local_cwd_head"), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value="live_pr_head"), \
         patch("pdd.ci_validation._poll_required_checks", side_effect=fake_poll), \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            issue_number=822,
            max_retries=0,
            step_template="unused",
            run_agentic_task_fn=lambda **_: (True, "CI_FIX_APPLIED", 0.0, "mock"),
            timeout=60.0,
            quiet=True,
        )

    assert captured["expected_head_sha"] == "live_pr_head", (
        "Without an explicit override, CI validation must follow the live PR head "
        "instead of a stale local worktree HEAD."
    )


def test_run_ci_validation_loop_reports_stale_expected_head_override(
    tmp_path: Path,
) -> None:
    stale_check = {
        "name": "PR head mismatch",
        "state": (
            "PR #42 head did not match the expected CI validation head.\n"
            "- expected head: `expectedsha`\n"
            "- live PR head: `livesha`\n"
            "- last known checks:\n- lint: bucket=pass, state=SUCCESS"
        ),
        "bucket": "fail",
        "link": "",
    }

    with patch("pdd.ci_validation._find_open_pr_number", return_value=42), \
         patch("pdd.ci_validation.detect_ci_system", return_value="github_actions"), \
         patch("pdd.ci_validation._get_head_sha", return_value="local_cwd_head"), \
         patch(
             "pdd.ci_validation._poll_required_checks",
             return_value=("stale_head", [stale_check]),
         ), \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True) as mock_comment, \
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
            expected_head_sha_override="expectedsha",
        )

    assert success is False
    assert cost == 0.0
    assert "expectedsha" in message
    assert "livesha" in message
    assert "Timed out waiting for required CI checks" not in message
    assert mock_comment.call_args.kwargs["attempts"] == 0


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


def test_classify_external_ci_failure_from_google_auth_secret_log() -> None:
    """Missing GitHub Actions auth secrets should be classified before LLM repair."""
    checks = [{"name": "build_and_preview", "state": "FAILURE", "bucket": "fail", "link": ""}]
    logs = (
        "google-github-actions/auth failed with: the GitHub Action workflow "
        "must specify exactly one of workload_identity_provider or "
        "credentials_json because the secret is empty."
    )

    assert _classify_external_ci_failure(checks, logs) is not None
    assert _classify_external_ci_failure(checks, "flake8: unused import") is None


def test_classify_external_ci_failure_does_not_mask_actionable_logs() -> None:
    """Mixed external setup and code/test failures must remain repairable."""
    checks = [
        {"name": "deploy", "state": "FAILURE", "bucket": "fail", "link": ""},
        {"name": "unit tests", "state": "FAILURE", "bucket": "fail", "link": ""},
    ]
    logs = (
        "google-github-actions/auth failed because credentials_json is not supplied\n"
        "pytest tests/test_widget.py::test_widget FAILED\n"
        "AssertionError: expected 2 got 1"
    )

    assert _classify_external_ci_failure(checks, logs) is None


def test_classify_external_ci_failure_does_not_mask_unlogged_failed_check() -> None:
    """A second non-external failed check keeps CI fail-closed even if logs are auth-only."""
    checks = [
        {"name": "deploy preview", "state": "FAILURE", "bucket": "fail", "link": ""},
        {"name": "unit tests", "state": "FAILURE", "bucket": "fail", "link": ""},
    ]
    logs = (
        "google-github-actions/auth failed with: the GitHub Action workflow "
        "must specify exactly one of workload_identity_provider or credentials_json."
    )

    assert _classify_external_ci_failure(checks, logs) is None


def test_classify_action_required_check_is_manual_action() -> None:
    """ACTION_REQUIRED is terminal, but it is not a code failure to repair."""
    checks = [
        {
            "name": "auto-heal-pr",
            "state": "ACTION_REQUIRED",
            "bucket": "fail",
            "link": "https://example.test/manual-trigger",
        }
    ]
    assert _classify_check_result(1, checks) == "action_required"


def test_classify_action_required_state_wins_with_missing_bucket() -> None:
    """GitHub can report ACTION_REQUIRED with an empty bucket; keep it manual."""
    checks = [
        {
            "name": "auto-heal-pr",
            "state": "ACTION_REQUIRED",
            "bucket": "",
            "link": "https://example.test/manual-trigger",
        }
    ]
    assert _classify_check_result(1, checks) == "action_required"


def test_classify_real_failure_wins_over_action_required() -> None:
    """A real failing check must still fail closed even if another check needs action."""
    checks = [
        {
            "name": "auto-heal-pr",
            "state": "ACTION_REQUIRED",
            "bucket": "fail",
            "link": "https://example.test/manual-trigger",
        },
        {"name": "unit tests", "state": "FAILURE", "bucket": "fail", "link": ""},
    ]
    assert _classify_check_result(1, checks) == "failed"


def test_classify_pending_wins_over_action_required() -> None:
    """Do not fail open while another required check is still running."""
    checks = [
        {
            "name": "auto-heal-pr",
            "state": "ACTION_REQUIRED",
            "bucket": "fail",
            "link": "https://example.test/manual-trigger",
        },
        {"name": "github-app-ci", "state": "IN_PROGRESS", "bucket": "pending", "link": ""},
    ]
    assert _classify_check_result(8, checks) == "pending"


def test_classify_failure_state_wins_even_with_missing_bucket() -> None:
    """Malformed/missing buckets must not hide a real failed state."""
    checks = [
        {
            "name": "auto-heal-pr",
            "state": "ACTION_REQUIRED",
            "bucket": "fail",
            "link": "https://example.test/manual-trigger",
        },
        {"name": "unit tests", "state": "FAILURE", "bucket": "", "link": ""},
    ]
    assert _classify_check_result(1, checks) == "failed"


def test_classify_unknown_bucket_fails_closed() -> None:
    """A non-empty check set with unknown buckets must not pass via all([])."""
    checks = [{"name": "full suite", "state": "SUCCESS", "bucket": "", "link": ""}]
    assert _classify_check_result(0, checks) == "failed"


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
         patch("pdd.ci_validation._poll_check_runs_for_head", return_value=("no_checks", [])), \
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


# ---------------------------------------------------------------------------
# Issue #1114: partial check data + permission error bypasses handler
# ---------------------------------------------------------------------------

PARTIAL_CHECKS_STDOUT = (
    '[{"name":"build","state":"PENDING","bucket":"pending","link":""}]'
)
RESOURCE_NOT_ACCESSIBLE_STDERR = (
    "GraphQL: Resource not accessible by integration "
    "(node.statusCheckRollup.nodes.0.commit.statusCheckRollup)"
)


def test_poll_returns_no_checks_on_resource_not_accessible_with_partial_data(
    tmp_path: Path,
) -> None:
    """When gh pr checks returns partial check data in stdout AND a 'Resource
    not accessible by integration' error in stderr, the poller should return
    ('no_checks', []) immediately — not poll until timeout.

    Bug: the handler at ci_validation.py:280 is gated behind
    `not latest_checks`, so it is skipped when partial data makes
    latest_checks non-empty."""
    partial_result = subprocess.CompletedProcess(
        args=[],
        returncode=1,
        stdout=PARTIAL_CHECKS_STDOUT,
        stderr=RESOURCE_NOT_ACCESSIBLE_STDERR,
    )

    # Provide enough monotonic values: 0 (start), 1 (first iter check),
    # then 9999 to exceed MAX_POLL_SECONDS if the bug causes continued polling.
    with patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._run_gh", return_value=partial_result) as mock_run, \
         patch("pdd.ci_validation.time.sleep", return_value=None), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0, 9999.0]):
        status, checks = _poll_required_checks(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            cwd=tmp_path,
            expected_head_sha="sha123",
            quiet=True,
        )

    assert status == "no_checks", (
        f"Expected 'no_checks' when partial data accompanies permission error, got '{status}'. "
        "The 'resource not accessible' handler must fire even when latest_checks is non-empty."
    )
    assert checks == []
    # Should exit on the first poll iteration, not retry
    assert mock_run.call_count == 1


def test_poll_emits_permission_warning_with_partial_data(tmp_path: Path) -> None:
    """When partial check data + permission error occurs and quiet=False,
    the yellow 'checks:read permission' warning should be printed."""
    partial_result = subprocess.CompletedProcess(
        args=[],
        returncode=1,
        stdout=PARTIAL_CHECKS_STDOUT,
        stderr=RESOURCE_NOT_ACCESSIBLE_STDERR,
    )

    with patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._run_gh", return_value=partial_result), \
         patch("pdd.ci_validation.time.sleep", return_value=None), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0, 9999.0]), \
         patch("pdd.ci_validation.console") as mock_console:
        status, checks = _poll_required_checks(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            cwd=tmp_path,
            expected_head_sha="sha123",
            quiet=False,
        )

    assert status == "no_checks"
    assert checks == []
    # Verify the permission warning was printed
    printed_args = [str(call) for call in mock_console.print.call_args_list]
    joined = " ".join(printed_args)
    assert "checks:read" in joined, (
        f"Expected 'checks:read' permission warning in console output, got: {printed_args}"
    )


def test_ci_validation_loop_succeeds_on_partial_data_permission_error(
    tmp_path: Path,
) -> None:
    """Integration: run_ci_validation_loop should return success when the
    poller encounters partial check data + 'Resource not accessible' error,
    not time out and post a failure comment."""
    partial_result = subprocess.CompletedProcess(
        args=[],
        returncode=1,
        stdout=PARTIAL_CHECKS_STDOUT,
        stderr=RESOURCE_NOT_ACCESSIBLE_STDERR,
    )

    fix_was_called = False

    def fail_if_called(**kwargs: object) -> tuple[bool, str, float, str]:
        nonlocal fix_was_called
        fix_was_called = True
        return True, "CI_FIX_APPLIED", 0.0, "mock"

    # Provide generous monotonic values — the loop and poller both call
    # time.monotonic.  When the bug is present the poller times out,
    # consuming extra calls, so supply enough to reach the timeout path.
    monotonic_values = [float(i) for i in range(20)] + [9999.0] * 5
    with patch("pdd.ci_validation._find_open_pr_number", return_value=42), \
         patch("pdd.ci_validation._get_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._run_gh", return_value=partial_result), \
         patch("pdd.ci_validation._poll_check_runs_for_head", return_value=("no_checks", [])), \
         patch("pdd.ci_validation.time.sleep", return_value=None), \
         patch("pdd.ci_validation.time.monotonic", side_effect=monotonic_values):
        success, message, cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="owner",
            repo_name="repo",
            issue_number=1114,
            max_retries=1,
            step_template="unused",
            run_agentic_task_fn=fail_if_called,
            timeout=60.0,
            quiet=True,
        )

    assert success is True, (
        f"Expected success=True when partial data + permission error, got False with message: {message}"
    )
    assert message == "No CI checks detected"
    assert cost == 0.0
    assert not fix_was_called, "LLM fix loop should not be entered on permission error"


def test_poll_returns_no_checks_on_no_required_checks_with_partial_data(
    tmp_path: Path,
) -> None:
    """The 'no required checks' handler at ci_validation.py:275 has the same
    `not latest_checks` guard bug — it should also fire when partial check
    data is present in stdout."""
    partial_result = subprocess.CompletedProcess(
        args=[],
        returncode=1,
        stdout=PARTIAL_CHECKS_STDOUT,
        stderr="no required checks reported on the 'fix/issue-1114' branch",
    )

    with patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._run_gh", return_value=partial_result) as mock_run, \
         patch("pdd.ci_validation.time.sleep", return_value=None), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0, 9999.0]):
        status, checks = _poll_required_checks(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            cwd=tmp_path,
            expected_head_sha="sha123",
            quiet=True,
        )

    assert status == "no_checks", (
        f"Expected 'no_checks' when 'no required checks' stderr accompanies partial data, got '{status}'."
    )
    assert checks == []
    assert mock_run.call_count == 1


def test_poll_logs_unknown_stderr_before_classifying_as_failed(
    tmp_path: Path,
) -> None:
    """When ``gh pr checks`` exits 1 with non-empty ``latest_checks`` AND
    unrecognised stderr, the poller falls through to ``_classify_check_result``
    which returns ``"failed"`` purely from the exit code. That can trigger the
    LLM fix loop for non-existent failures.

    Greg's review on PR #1116 asked us to at least surface the stderr in this
    path so users can distinguish a real check failure from a gh transport
    error. Verify the yellow warning is printed before classification.
    """
    failed_checks_stdout = (
        '[{"name":"build","state":"FAILURE","bucket":"fail","link":""}]'
    )
    unknown_stderr = (
        "GraphQL: Something nobody has ever seen before "
        "(node.statusCheckRollup.nodes.0.commit.statusCheckRollup)"
    )
    failed_result = subprocess.CompletedProcess(
        args=[],
        returncode=1,
        stdout=failed_checks_stdout,
        stderr=unknown_stderr,
    )

    with patch("pdd.ci_validation._get_pr_head_sha", return_value="sha123"), \
         patch("pdd.ci_validation._run_gh", return_value=failed_result), \
         patch("pdd.ci_validation.time.sleep", return_value=None), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[0.0, 1.0, 9999.0]), \
         patch("pdd.ci_validation.console") as mock_console:
        status, checks = _poll_required_checks(
            repo_owner="owner",
            repo_name="repo",
            pr_number=42,
            cwd=tmp_path,
            expected_head_sha="sha123",
            quiet=False,
        )

    # Behaviour preserved: still classifies as failed (real check failure
    # signal must not be lost), and partial data is returned to the caller.
    assert status == "failed", f"Expected 'failed' classification, got '{status}'"
    assert len(checks) == 1
    # New observability: the unknown stderr is logged so users can see it.
    printed_args = [str(call) for call in mock_console.print.call_args_list]
    joined = " ".join(printed_args)
    assert "Something nobody has ever seen before" in joined, (
        f"Expected unknown stderr to be logged before classifying as failed, "
        f"got prints: {printed_args}"
    )
    assert "exit code 1" in joined, (
        f"Log line should make it explicit this is from exit code 1 fall-through, "
        f"got: {printed_args}"
    )


# ---------------------------------------------------------------------------
# Issue #1587: "no required checks" / timeout treated as ready while CI failing
#
# run_ci_validation_loop maps status == "no_checks" -> (True, "No CI checks
# detected") (ci_validation.py:863-864) — a FAIL-OPEN path. _poll_required_checks
# returns "no_checks" for several conditions that are NOT "this PR genuinely has
# no required checks": the GitHub App installation token cannot read the GraphQL
# statusCheckRollup ("resource not accessible by integration"), gh pr checks
# --required omits required checks that have not reported yet (cli/cli#8855), and
# poll timeouts. In all of these the PR's live head may have FAILING checks, yet
# the loop declares the PR ready. The documented contract for the gate is
# fail-closed and head-pinned (see run_github_checks_gate's docstring); the loop
# must adopt it by cross-checking the live head's real check runs via the REST
# Checks API (_poll_check_runs_for_head) before treating "no_checks" as ready.
# ---------------------------------------------------------------------------

# The live PR head visible on GitHub in the report (pdd_cloud#1997).
LIVE_HEAD_SHA = "143082622265be1b997a1b0fc5409dbc2e3ea408"
STALE_HEAD_SHA = "0d55021deadbeefdeadbeefdeadbeefdeadbeef"

# The real, failing required checks GitHub showed on the PR head.
FAILING_CHECK_RUNS = {
    "check_runs": [
        {
            "name": "pr-tests (prompt-driven-development-stg)",
            "status": "completed",
            "conclusion": "failure",
            "html_url": "https://github.com/promptdriven/pdd_cloud/runs/1",
        },
        {
            "name": "auto-heal-pr",
            "status": "completed",
            "conclusion": "failure",
            "html_url": "https://github.com/promptdriven/pdd_cloud/runs/2",
        },
    ]
}


def _failing_check_runs_result() -> subprocess.CompletedProcess:
    """REST ``commits/{sha}/check-runs`` response showing the real failures."""
    return subprocess.CompletedProcess(
        args=[],
        returncode=0,
        stdout=json.dumps(FAILING_CHECK_RUNS),
        stderr="",
    )


# --- Test 1 (Step 5 reproduction test, migrated from tests/test_issue_1587_reproduction.py) ---
def test_loop_not_ready_when_required_poll_no_checks_but_head_checks_failing(
    tmp_path: Path,
) -> None:
    """Fail-open core defect: ``--required`` poll returns ``no_checks`` (because the
    GitHub App token cannot read the GraphQL ``statusCheckRollup``), but the PR
    head's REAL check runs are failing. The loop must NOT report the PR as ready.

    On the buggy code, ``run_ci_validation_loop`` returns
    ``(True, "No CI checks detected")`` here — exactly the "PR treated as ready
    while CI failing" symptom from issue #1587.
    """
    # gh pr checks --required -> App token cannot read statusCheckRollup.
    required_permission_error = subprocess.CompletedProcess(
        args=[],
        returncode=1,
        stdout="",
        stderr="GraphQL: Resource not accessible by integration (node.statusCheckRollup)",
    )

    with patch("pdd.ci_validation._find_open_pr_number", return_value=1997), \
         patch("pdd.ci_validation.detect_ci_system", return_value="github_actions"), \
         patch("pdd.ci_validation._get_head_sha", return_value=LIVE_HEAD_SHA), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value=LIVE_HEAD_SHA), \
         patch("pdd.ci_validation._run_gh", return_value=required_permission_error), \
         patch("pdd.ci_validation._run_gh_api", return_value=_failing_check_runs_result()), \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True), \
         patch("pdd.ci_validation.time.sleep", return_value=None), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[float(i) for i in range(50)]):
        success, message, _cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="promptdriven",
            repo_name="pdd_cloud",
            issue_number=2107,
            max_retries=1,
            step_template="unused",
            run_agentic_task_fn=lambda **_: (True, "CI_FIX_APPLIED", 0.0, "mock"),
            timeout=60.0,
            quiet=True,
        )

    assert success is False, (
        "PR head has FAILING required checks (pr-tests, auto-heal-pr); the CI "
        "validation loop must fail closed, not treat the PR as ready just because "
        f"`gh pr checks --required` could not read them. Got success={success!r}, "
        f"message={message!r}."
    )
    # The message must not claim the PR is clean / has no checks.
    assert "No CI checks detected" not in message, (
        "Loop reported 'No CI checks detected' while GitHub showed failing checks "
        "on the PR head — this is the fail-open bug from issue #1587."
    )


# --- Test 2 (Step 5 reproduction test, migrated from tests/test_issue_1587_reproduction.py) ---
def test_loop_not_ready_when_required_checks_unreported_but_head_checks_failing(
    tmp_path: Path,
) -> None:
    """``gh pr checks --required`` omits required checks that have not reported a
    status yet (cli/cli#8855). gh then exits 1 with "no required checks", which
    the poller maps to ``no_checks``. But the PR head's real check runs are
    failing. The loop must not report the PR as ready.
    """
    # gh pr checks --required -> "no required checks" (checks not yet reported).
    no_required_checks_result = subprocess.CompletedProcess(
        args=[],
        returncode=1,
        stdout="",
        stderr="no required checks reported on the 'fix/issue-2107' branch",
    )

    with patch("pdd.ci_validation._find_open_pr_number", return_value=1997), \
         patch("pdd.ci_validation.detect_ci_system", return_value="github_actions"), \
         patch("pdd.ci_validation._get_head_sha", return_value=LIVE_HEAD_SHA), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value=LIVE_HEAD_SHA), \
         patch("pdd.ci_validation._run_gh", return_value=no_required_checks_result), \
         patch("pdd.ci_validation._run_gh_api", return_value=_failing_check_runs_result()), \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True), \
         patch("pdd.ci_validation.time.sleep", return_value=None), \
         patch("pdd.ci_validation.time.monotonic", side_effect=[float(i) for i in range(50)]):
        success, message, _cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="promptdriven",
            repo_name="pdd_cloud",
            issue_number=2107,
            max_retries=1,
            step_template="unused",
            run_agentic_task_fn=lambda **_: (True, "CI_FIX_APPLIED", 0.0, "mock"),
            timeout=60.0,
            quiet=True,
        )

    assert success is False, (
        "PR head has FAILING check runs; an empty `--required` result (checks not "
        "yet reported) must not be treated as 'no checks => ready'. "
        f"Got success={success!r}, message={message!r}."
    )
    assert "No CI checks detected" not in message, (
        "Loop reported 'No CI checks detected' while GitHub showed failing checks."
    )


# --- Test 3: Genuinely no CI — required poll no_checks AND live-head cross-check
# empty -> still ready (regression guard so the fail-closed fix does not
# over-correct and break repos that truly have no CI). Passes today; must keep
# passing after the fix. ---
def test_loop_ready_when_no_required_and_live_head_genuinely_has_no_checks(
    tmp_path: Path,
) -> None:
    """When the ``--required`` poll AND the live-head REST cross-check both report
    ``no_checks`` (the repo truly has no CI), the loop may treat the PR as ready
    and must NOT enter the LLM fix loop.
    """
    fix_was_called = False

    def fail_if_called(**_kwargs: object) -> tuple:
        nonlocal fix_was_called
        fix_was_called = True
        return True, "CI_FIX_APPLIED", 0.0, "mock"

    with patch("pdd.ci_validation._find_open_pr_number", return_value=1997), \
         patch("pdd.ci_validation.detect_ci_system", return_value="github_actions"), \
         patch("pdd.ci_validation._get_head_sha", return_value=LIVE_HEAD_SHA), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value=LIVE_HEAD_SHA), \
         patch("pdd.ci_validation._poll_required_checks", return_value=("no_checks", [])), \
         patch("pdd.ci_validation._poll_check_runs_for_head", return_value=("no_checks", [])), \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="promptdriven",
            repo_name="pdd_cloud",
            issue_number=2107,
            max_retries=1,
            step_template="unused",
            run_agentic_task_fn=fail_if_called,
            timeout=60.0,
            quiet=True,
        )

    assert success is True, (
        f"A repo that genuinely has no CI checks must stay ready, got "
        f"success={success!r}, message={message!r}."
    )
    assert message == "No CI checks detected"
    assert cost == 0.0
    assert not fix_was_called, (
        "LLM fix loop must not run when both the required poll and the live-head "
        "cross-check confirm there are genuinely no checks."
    )


# --- Test 4: required poll no_checks + live head PENDING (checks present but not
# completed within the poll window) -> fail closed. ---
def test_loop_inconclusive_when_required_no_checks_but_live_head_pending(
    tmp_path: Path,
) -> None:
    """When the ``--required`` poll returns ``no_checks`` and the
    live head's real check runs are still pending / not yet reported (the REST
    cross-check reports ``timeout`` because the checks never completed within the
    window), the loop must treat CI as INCONCLUSIVE and fail OPEN — the bot
    cannot trigger a manually-run / external required check, and a pending check
    is not a failing one. It must NOT post a CI-failure comment and must NOT
    drive the LLM fix loop.

    This reverses the prior fail-closed-on-pending behavior. FAILING live
    heads still fail closed (covered by the failing-head tests above), because a
    failing cross-check returns ``failed`` and never reaches the timeout branch.
    """
    pending_run = {
        "name": "pr-tests (prompt-driven-development-stg)",
        "state": "IN_PROGRESS",
        "bucket": "pending",
        "link": "https://github.com/promptdriven/pdd_cloud/runs/1",
    }
    fix_was_called = False

    def fail_if_called(**_kwargs: object) -> tuple:
        nonlocal fix_was_called
        fix_was_called = True
        return True, "CI_FIX_APPLIED", 0.0, "mock"

    with patch("pdd.ci_validation._find_open_pr_number", return_value=1997), \
         patch("pdd.ci_validation.detect_ci_system", return_value="github_actions"), \
         patch("pdd.ci_validation._get_head_sha", return_value=LIVE_HEAD_SHA), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value=LIVE_HEAD_SHA), \
         patch("pdd.ci_validation._poll_required_checks", return_value=("no_checks", [])), \
         patch("pdd.ci_validation._poll_check_runs_for_head", return_value=("timeout", [pending_run])), \
         patch("pdd.ci_validation.post_pr_comment", return_value=True), \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True) as failure_comment, \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, _cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="promptdriven",
            repo_name="pdd_cloud",
            issue_number=2107,
            max_retries=1,
            step_template="unused",
            run_agentic_task_fn=fail_if_called,
            timeout=60.0,
            quiet=True,
        )

    assert success is True, (
        "A pending (non-failing) live head the bot cannot advance must be "
        f"inconclusive (fail-open), not a hard failure. Got success={success!r}, "
        f"message={message!r}."
    )
    assert "inconclusive" in message.lower()
    assert "No CI checks detected" not in message
    assert not fix_was_called, (
        "An inconclusive pending head must not drive the LLM CI-fix loop."
    )
    failure_comment.assert_not_called()


# --- Test 5: caller-boundary — the loop must route the no_checks case through
# _poll_check_runs_for_head on the live PR head and act on that callee's verdict. ---
def test_loop_routes_no_checks_through_live_head_cross_check(
    tmp_path: Path,
) -> None:
    """When ``_poll_required_checks`` returns ``no_checks``, the loop must call
    ``_poll_check_runs_for_head`` for the live PR head and let that callee's verdict
    drive the result. This asserts BOTH sides of the caller/callee boundary:

    1. the caller actually invokes ``_poll_check_runs_for_head`` with the live PR
       head SHA (not the stale expected SHA), and
    2. because the callee reports ``failed``, the loop returns ``success is False``.

    On the buggy code ``_poll_check_runs_for_head`` is never called from the loop,
    so the ``assert_called`` below fails — proving the loop ignores the live head.
    """
    failing_run = {
        "name": "pr-tests (prompt-driven-development-stg)",
        "state": "FAILURE",
        "bucket": "fail",
        "link": "https://github.com/promptdriven/pdd_cloud/runs/1",
    }

    with patch("pdd.ci_validation._find_open_pr_number", return_value=1997), \
         patch("pdd.ci_validation.detect_ci_system", return_value="github_actions"), \
         patch("pdd.ci_validation._get_head_sha", return_value=STALE_HEAD_SHA), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value=LIVE_HEAD_SHA), \
         patch("pdd.ci_validation._poll_required_checks", return_value=("no_checks", [])), \
         patch(
             "pdd.ci_validation._poll_check_runs_for_head",
             return_value=("failed", [failing_run]),
         ) as mock_cross_check, \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True), \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, _cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="promptdriven",
            repo_name="pdd_cloud",
            issue_number=2107,
            max_retries=1,
            step_template="unused",
            run_agentic_task_fn=lambda **_: (True, "CI_FIX_APPLIED", 0.0, "mock"),
            timeout=60.0,
            quiet=True,
        )

    mock_cross_check.assert_called()
    assert mock_cross_check.call_args.kwargs.get("head_sha") == LIVE_HEAD_SHA, (
        "The loop must cross-check the LIVE PR head SHA, got "
        f"{mock_cross_check.call_args.kwargs.get('head_sha')!r}."
    )
    assert success is False, (
        "The live-head cross-check reported failing checks; the loop must act on "
        f"that verdict and fail closed. Got success={success!r}, message={message!r}."
    )


def test_loop_cross_checks_live_head_when_local_head_is_stale(
    tmp_path: Path,
) -> None:
    """A stale local worktree head must not be used for the no_checks cross-check."""
    failing_run = {
        "name": "pr-tests (prompt-driven-development-stg)",
        "state": "FAILURE",
        "bucket": "fail",
        "link": "https://github.com/promptdriven/pdd_cloud/runs/1",
    }

    with patch("pdd.ci_validation._find_open_pr_number", return_value=1997), \
         patch("pdd.ci_validation.detect_ci_system", return_value="github_actions"), \
         patch("pdd.ci_validation._get_head_sha", return_value="stale-local-head"), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value=LIVE_HEAD_SHA), \
         patch("pdd.ci_validation._poll_required_checks", return_value=("no_checks", [])), \
         patch(
             "pdd.ci_validation._poll_check_runs_for_head",
             return_value=("failed", [failing_run]),
         ) as mock_cross_check, \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True), \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, _cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="promptdriven",
            repo_name="pdd_cloud",
            issue_number=2107,
            max_retries=1,
            step_template="unused",
            run_agentic_task_fn=lambda **_: (True, "CI_FIX_APPLIED", 0.0, "mock"),
            timeout=60.0,
            quiet=True,
        )

    assert mock_cross_check.call_args.kwargs.get("head_sha") == LIVE_HEAD_SHA
    assert success is False
    assert "No CI checks detected" not in message


def test_loop_cross_check_respects_explicit_expected_head_override(
    tmp_path: Path,
) -> None:
    """The final-gate caller can still pin the exact post-checkup PR head."""
    with patch("pdd.ci_validation._find_open_pr_number", return_value=1997), \
         patch("pdd.ci_validation.detect_ci_system", return_value="github_actions"), \
         patch("pdd.ci_validation._get_head_sha", return_value="stale-local-head"), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value=LIVE_HEAD_SHA) as mock_live_head, \
         patch("pdd.ci_validation._poll_required_checks", return_value=("no_checks", [])), \
         patch(
             "pdd.ci_validation._poll_check_runs_for_head",
             return_value=("no_checks", []),
         ) as mock_cross_check, \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, _cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="promptdriven",
            repo_name="pdd_cloud",
            issue_number=2107,
            max_retries=1,
            step_template="unused",
            run_agentic_task_fn=lambda **_: (True, "CI_FIX_APPLIED", 0.0, "mock"),
            timeout=60.0,
            quiet=True,
            expected_head_sha_override="verified-post-checkup-head",
        )

    mock_live_head.assert_not_called()
    assert mock_cross_check.call_args.kwargs.get("head_sha") == "verified-post-checkup-head"
    assert success is True
    assert message == "No CI checks detected"


def test_loop_inconclusive_when_live_head_cross_check_needs_manual_action(
    tmp_path: Path,
) -> None:
    """Manual-action live-head check runs must not drive the CI-fix loop."""
    action_required_run = {
        "name": "auto-heal-pr (prompt-driven-development-stg)",
        "state": "ACTION_REQUIRED",
        "bucket": "action_required",
        "link": "https://console.cloud.google.com/cloud-build/triggers/example",
    }
    fix_was_called = False

    def fail_if_called(**_kwargs: object) -> tuple:
        nonlocal fix_was_called
        fix_was_called = True
        return True, "CI_FIX_APPLIED", 0.0, "mock"

    with patch("pdd.ci_validation._find_open_pr_number", return_value=1997), \
         patch("pdd.ci_validation.detect_ci_system", return_value="github_actions"), \
         patch("pdd.ci_validation._get_head_sha", return_value=STALE_HEAD_SHA), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value=LIVE_HEAD_SHA), \
         patch("pdd.ci_validation._poll_required_checks", return_value=("no_checks", [])), \
         patch(
             "pdd.ci_validation._poll_check_runs_for_head",
             return_value=("action_required", [action_required_run]),
         ), \
         patch("pdd.ci_validation.post_pr_comment", return_value=True) as info_comment, \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True) as failure_comment, \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="promptdriven",
            repo_name="pdd_cloud",
            issue_number=1740,
            max_retries=1,
            step_template="unused",
            run_agentic_task_fn=fail_if_called,
            timeout=60.0,
            quiet=True,
        )

    assert success is True
    assert cost == 0.0
    assert "manual action" in message.lower()
    assert "inconclusive" in message.lower()
    assert not fix_was_called
    info_comment.assert_called_once()
    failure_comment.assert_not_called()


def test_loop_not_ready_when_live_head_cross_check_is_unreadable(
    tmp_path: Path,
) -> None:
    """Unreadable live-head check-runs must fail closed, not look like no CI."""
    with patch("pdd.ci_validation._find_open_pr_number", return_value=1997), \
         patch("pdd.ci_validation.detect_ci_system", return_value="github_actions"), \
         patch("pdd.ci_validation._get_head_sha", return_value=STALE_HEAD_SHA), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value=LIVE_HEAD_SHA), \
         patch("pdd.ci_validation._poll_required_checks", return_value=("no_checks", [])), \
         patch("pdd.ci_validation._poll_check_runs_for_head", return_value=("unreadable", [])), \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True), \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, _cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="promptdriven",
            repo_name="pdd_cloud",
            issue_number=2107,
            max_retries=1,
            step_template="unused",
            run_agentic_task_fn=lambda **_: (True, "CI_FIX_APPLIED", 0.0, "mock"),
            timeout=60.0,
            quiet=True,
        )

    assert success is False
    assert "unreadable" in message
    assert "No CI checks detected" not in message


# ---------------------------------------------------------------------------
# A required CI check that never completes within the poll window
# (manually-triggered / external CI the bot structurally cannot run, e.g.
# pdd_cloud's /gcbrun-gated build, or simply a slow check) is INCONCLUSIVE, not
# a failure. The fix is already committed to the PR; a pending required check
# must not retroactively hard-fail an otherwise-correct fix. A genuine check
# FAILURE returns "failed" and never reaches the timeout branch, so failing
# open here cannot mask a real CI failure.
# ---------------------------------------------------------------------------
def test_loop_inconclusive_when_required_checks_time_out(tmp_path: Path) -> None:
    """A poll timeout on still-pending required checks must fail OPEN as
    inconclusive (success=True with a best-effort note), not hard-fail the run,
    and must not drive the LLM CI-fix loop or post a CI-failure comment."""
    pending_run = {
        "name": "build (manual /gcbrun)",
        "state": "PENDING",
        "bucket": "pending",
        "link": "https://github.com/promptdriven/pdd_cloud/runs/1",
    }
    fix_was_called = False

    def fail_if_called(**_kwargs: object) -> tuple:
        nonlocal fix_was_called
        fix_was_called = True
        return True, "CI_FIX_APPLIED", 0.0, "mock"

    with patch("pdd.ci_validation._find_open_pr_number", return_value=1997), \
         patch("pdd.ci_validation.detect_ci_system", return_value="github_actions"), \
         patch("pdd.ci_validation._get_head_sha", return_value=LIVE_HEAD_SHA), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value=LIVE_HEAD_SHA), \
         patch(
             "pdd.ci_validation._poll_required_checks",
             return_value=("timeout", [pending_run]),
         ), \
         patch("pdd.ci_validation.post_pr_comment", return_value=True), \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True) as failure_comment, \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, _cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="promptdriven",
            repo_name="pdd_cloud",
            issue_number=2107,
            max_retries=1,
            step_template="unused",
            run_agentic_task_fn=fail_if_called,
            timeout=60.0,
            quiet=True,
        )

    assert success is True, (
        "A pending/timed-out required check the bot cannot trigger must be "
        f"treated as inconclusive (fail-open), not a hard failure. Got "
        f"success={success!r}, message={message!r}."
    )
    assert "inconclusive" in message.lower(), (
        f"The message must signal the result is inconclusive, got {message!r}."
    )
    assert not fix_was_called, (
        "An inconclusive timeout must not drive the LLM CI-fix loop."
    )
    assert "Timed out waiting for required CI checks to complete" not in message, (
        "The inconclusive-timeout path must not reuse the old hard-fail message."
    )
    failure_comment.assert_not_called()


def test_loop_inconclusive_when_required_check_needs_manual_action(
    tmp_path: Path,
) -> None:
    """ACTION_REQUIRED required checks need an external/manual trigger, not LLM repair."""
    action_required = {
        "name": "auto-heal-pr (prompt-driven-development-stg)",
        "state": "ACTION_REQUIRED",
        "bucket": "fail",
        "link": "https://console.cloud.google.com/cloud-build/triggers/example",
    }
    fix_was_called = False

    def fail_if_called(**_kwargs: object) -> tuple:
        nonlocal fix_was_called
        fix_was_called = True
        return True, "CI_FIX_APPLIED", 0.0, "mock"

    with patch("pdd.ci_validation._find_open_pr_number", return_value=2459), \
         patch("pdd.ci_validation.detect_ci_system", return_value="github_actions"), \
         patch("pdd.ci_validation._get_head_sha", return_value=LIVE_HEAD_SHA), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value=LIVE_HEAD_SHA), \
         patch(
             "pdd.ci_validation._poll_required_checks",
             return_value=("action_required", [action_required]),
         ), \
         patch("pdd.ci_validation.post_pr_comment", return_value=True) as info_comment, \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True) as failure_comment, \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="promptdriven",
            repo_name="pdd_cloud",
            issue_number=1740,
            max_retries=2,
            step_template="unused",
            run_agentic_task_fn=fail_if_called,
            timeout=60.0,
            quiet=True,
        )

    assert success is True
    assert cost == 0.0
    assert "manual action" in message.lower()
    assert "inconclusive" in message.lower()
    assert not fix_was_called, "ACTION_REQUIRED must not drive the LLM CI-fix loop."
    info_comment.assert_called_once()
    failure_comment.assert_not_called()


def test_loop_fails_closed_when_timeout_without_any_checks_read(tmp_path: Path) -> None:
    """Guard (the other half of fail-open): a poll timeout where NO
    required checks were ever read — the PR head never matched the expected SHA,
    or the rollup was unreadable for the whole window, so ``_poll_required_checks``
    returns ``("timeout", [])`` — must FAIL CLOSED, not fail open. With an empty
    check set we cannot prove the checks are merely pending rather than failing,
    so we must not green-light a head whose real status was never observed."""
    with patch("pdd.ci_validation._find_open_pr_number", return_value=1997), \
         patch("pdd.ci_validation.detect_ci_system", return_value="github_actions"), \
         patch("pdd.ci_validation._get_head_sha", return_value=LIVE_HEAD_SHA), \
         patch("pdd.ci_validation._get_pr_head_sha", return_value=STALE_HEAD_SHA), \
         patch("pdd.ci_validation._poll_required_checks", return_value=("timeout", [])), \
         patch("pdd.ci_validation.post_pr_comment", return_value=True) as info_comment, \
         patch("pdd.ci_validation.post_ci_failure_comment", return_value=True) as failure_comment, \
         patch("pdd.ci_validation.time.sleep", return_value=None):
        success, message, _cost = run_ci_validation_loop(
            cwd=tmp_path,
            repo_owner="promptdriven",
            repo_name="pdd_cloud",
            issue_number=2107,
            max_retries=1,
            step_template="unused",
            run_agentic_task_fn=lambda **_: (True, "CI_FIX_APPLIED", 0.0, "mock"),
            timeout=60.0,
            quiet=True,
        )

    assert success is False, (
        "A timeout where no required checks were ever read must fail closed "
        f"(real status unknown), not fail open. Got success={success!r}, "
        f"message={message!r}."
    )
    assert "inconclusive" not in message.lower(), (
        "The unread-checks timeout is a real fail-closed, not an inconclusive "
        f"fail-open. Got message={message!r}."
    )
    # The inconclusive best-effort note is for the pending-checks case only;
    # the unread case posts a CI-failure comment instead.
    info_comment.assert_not_called()
    failure_comment.assert_called_once()
