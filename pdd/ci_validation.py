from __future__ import annotations

import io
import json
import subprocess
import time
import zipfile
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

from rich.console import Console

from .agentic_common import DEFAULT_MAX_RETRIES, post_pr_comment, substitute_template_variables
from .preprocess import preprocess

console = Console()

INITIAL_POLL_DELAY_SECONDS = 30
POLL_INTERVAL_SECONDS = 30
MAX_POLL_SECONDS = 600
MAX_LOG_CHARS = 20000

PASS_BUCKETS = {"pass", "skipping"}
FAIL_BUCKETS = {"fail", "cancel"}
PENDING_BUCKETS = {"pending"}
SKIP_BUCKETS = {"skip", "skipped", "skipping"}
FINAL_GATE_PASS_BUCKETS = {"pass"}
ACTION_REQUIRED_STATES = {"action_required"}
ACTION_REQUIRED_BUCKETS = {"action_required"}
FAILURE_STATES = {"failure", "failed", "cancelled", "canceled", "timed_out", "startup_failure"}
KNOWN_CHECK_BUCKETS = PASS_BUCKETS | FAIL_BUCKETS | PENDING_BUCKETS | SKIP_BUCKETS | ACTION_REQUIRED_BUCKETS
ACTIONABLE_FAILURE_LOG_MARKERS = (
    "assertionerror",
    "build failed",
    "can't resolve",
    "cannot find module",
    "cannot resolve",
    "compilation failed",
    "could not resolve",
    "eslint",
    "failed to compile",
    "flake8",
    "go test",
    "importerror",
    "javac",
    "module not found",
    "modulenotfounderror",
    "mvn test",
    "mypy",
    "npm err!",
    "pnpm test",
    "pytest",
    "ruff",
    "syntaxerror",
    "test failed",
    "tests failed",
    "traceback (most recent call last)",
    "tsc ",
    "unittest",
    "yarn test",
)
GENERIC_CI_CHECK_NAME_MARKERS = (
    "actions",
    "build",
    "check",
    "ci",
    "continuous integration",
    "pipeline",
    "workflow",
)
EXTERNAL_CI_CHECK_NAME_MARKERS = (
    "auth",
    "auto-heal",
    "cloud build",
    "deploy",
    "firebase",
    "gcbrun",
    "google",
    "preview",
)
ACTIONABLE_CHECK_NAME_MARKERS = (
    "eslint",
    "flake8",
    "lint",
    "mypy",
    "pytest",
    "ruff",
    "test",
    "tsc",
    "typecheck",
    "unit",
)

# Substring gh CLI prints to stderr when no required checks are configured.
# Centralised so tests can reference the same constant instead of duplicating
# a magic string.
GH_NO_REQUIRED_CHECKS_PHRASE = "no required checks"
GH_NO_CHECKS_PHRASES = (GH_NO_REQUIRED_CHECKS_PHRASE, "no checks")


def detect_ci_system(cwd: Path) -> str:
    """Infer the repo's CI system from common config locations."""
    if (cwd / ".github" / "workflows").is_dir():
        return "github_actions"
    if any((cwd / name).exists() for name in ("cloudbuild.yaml", "cloudbuild-ci.yaml", "cloudbuild.yml")):
        return "cloud_build"
    if (cwd / ".circleci" / "config.yml").exists():
        return "circleci"
    if (cwd / ".gitlab-ci.yml").exists():
        return "gitlab_ci"
    if (cwd / "Jenkinsfile").exists():
        return "jenkins"
    return "unknown"


def _run_command(cmd: List[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    """Run a subprocess and capture text output without raising."""
    try:
        return subprocess.run(
            cmd,
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError:
        return subprocess.CompletedProcess(cmd, returncode=127, stdout="", stderr=f"{cmd[0]}: not found")


def _run_command_bytes(cmd: List[str], cwd: Path) -> subprocess.CompletedProcess[bytes]:
    """Run a subprocess and capture byte output without raising."""
    try:
        return subprocess.run(
            cmd,
            cwd=cwd,
            capture_output=True,
            check=False,
        )
    except OSError:
        return subprocess.CompletedProcess(cmd, returncode=127, stdout=b"", stderr=b"")


def _run_gh(repo_owner: str, repo_name: str, cwd: Path, args: List[str]) -> subprocess.CompletedProcess[str]:
    """Run a gh command scoped to the current repository."""
    return _run_command(["gh", *args, "--repo", f"{repo_owner}/{repo_name}"], cwd)


def _run_gh_api(cwd: Path, args: List[str]) -> subprocess.CompletedProcess[str]:
    """Run a gh api command.

    ``gh api`` endpoints already include the repository path and do not support
    the global ``--repo`` flag.
    """
    return _run_command(["gh", "api", *args], cwd)


def _run_gh_bytes(
    repo_owner: str,
    repo_name: str,
    cwd: Path,
    args: List[str],
) -> subprocess.CompletedProcess[bytes]:
    """Run a gh command that may return binary output."""
    return _run_command_bytes(["gh", *args, "--repo", f"{repo_owner}/{repo_name}"], cwd)


def _get_current_branch(cwd: Path) -> str:
    """Return the current git branch name."""
    result = _run_command(["git", "rev-parse", "--abbrev-ref", "HEAD"], cwd)
    if result.returncode != 0:
        return ""
    return result.stdout.strip()


def _get_head_sha(cwd: Path) -> str:
    """Return the current HEAD commit SHA."""
    result = _run_command(["git", "rev-parse", "HEAD"], cwd)
    if result.returncode != 0:
        return ""
    return result.stdout.strip()


def _find_open_pr_number(repo_owner: str, repo_name: str, cwd: Path) -> Optional[int]:
    """Find the open PR associated with the current branch."""
    branch = _get_current_branch(cwd)
    if not branch:
        return None

    result = _run_gh(
        repo_owner,
        repo_name,
        cwd,
        ["pr", "list", "--state", "open", "--head", branch, "--json", "number"],
    )
    if result.returncode == 0:
        try:
            prs = json.loads(result.stdout or "[]")
        except json.JSONDecodeError:
            prs = []
        if prs:
            try:
                return int(prs[0]["number"])
            except (KeyError, TypeError, ValueError):
                return None

    fallback = _run_gh(
        repo_owner,
        repo_name,
        cwd,
        ["pr", "view", branch, "--json", "number"],
    )
    if fallback.returncode != 0:
        return None

    try:
        payload = json.loads(fallback.stdout or "{}")
        return int(payload["number"])
    except (KeyError, TypeError, ValueError, json.JSONDecodeError):
        return None


def _get_pr_head_sha(repo_owner: str, repo_name: str, pr_number: int, cwd: Path) -> str:
    """Return the PR head SHA reported by GitHub."""
    result = _run_gh(
        repo_owner,
        repo_name,
        cwd,
        ["pr", "view", str(pr_number), "--json", "headRefOid"],
    )
    if result.returncode != 0 or not result.stdout.strip():
        return ""

    try:
        payload = json.loads(result.stdout or "{}")
        return str(payload.get("headRefOid", "")).strip()
    except json.JSONDecodeError:
        return ""


def _normalize_checks(raw_checks: Any) -> List[Dict[str, str]]:
    """Normalize gh check payloads into a stable structure."""
    if not isinstance(raw_checks, list):
        return []

    checks: List[Dict[str, str]] = []
    for item in raw_checks:
        if not isinstance(item, dict):
            continue
        checks.append(
            {
                "name": str(item.get("name", "")).strip(),
                "state": str(item.get("state", "")).strip(),
                "bucket": str(item.get("bucket", "")).strip().lower(),
                "link": str(item.get("link", "")).strip(),
            }
        )
    return checks


def _check_run_bucket(status: str, conclusion: str) -> str:
    """Map REST check-run status/conclusion fields to gh-style buckets."""
    normalized_status = status.strip().lower()
    normalized_conclusion = conclusion.strip().lower()

    if normalized_status != "completed":
        return "pending"
    if normalized_conclusion == "success":
        return "pass"
    if normalized_conclusion in {"skipped", "neutral"}:
        return "skipped"
    if normalized_conclusion in ACTION_REQUIRED_STATES:
        return "action_required"
    if normalized_conclusion in {
        "failure",
        "cancelled",
        "timed_out",
        "startup_failure",
    }:
        return "fail"
    return ""


def _normalize_check_runs(raw_payload: Any) -> List[Dict[str, str]]:
    """Normalize REST check-runs payloads into the shared check structure."""
    if not isinstance(raw_payload, dict):
        return []
    raw_runs = raw_payload.get("check_runs")
    if not isinstance(raw_runs, list):
        return []

    checks: List[Dict[str, str]] = []
    for item in raw_runs:
        if not isinstance(item, dict):
            continue
        status = str(item.get("status", "")).strip()
        conclusion = str(item.get("conclusion", "") or "").strip()
        link = str(item.get("html_url") or item.get("details_url") or "").strip()
        checks.append(
            {
                "name": str(item.get("name", "")).strip(),
                "state": (conclusion or status).upper(),
                "bucket": _check_run_bucket(status, conclusion),
                "link": link,
            }
        )
    return checks


def _render_check_summary(checks: List[Dict[str, str]]) -> str:
    """Render required checks into a compact markdown list."""
    if not checks:
        return "No required CI checks were reported."

    lines: List[str] = []
    for check in checks:
        bucket = check.get("bucket") or "unknown"
        state = check.get("state") or "unknown"
        link = check.get("link")
        line = f"- {check.get('name') or 'unnamed check'}: bucket={bucket}, state={state}"
        if link:
            line += f", link={link}"
        lines.append(line)
    return "\n".join(lines)


def _classify_external_ci_failure(checks: List[Dict[str, str]], failure_logs: str) -> Optional[str]:
    """Return a reason when a CI failure is clearly external/manual setup."""
    haystack = f"{_render_check_summary(checks)}\n{failure_logs or ''}".lower()
    if not haystack.strip():
        return None
    if any(marker in (failure_logs or "").lower() for marker in ACTIONABLE_FAILURE_LOG_MARKERS):
        return None
    if not _failed_check_set_is_pure_external_setup(checks):
        return None

    google_auth_action = "google-github-actions/auth" in haystack
    missing_google_auth_inputs = (
        "credentials_json" in haystack
        and "workload_identity_provider" in haystack
        and (
            "must specify exactly one" in haystack
            or "not supplied" in haystack
            or "not provided" in haystack
            or "not set" in haystack
            or "secret" in haystack
        )
    )
    if google_auth_action and missing_google_auth_inputs:
        return (
            "GitHub Actions Google authentication is missing or empty "
            "(`credentials_json` / `workload_identity_provider`)."
        )

    firebase_secret_failure = (
        ("firebase_service_account" in haystack or "firebase service account" in haystack)
        and (
            "secret" in haystack
            or "secrets." in haystack
            or "service account" in haystack
        )
        and any(
            marker in haystack
            for marker in (
                "not supplied",
                "not provided",
                "not configured",
                "not set",
                "empty",
                "unavailable",
                "not found",
                "does not exist",
            )
        )
    )
    if firebase_secret_failure:
        return "Firebase deployment credentials are missing from the CI environment."

    secrets_unavailable_for_event = (
        "secrets are not passed" in haystack
        or "secret is not available" in haystack
        or "secrets are unavailable" in haystack
    )
    if secrets_unavailable_for_event and any(
        marker in haystack
        for marker in ("github action", "github actions", "workflow", "fork", "pull request")
    ):
        return "GitHub Actions secrets are unavailable for this workflow event."

    integration_permission_failure = (
        "resource not accessible by integration" in haystack
        and any(marker in haystack for marker in ("github", "check", "workflow", "pull request"))
    )
    if integration_permission_failure:
        return "The GitHub integration token lacks permission to access this CI resource."

    return None


def _failed_check_set_is_pure_external_setup(checks: List[Dict[str, str]]) -> bool:
    """True when failed check names do not indicate code/test failures."""
    failed_checks = [
        check
        for check in checks
        if check.get("bucket", "").lower() in FAIL_BUCKETS
        or check.get("state", "").lower() in FAILURE_STATES
    ]
    if not failed_checks:
        return False

    for check in failed_checks:
        name = check.get("name", "").strip().lower()
        if any(marker in name for marker in ACTIONABLE_CHECK_NAME_MARKERS):
            return False
        if not any(
            marker in name
            for marker in EXTERNAL_CI_CHECK_NAME_MARKERS + GENERIC_CI_CHECK_NAME_MARKERS
        ):
            return False
    return True


def _load_ci_config(cwd: Path) -> Dict[str, Any]:
    """Load the optional root-level .pddrc CI config."""
    try:
        from .construct_paths import _find_pddrc_file, _load_pddrc_config

        pddrc_path = _find_pddrc_file(cwd)
        if pddrc_path is None:
            return {}
        config = _load_pddrc_config(pddrc_path)
    except Exception:  # noqa: BLE001 — CI config is optional best-effort input
        return {}

    ci_config = config.get("ci", {})
    if not isinstance(ci_config, dict):
        return {}
    return ci_config


def _external_ci_setup_fail_open_enabled(cwd: Path) -> bool:
    """Return whether failed external setup/auth checks may be inconclusive."""
    return _load_ci_config(cwd).get("external_setup_fail_open") is True


def _configured_manual_trigger_comments(cwd: Path, checks: List[Dict[str, str]]) -> List[str]:
    """Return configured manual CI trigger comments for the observed checks."""
    ci_config = _load_ci_config(cwd)
    comments: List[str] = []
    action_required_checks = [
        check
        for check in checks
        if check.get("state", "").lower() in ACTION_REQUIRED_STATES
        or check.get("bucket", "").lower() in ACTION_REQUIRED_BUCKETS
    ]
    unmatched_action_required_check = False
    manual_triggers = ci_config.get("manual_triggers")
    if isinstance(manual_triggers, dict):
        for check in action_required_checks:
            check_name = check.get("name", "").strip().lower()
            matched_check = False
            if check_name:
                for pattern, comment in manual_triggers.items():
                    pattern_text = str(pattern).strip().lower()
                    comment_text = str(comment).strip()
                    if pattern_text and pattern_text in check_name and comment_text:
                        if comment_text not in comments:
                            comments.append(comment_text)
                        matched_check = True
            if not matched_check:
                unmatched_action_required_check = True
    elif action_required_checks:
        unmatched_action_required_check = True

    comment = ci_config.get("manual_trigger_comment")
    if unmatched_action_required_check and isinstance(comment, str) and comment.strip():
        fallback_comment = comment.strip()
        if fallback_comment not in comments:
            comments.append(fallback_comment)
    return comments


def _configured_manual_trigger_comment(cwd: Path, checks: List[Dict[str, str]]) -> Optional[str]:
    """Return the first configured manual CI trigger comment for compatibility."""
    comments = _configured_manual_trigger_comments(cwd, checks)
    return comments[0] if comments else None


def _next_configured_manual_trigger_comment(
    cwd: Path,
    checks: List[Dict[str, str]],
    posted_comments: set[str],
) -> Optional[str]:
    """Return the next configured manual trigger that has not been posted."""
    for comment in _configured_manual_trigger_comments(cwd, checks):
        if comment not in posted_comments:
            return comment
    return None


def _render_stale_head_summary(
    *,
    pr_number: int,
    expected_head_sha: str,
    live_head_sha: str,
    checks: List[Dict[str, str]],
) -> str:
    """Render a clear diagnostic when the expected PR head never became live."""
    expected = expected_head_sha or "<unknown>"
    live = live_head_sha or "<unknown>"
    summary = _render_check_summary(checks)
    return (
        f"PR #{pr_number} head did not match the expected CI validation head.\n"
        f"- expected head: `{expected}`\n"
        f"- live PR head: `{live}`\n"
        f"- last known checks:\n{summary}"
    )


def _classify_check_result(returncode: int, checks: List[Dict[str, str]]) -> str:
    """Classify `gh pr checks` output using both exit code and bucket values."""
    buckets = [check.get("bucket", "").lower() for check in checks if check.get("bucket")]
    unknown_checks = [
        check
        for check in checks
        if check.get("bucket", "").lower() not in KNOWN_CHECK_BUCKETS
        and check.get("state", "").lower() not in ACTION_REQUIRED_STATES
    ]
    pending_checks = [
        check
        for check in checks
        if check.get("bucket", "").lower() in PENDING_BUCKETS
    ]
    action_required_checks = [
        check
        for check in checks
        if check.get("state", "").lower() in ACTION_REQUIRED_STATES
        or check.get("bucket", "").lower() in ACTION_REQUIRED_BUCKETS
    ]
    real_failures = [
        check
        for check in checks
        if (
            check.get("bucket", "").lower() in FAIL_BUCKETS
            and check.get("state", "").lower() not in ACTION_REQUIRED_STATES
        )
        or check.get("state", "").lower() in FAILURE_STATES
    ]
    non_success_checks = [
        check
        for check in checks
        if check.get("bucket", "").lower() not in PASS_BUCKETS
        and check.get("bucket", "").lower() not in SKIP_BUCKETS
    ]

    if real_failures:
        return "failed"
    if unknown_checks:
        return "failed"
    if pending_checks:
        return "pending"
    if action_required_checks and len(action_required_checks) == len(non_success_checks):
        return "action_required"
    if checks and all(bucket in PASS_BUCKETS for bucket in buckets):
        return "passed"

    if returncode == 0:
        return "passed"
    if returncode == 1:
        return "failed"
    return "pending"


def _poll_required_checks(
    repo_owner: str,
    repo_name: str,
    pr_number: int,
    cwd: Path,
    *,
    expected_head_sha: str,
    quiet: bool,
    required_only: bool = True,
) -> Tuple[str, List[Dict[str, str]]]:
    """Poll PR checks until they pass, fail, or time out."""
    saw_checks = False
    saw_ambiguous_error = False
    matched_expected_head = not bool(expected_head_sha)
    last_remote_head_sha = ""
    latest_checks: List[Dict[str, str]] = []
    start = time.monotonic()

    while time.monotonic() - start < MAX_POLL_SECONDS:
        remote_head_sha = _get_pr_head_sha(repo_owner, repo_name, pr_number, cwd)
        if remote_head_sha:
            last_remote_head_sha = remote_head_sha
        if expected_head_sha and remote_head_sha:
            matched_expected_head = remote_head_sha == expected_head_sha
            if not matched_expected_head:
                if not quiet:
                    console.print(
                        f"[dim]PR #{pr_number} live head is {remote_head_sha[:7]}, "
                        f"not expected head {expected_head_sha[:7]}; checking "
                        "live-head status before waiting...[/dim]"
                    )

        check_args = ["pr", "checks", str(pr_number)]
        if required_only:
            check_args.append("--required")
        check_args.extend(["--json", "name,state,bucket,link"])
        result = _run_gh(repo_owner, repo_name, cwd, check_args)

        latest_checks = []
        if result.stdout.strip():
            try:
                latest_checks = _normalize_checks(json.loads(result.stdout or "[]"))
            except json.JSONDecodeError:
                if not quiet:
                    console.print("[yellow]CI polling warning: failed to parse `gh pr checks` JSON output.[/yellow]")

        saw_checks = saw_checks or bool(latest_checks)

        # gh pr checks --required exits 1 — check stderr for known errors
        # before inspecting latest_checks, because partial check data can
        # accompany permission/config errors (issue #1114).
        if result.returncode == 1:
            stderr_lower = (result.stderr or "").lower()
            if any(phrase in stderr_lower for phrase in GH_NO_CHECKS_PHRASES):
                return "no_checks", []
            # GitHub App installation token may lack checks:read on fork repos.
            # "resource not accessible by integration" means we can't read check
            # status — treat as no required checks rather than polling until timeout.
            if "resource not accessible by integration" in stderr_lower:
                if not quiet:
                    console.print(
                        "[yellow]CI polling: cannot read check status "
                        "(GitHub App may lack checks:read permission on this repo). "
                        "Skipping CI validation.[/yellow]"
                    )
                return "no_checks", []
            if not latest_checks:
                # Ambiguous error (e.g. HTTP 401); keep polling.
                saw_ambiguous_error = True
                if not quiet:
                    stderr_msg = result.stderr.strip()
                    if stderr_msg:
                        console.print(f"[yellow]CI polling warning: {stderr_msg}[/yellow]")
                time.sleep(POLL_INTERVAL_SECONDS)
                continue
            # returncode=1 + non-empty latest_checks + unrecognised stderr.
            # This falls through to _classify_check_result, which will return
            # "failed" purely from the exit code — potentially triggering the
            # LLM fix loop for non-existent failures. Surface the stderr so
            # users can tell whether it was a real check failure or a gh
            # transport error masquerading as one.
            if not quiet:
                stderr_msg = result.stderr.strip()
                if stderr_msg:
                    console.print(
                        f"[yellow]CI polling warning (classifying as failed "
                        f"from exit code 1): {stderr_msg}[/yellow]"
                    )

        status = _classify_check_result(result.returncode, latest_checks)

        if status == "failed":
            return status, latest_checks
        if status == "action_required" and matched_expected_head:
            return status, latest_checks
        if status == "passed" and matched_expected_head:
            return status, latest_checks

        if result.returncode not in {0, 1, 8} and not quiet:
            stderr = result.stderr.strip()
            if stderr:
                console.print(f"[yellow]CI polling warning: {stderr}[/yellow]")

        time.sleep(POLL_INTERVAL_SECONDS)

    if not saw_checks and matched_expected_head and not saw_ambiguous_error:
        return "no_checks", []
    if expected_head_sha and not matched_expected_head:
        stale_summary = _render_stale_head_summary(
            pr_number=pr_number,
            expected_head_sha=expected_head_sha,
            live_head_sha=last_remote_head_sha,
            checks=latest_checks,
        )
        return "stale_head", [
            {
                "name": "PR head mismatch",
                "state": stale_summary,
                "bucket": "fail",
                "link": "",
            }
        ]
    return "timeout", latest_checks


def _poll_check_runs_for_head(
    repo_owner: str,
    repo_name: str,
    cwd: Path,
    *,
    head_sha: str,
    quiet: bool,
) -> Tuple[str, List[Dict[str, str]]]:
    """Poll REST check runs for the exact PR head SHA.

    Final gate uses this instead of ``gh pr checks`` because the latter reads
    GitHub's GraphQL ``statusCheckRollup`` field. Installation tokens can have
    ``checks:read`` while lacking commit-status permissions, and the GraphQL
    rollup fails even when real check runs are readable through the REST Checks
    API.
    """
    saw_checks = False
    saw_api_error = False
    latest_checks: List[Dict[str, str]] = []
    start = time.monotonic()

    while time.monotonic() - start < MAX_POLL_SECONDS:
        result = _run_gh_api(
            cwd,
            [f"repos/{repo_owner}/{repo_name}/commits/{head_sha}/check-runs?per_page=100"],
        )

        latest_checks = []
        if result.stdout.strip():
            try:
                latest_checks = _normalize_check_runs(json.loads(result.stdout or "{}"))
            except json.JSONDecodeError:
                if not quiet:
                    console.print("[yellow]CI polling warning: failed to parse check-runs JSON output.[/yellow]")

        saw_checks = saw_checks or bool(latest_checks)
        if latest_checks:
            status = _classify_check_result(result.returncode, latest_checks)
            if status in {"passed", "failed", "action_required"}:
                return status, latest_checks

        if result.returncode != 0:
            saw_api_error = True
            stderr_lower = (result.stderr or "").lower()
            if "resource not accessible by integration" in stderr_lower:
                if not quiet:
                    console.print(
                        "[yellow]CI polling: cannot read GitHub check runs "
                        "(GitHub App may lack checks:read permission on this repo).[/yellow]"
                    )
                return "unreadable", []
            if not quiet:
                stderr = result.stderr.strip()
                if stderr:
                    console.print(f"[yellow]CI polling warning: {stderr}[/yellow]")

        time.sleep(POLL_INTERVAL_SECONDS)

    if not saw_checks:
        if saw_api_error:
            return "unreadable", []
        return "no_checks", []
    return "timeout", latest_checks


def run_github_checks_gate(
    cwd: Path,
    repo_owner: str,
    repo_name: str,
    pr_number: int,
    *,
    quiet: bool,
    expected_head_sha: Optional[str] = None,
    required_only: bool = False,
) -> Tuple[bool, str, str]:
    """Strict final-gate check over GitHub PR checks.

    Unlike ``run_ci_validation_loop``, this is verify-only and fail-closed:
    missing, unreadable, skipped, pending, failed, stale, or wrong-head checks
    all fail because this path uses GitHub checks as the full-suite source of
    truth.
    """
    head_sha = (expected_head_sha or "").strip() or _get_pr_head_sha(
        repo_owner, repo_name, pr_number, cwd
    )
    source_name = "required GitHub checks" if required_only else "GitHub checks"

    if not head_sha:
        return False, f"{source_name} gate could not read the current PR head SHA.", ""

    if not quiet:
        console.print(
            f"[bold]Final gate: waiting for {source_name} on PR #{pr_number} "
            f"head {head_sha[:8]}...[/bold]"
        )

    if required_only:
        status, checks = _poll_required_checks(
            repo_owner,
            repo_name,
            pr_number,
            cwd,
            expected_head_sha=head_sha,
            quiet=quiet,
            required_only=True,
        )
    else:
        status, checks = _poll_check_runs_for_head(
            repo_owner,
            repo_name,
            cwd,
            head_sha=head_sha,
            quiet=quiet,
        )
    summary = _render_check_summary(checks)
    skipped = [
        check
        for check in checks
        if check.get("bucket", "").lower() in SKIP_BUCKETS
        or check.get("state", "").lower() in SKIP_BUCKETS
    ]
    unknown = [
        check
        for check in checks
        if check.get("bucket", "").lower() not in (
            FINAL_GATE_PASS_BUCKETS
            | FAIL_BUCKETS
            | PENDING_BUCKETS
            | SKIP_BUCKETS
            | ACTION_REQUIRED_BUCKETS
        )
    ]

    if status == "passed" and checks and not skipped and not unknown:
        return True, f"{source_name} passed on PR head {head_sha[:8]}.\n{summary}", head_sha
    if status == "passed" and not checks:
        return False, f"{source_name} were missing for PR head {head_sha[:8]}.", head_sha
    if skipped:
        return (
            False,
            f"{source_name} included skipped checks on PR head {head_sha[:8]}:\n{summary}",
            head_sha,
        )
    if status == "action_required":
        return (
            False,
            f"{source_name} require manual action on PR head {head_sha[:8]}:\n{summary}",
            head_sha,
        )
    if unknown:
        return (
            False,
            f"{source_name} included unknown check states on PR head {head_sha[:8]}:\n{summary}",
            head_sha,
        )
    if status == "failed":
        return False, f"{source_name} failed on PR head {head_sha[:8]}:\n{summary}", head_sha
    if status in {"no_checks", "unreadable"}:
        return (
            False,
            (
                f"{source_name} were missing or unreadable for PR head "
                f"{head_sha[:8]}; final gate requires GitHub checks as "
                "full-suite truth."
            ),
            head_sha,
        )
    if status == "timeout":
        return (
            False,
            (
                f"{source_name} were pending, stale, or not reported for PR "
                f"head {head_sha[:8]} before the polling timeout:\n{summary}"
            ),
            head_sha,
        )
    if status == "stale_head":
        return False, summary, head_sha
    return (
        False,
        f"{source_name} returned unexpected status {status!r} on PR head {head_sha[:8]}:\n{summary}",
        head_sha,
    )


def _load_failed_runs(
    repo_owner: str,
    repo_name: str,
    cwd: Path,
    head_sha: str,
) -> List[Dict[str, Any]]:
    """List failed GitHub Actions runs for a specific commit SHA."""
    result = _run_gh(
        repo_owner,
        repo_name,
        cwd,
        [
            "run",
            "list",
            "--commit",
            head_sha,
            "--limit",
            "20",
            "--json",
            "databaseId,headSha,name,workflowName,conclusion,url",
        ],
    )
    if result.returncode != 0 or not result.stdout.strip():
        return []

    try:
        runs = json.loads(result.stdout)
    except json.JSONDecodeError:
        return []

    failed_runs: List[Dict[str, Any]] = []
    for run in runs:
        if not isinstance(run, dict):
            continue
        conclusion = str(run.get("conclusion", "")).lower()
        if conclusion not in {"failure", "cancelled", "timed_out", "action_required", "startup_failure"}:
            continue
        failed_runs.append(run)
    return failed_runs


def _filter_runs_for_failures(
    runs: List[Dict[str, Any]],
    failures: List[Dict[str, str]],
) -> List[Dict[str, Any]]:
    """Prefer runs whose names match the failing required checks."""
    failure_names = {
        check.get("name", "").strip().lower()
        for check in failures
        if check.get("name", "").strip()
    }
    if not failure_names:
        return runs

    matched_runs = [
        run
        for run in runs
        if str(run.get("name", "")).strip().lower() in failure_names
        or str(run.get("workflowName", "")).strip().lower() in failure_names
    ]
    return matched_runs or runs


def _fetch_failed_run_view_log(
    repo_owner: str,
    repo_name: str,
    cwd: Path,
    run_id: int,
) -> str:
    """Fetch failed job logs using `gh run view --log-failed`."""
    result = _run_gh(
        repo_owner,
        repo_name,
        cwd,
        ["run", "view", str(run_id), "--log-failed"],
    )
    if result.returncode != 0:
        return ""
    return result.stdout.strip()


def _extract_text_from_zip_bytes(payload: bytes) -> str:
    """Extract readable text from a GitHub Actions log zip payload."""
    if not payload:
        return ""

    try:
        with zipfile.ZipFile(io.BytesIO(payload)) as archive:
            sections: List[str] = []
            for info in sorted(archive.infolist(), key=lambda item: item.filename):
                if info.is_dir():
                    continue
                with archive.open(info) as handle:
                    text = handle.read().decode("utf-8", errors="replace").strip()
                if text:
                    sections.append(f"## {info.filename}\n{text}")
            return "\n\n".join(sections).strip()
    except zipfile.BadZipFile:
        return ""


def _fetch_failed_run_zip_log(
    repo_owner: str,
    repo_name: str,
    cwd: Path,
    run_id: int,
) -> str:
    """Fetch failed job logs through the Actions log zip API."""
    result = _run_gh_bytes(
        repo_owner,
        repo_name,
        cwd,
        ["api", f"repos/{repo_owner}/{repo_name}/actions/runs/{run_id}/logs"],
    )
    if result.returncode != 0:
        return ""
    return _extract_text_from_zip_bytes(result.stdout).strip()


def _collect_failure_logs(
    repo_owner: str,
    repo_name: str,
    cwd: Path,
    head_sha: str,
    failures: List[Dict[str, str]],
) -> str:
    """Collect failed run logs, falling back to the check URLs when needed."""
    runs = _filter_runs_for_failures(
        _load_failed_runs(repo_owner, repo_name, cwd, head_sha),
        failures,
    )

    log_sections: List[str] = []
    for run in runs:
        run_id = run.get("databaseId")
        if not run_id:
            continue

        heading = str(run.get("workflowName") or run.get("name") or f"run {run_id}")
        view_logs = _fetch_failed_run_view_log(repo_owner, repo_name, cwd, int(run_id))
        if view_logs:
            log_sections.append(f"## {heading}\n{view_logs}")
            continue

        zip_logs = _fetch_failed_run_zip_log(repo_owner, repo_name, cwd, int(run_id))
        if zip_logs:
            log_sections.append(f"## {heading}\n{zip_logs}")

        if len("\n\n".join(log_sections)) >= MAX_LOG_CHARS:
            break

    if log_sections:
        return "\n\n".join(log_sections)[:MAX_LOG_CHARS]

    fallback_lines = ["No failed run logs were available via `gh`."]
    for failure in failures:
        link = failure.get("link")
        if link:
            fallback_lines.append(f"- {failure.get('name') or 'unnamed check'}: {link}")
    return "\n".join(fallback_lines)[:MAX_LOG_CHARS]


def _render_step_template(step_template: str, context: Dict[str, Any]) -> str:
    """Preprocess and substitute the step 10 prompt template."""
    rendered = preprocess(
        step_template,
        recursive=True,
        double_curly_brackets=True,
        exclude=list(context.keys()),
    )
    rendered = rendered.replace("{{", "{").replace("}}", "}")
    return substitute_template_variables(rendered, context)


def _commit_ci_fix(
    cwd: Path,
    repo_owner: str,
    repo_name: str,
    issue_number: int,
) -> Tuple[bool, str]:
    """Stage non-artifact changes, commit them, and push to the PR branch."""
    from .agentic_e2e_fix_orchestrator import (
        _get_modified_and_untracked,
        _has_unpushed_commits,
        _is_intermediate_file,
        _push_with_retry,
    )

    files_to_commit = [
        path
        for path in sorted(_get_modified_and_untracked(cwd))
        if not _is_intermediate_file(path)
    ]

    if not files_to_commit:
        if _has_unpushed_commits(cwd):
            push_ok, push_err = _push_with_retry(cwd, repo_owner, repo_name)
            if push_ok:
                return True, "Pushed existing CI fix commits"
            return False, f"Push failed: {push_err}"
        return False, "CI fix reported changes, but no committable files were found"

    for path in files_to_commit:
        stage = _run_command(["git", "add", "--", path], cwd)
        if stage.returncode != 0:
            return False, f"Failed to stage {path}: {stage.stderr.strip()}"

    commit = _run_command(
        ["git", "commit", "-m", f"ci: fix CI failures for #{issue_number}"],
        cwd,
    )
    if commit.returncode != 0:
        if _has_unpushed_commits(cwd):
            push_ok, push_err = _push_with_retry(cwd, repo_owner, repo_name)
            if push_ok:
                return True, "Pushed existing CI fix commits"
            return False, f"Push failed: {push_err}"
        return False, f"Failed to commit CI fix: {commit.stderr.strip()}"

    push_ok, push_err = _push_with_retry(cwd, repo_owner, repo_name)
    if push_ok:
        return True, f"Committed and pushed {len(files_to_commit)} CI fix file(s)"
    return False, f"Push failed: {push_err}"


def post_ci_failure_comment(
    repo_owner: str,
    repo_name: str,
    pr_number: int,
    failures: List[str],
    attempts: int,
    cwd: Path,
) -> bool:
    """Post a structured PR comment for unresolved CI failures."""
    body_lines = [
        "CI validation exhausted its retry budget.",
        "",
        "What was attempted:",
        f"- Polled required CI checks for PR #{pr_number}",
        f"- Ran automated CI fix iterations: {attempts}",
        "- Retrieved failure logs or check URLs for each failing check",
        "",
        "Remaining required check failures:",
    ]
    if failures:
        body_lines.extend(f"- {failure}" for failure in failures)
    else:
        body_lines.append("- Required checks did not report a concrete failure summary.")

    return post_pr_comment(
        repo_owner=repo_owner,
        repo_name=repo_name,
        pr_number=pr_number,
        body="\n".join(body_lines),
        cwd=cwd,
    )


def run_ci_validation_loop(
    cwd: Path,
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    max_retries: int,
    step_template: str,
    run_agentic_task_fn: Callable[..., Tuple[bool, str, float, str]],
    timeout: float,
    quiet: bool,
    expected_head_sha_override: Optional[str] = None,
) -> Tuple[bool, str, float]:
    """Poll required PR checks and iterate on CI-only failures until they pass.

    ``expected_head_sha_override`` lets a caller wait for a specific PR head
    SHA instead of inferring it from ``cwd``'s local HEAD — useful when the
    head being validated was pushed from a different worktree, so ``cwd``'s
    local HEAD is stale relative to the PR remote. Passing the exact PR head
    SHA via this override makes the poll wait for the correct head and
    prevents the timeout from burning while ``cwd``'s stale HEAD is compared
    to the advanced remote.
    """
    total_cost = 0.0
    max_retries = max(0, int(max_retries))
    pr_number = _find_open_pr_number(repo_owner, repo_name, cwd)

    if pr_number is None:
        return True, "No open PR found for current branch; skipping CI validation", total_cost

    ci_system = detect_ci_system(cwd)
    if not quiet:
        console.print(
            f"[bold][Step 10/10] Waiting for required CI checks on PR #{pr_number} "
            f"({ci_system})...[/bold]"
        )

    time.sleep(INITIAL_POLL_DELAY_SECONDS)

    fix_attempt = 0
    last_failures: List[Dict[str, str]] = []
    last_summary = "No required CI checks were reported."
    posted_manual_trigger_comments: set[str] = set()

    while True:
        head_sha = (
            expected_head_sha_override
            or _get_pr_head_sha(repo_owner, repo_name, pr_number, cwd)
            or _get_head_sha(cwd)
        )
        status, checks = _poll_required_checks(
            repo_owner,
            repo_name,
            pr_number,
            cwd,
            expected_head_sha=head_sha,
            quiet=quiet,
        )

        if status == "passed":
            return True, "Required CI checks passed", total_cost
        if status == "no_checks":
            # Requirement 12: cross-check the live PR head's real check runs before
            # treating "no_checks" as ready. _poll_required_checks returns "no_checks"
            # for several distinct situations that are NOT "genuinely no required
            # checks" (App-token-unreadable status rollup, required checks not yet
            # reported, or a poll timeout with nothing read). Failing open on all of
            # these silently green-lights a PR whose live head actually has failing
            # checks. Reuse the REST Checks API path the final gate uses.
            cross_head_sha = expected_head_sha_override or _get_pr_head_sha(
                repo_owner,
                repo_name,
                pr_number,
                cwd,
            ) or head_sha
            cross_status, cross_checks = _poll_check_runs_for_head(
                repo_owner=repo_owner,
                repo_name=repo_name,
                head_sha=cross_head_sha,
                cwd=cwd,
                quiet=quiet,
            )
            # Only treat as genuinely having no checks if the cross-check confirms it.
            if cross_status == "no_checks":
                return True, "No CI checks detected", total_cost
            # The required-check poll could not read the rollup, but the live
            # head's real check runs are all green: the PR genuinely passed.
            # Return ready here instead of falling through to the failure path,
            # otherwise an already-passing PR whose GraphQL statusCheckRollup is
            # unreadable by the App token (the exact condition this cross-check
            # exists for) would drive a pointless fix loop or be reported as not
            # ready.
            if cross_status == "passed":
                return (
                    True,
                    f"Required CI checks passed on live PR head {cross_head_sha[:8]}",
                    total_cost,
                )
            # Otherwise the PR is not ready; fall through with the real check status.
            status = cross_status
            checks = cross_checks
            if status == "unreadable":
                message = (
                    f"GitHub check runs were missing or unreadable for PR head "
                    f"{cross_head_sha[:8]}; CI validation cannot verify the PR."
                )
                post_ci_failure_comment(
                    repo_owner=repo_owner,
                    repo_name=repo_name,
                    pr_number=pr_number,
                    failures=[message],
                    attempts=fix_attempt,
                    cwd=cwd,
                )
                return False, message, total_cost
        if status == "timeout":
            # A poll timeout means the required checks never reached
            # a terminal state in the window. Two distinct cases must be split:
            #
            #   (a) we OBSERVED the required checks and they are merely pending
            #       (`checks` is non-empty). A genuine check FAILURE returns
            #       "failed" from _classify_check_result / _poll_required_checks
            #       and never reaches this branch, so observed-at-timeout checks
            #       are pending, never failing. This is genuinely INCONCLUSIVE
            #       (commonly a manually-triggered or external check the bot
            #       structurally cannot run, e.g. a /gcbrun-gated build) — fail
            #       OPEN so a pending check does not retroactively hard-fail an
            #       already-committed fix. Leave a neutral best-effort note (NOT
            #       a CI-failure comment) and proceed.
            #
            #   (b) we NEVER got a clean read (`checks` is empty): the PR head
            #       never matched the expected SHA, or the rollup was unreadable
            #       for the whole window. We cannot prove the checks are merely
            #       pending rather than failing, so fail CLOSED rather than
            #       green-light a head whose real status we never saw.
            if checks:
                last_failures = checks
                last_summary = _render_check_summary(checks)
                note = (
                    f"Required CI checks for PR #{pr_number} did not reach a "
                    f"terminal state within the {MAX_POLL_SECONDS // 60}-minute "
                    f"poll window (still pending or unreported). Treating CI as "
                    f"inconclusive and proceeding: external or manually-triggered "
                    f"checks the bot cannot run are best-effort, not a hard gate. "
                    f"Last observed status:\n{last_summary}"
                )
                try:
                    post_pr_comment(
                        repo_owner=repo_owner,
                        repo_name=repo_name,
                        pr_number=pr_number,
                        body=note,
                        cwd=cwd,
                    )
                except Exception:  # noqa: BLE001 — informational note is best-effort
                    pass
                return (
                    True,
                    (
                        "Required CI checks did not complete within the poll "
                        "window (still pending or unavailable); proceeding — "
                        "external CI is best-effort and treated as inconclusive."
                    ),
                    total_cost,
                )
            # Case (b): the required checks were never read for the expected head.
            post_ci_failure_comment(
                repo_owner=repo_owner,
                repo_name=repo_name,
                pr_number=pr_number,
                failures=[
                    "Could not read the required CI checks before the poll "
                    "window elapsed: the PR head never matched the expected SHA, "
                    "or the check status was unreadable for the whole window."
                ],
                attempts=fix_attempt,
                cwd=cwd,
            )
            return (
                False,
                (
                    "Could not read required CI checks before the poll window "
                    "elapsed (the PR head never matched the expected SHA, or the "
                    "checks were unreadable); failing closed."
                ),
                total_cost,
            )
        if status == "action_required":
            trigger_comment = _next_configured_manual_trigger_comment(
                cwd,
                checks,
                posted_manual_trigger_comments,
            )
            if trigger_comment:
                trigger_posted = False
                try:
                    trigger_posted = post_pr_comment(
                        repo_owner=repo_owner,
                        repo_name=repo_name,
                        pr_number=pr_number,
                        body=trigger_comment,
                        cwd=cwd,
                    )
                except Exception:  # noqa: BLE001 — fall back to inconclusive reporting below
                    trigger_posted = False

                if trigger_posted:
                    posted_manual_trigger_comments.add(trigger_comment)
                    if not quiet:
                        console.print(
                            "[yellow]Posted configured manual CI trigger comment; "
                            "waiting for checks to re-run...[/yellow]"
                        )
                    time.sleep(INITIAL_POLL_DELAY_SECONDS)
                    continue

            last_failures = checks
            last_summary = _render_check_summary(checks)
            note = (
                f"Required CI checks for PR #{pr_number} require manual action "
                "or an external trigger before they can complete. Treating CI "
                "as inconclusive and proceeding: these checks are not code "
                "failures for the automated CI-fix loop to repair. Last "
                f"observed status:\n{last_summary}"
            )
            try:
                post_pr_comment(
                    repo_owner=repo_owner,
                    repo_name=repo_name,
                    pr_number=pr_number,
                    body=note,
                    cwd=cwd,
                )
            except Exception:  # noqa: BLE001 — informational note is best-effort
                pass
            return (
                True,
                (
                    "Required CI checks require manual action or an external "
                    "trigger; proceeding — external CI is best-effort and "
                    "treated as inconclusive."
                ),
                total_cost,
            )
        if status == "stale_head":
            last_failures = checks
            last_summary = _render_check_summary(last_failures)
            post_ci_failure_comment(
                repo_owner=repo_owner,
                repo_name=repo_name,
                pr_number=pr_number,
                failures=last_summary.splitlines(),
                attempts=fix_attempt,
                cwd=cwd,
            )
            return False, last_summary, total_cost

        last_failures = checks
        last_summary = _render_check_summary(last_failures)
        ci_failure_logs = _collect_failure_logs(
            repo_owner=repo_owner,
            repo_name=repo_name,
            cwd=cwd,
            head_sha=head_sha,
            failures=last_failures,
        )
        external_reason = None
        if _external_ci_setup_fail_open_enabled(cwd):
            external_reason = _classify_external_ci_failure(last_failures, ci_failure_logs)
        if external_reason:
            note = (
                f"Required CI checks for PR #{pr_number} failed for an external "
                f"CI setup reason: {external_reason} Treating CI as inconclusive "
                "and proceeding: this is not a code failure for the automated "
                "CI-fix loop to repair. Last observed status:\n"
                f"{last_summary}"
            )
            try:
                post_pr_comment(
                    repo_owner=repo_owner,
                    repo_name=repo_name,
                    pr_number=pr_number,
                    body=note,
                    cwd=cwd,
                )
            except Exception:  # noqa: BLE001 — informational note is best-effort
                pass
            return (
                True,
                (
                    "Required CI checks failed for an external CI setup reason; "
                    "proceeding — external CI is best-effort and treated as "
                    "inconclusive."
                ),
                total_cost,
            )

        if fix_attempt >= max_retries:
            post_ci_failure_comment(
                repo_owner=repo_owner,
                repo_name=repo_name,
                pr_number=pr_number,
                failures=last_summary.splitlines(),
                attempts=fix_attempt,
                cwd=cwd,
            )
            return False, last_summary, total_cost

        fix_attempt += 1

        if not quiet:
            console.print(
                f"[yellow][Step 10/10] Required CI checks failed; applying CI fix "
                f"attempt {fix_attempt}/{max_retries}...[/yellow]"
            )

        prompt = _render_step_template(
            step_template,
            {
                "issue_url": f"https://github.com/{repo_owner}/{repo_name}/issues/{issue_number}",
                "repo_owner": repo_owner,
                "repo_name": repo_name,
                "issue_number": issue_number,
                "ci_attempt": fix_attempt,
                "ci_max_retries": max_retries,
                "ci_check_results": last_summary,
                "ci_failure_logs": ci_failure_logs,
                "ci_system": ci_system,
            },
        )

        success, output, cost, _model = run_agentic_task_fn(
            instruction=prompt,
            cwd=cwd,
            verbose=False,
            quiet=quiet,
            timeout=timeout,
            label=f"ci_validation_attempt{fix_attempt}",
            max_retries=DEFAULT_MAX_RETRIES,
        )
        total_cost += cost

        if not success:
            return False, f"CI fix attempt {fix_attempt} failed: {output}", total_cost

        if "CI_FIX_APPLIED" not in output:
            post_ci_failure_comment(
                repo_owner=repo_owner,
                repo_name=repo_name,
                pr_number=pr_number,
                failures=last_summary.splitlines(),
                attempts=fix_attempt,
                cwd=cwd,
            )
            return False, "CI fix task did not apply an actionable fix", total_cost

        commit_success, commit_message = _commit_ci_fix(
            cwd=cwd,
            repo_owner=repo_owner,
            repo_name=repo_name,
            issue_number=issue_number,
        )
        if not commit_success:
            return False, commit_message, total_cost

        if not quiet:
            console.print(f"[green]{commit_message}[/green]")
        time.sleep(INITIAL_POLL_DELAY_SECONDS)
