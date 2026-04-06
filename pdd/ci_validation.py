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

# Substring gh CLI prints to stderr when no required checks are configured.
# Centralised so tests can reference the same constant instead of duplicating
# a magic string.
GH_NO_REQUIRED_CHECKS_PHRASE = "no required checks"


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


def _classify_check_result(returncode: int, checks: List[Dict[str, str]]) -> str:
    """Classify `gh pr checks` output using both exit code and bucket values."""
    buckets = [check.get("bucket", "").lower() for check in checks if check.get("bucket")]

    if any(bucket in FAIL_BUCKETS for bucket in buckets):
        return "failed"
    if checks and all(bucket in PASS_BUCKETS for bucket in buckets):
        return "passed"
    if any(bucket in PENDING_BUCKETS for bucket in buckets):
        return "pending"

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
) -> Tuple[str, List[Dict[str, str]]]:
    """Poll required checks until they pass, fail, or time out."""
    saw_checks = False
    saw_ambiguous_error = False
    matched_expected_head = not bool(expected_head_sha)
    latest_checks: List[Dict[str, str]] = []
    start = time.monotonic()

    while time.monotonic() - start < MAX_POLL_SECONDS:
        remote_head_sha = _get_pr_head_sha(repo_owner, repo_name, pr_number, cwd)
        if expected_head_sha and remote_head_sha:
            matched_expected_head = remote_head_sha == expected_head_sha
            if not matched_expected_head:
                if not quiet:
                    console.print(
                        f"[dim]Waiting for PR #{pr_number} to update to head {expected_head_sha[:7]}...[/dim]"
                    )
                time.sleep(POLL_INTERVAL_SECONDS)
                continue

        result = _run_gh(
            repo_owner,
            repo_name,
            cwd,
            [
                "pr",
                "checks",
                str(pr_number),
                "--required",
                "--json",
                "name,state,bucket,link",
            ],
        )

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
            if GH_NO_REQUIRED_CHECKS_PHRASE in stderr_lower:
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

        status = _classify_check_result(result.returncode, latest_checks)

        if status in {"passed", "failed"}:
            return status, latest_checks

        if result.returncode not in {0, 1, 8} and not quiet:
            stderr = result.stderr.strip()
            if stderr:
                console.print(f"[yellow]CI polling warning: {stderr}[/yellow]")

        time.sleep(POLL_INTERVAL_SECONDS)

    if not saw_checks and matched_expected_head and not saw_ambiguous_error:
        return "no_checks", []
    return "timeout", latest_checks


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
        exclude_keys=list(context.keys()),
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
        f"- Retrieved failure logs or check URLs for each failing check",
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
) -> Tuple[bool, str, float]:
    """Poll required PR checks and iterate on CI-only failures until they pass."""
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

    while True:
        head_sha = _get_head_sha(cwd)
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
            return True, "No CI checks detected", total_cost
        if status == "timeout":
            if checks:
                last_failures = checks
                last_summary = _render_check_summary(checks)
            post_ci_failure_comment(
                repo_owner=repo_owner,
                repo_name=repo_name,
                pr_number=pr_number,
                failures=last_summary.splitlines(),
                attempts=fix_attempt,
                cwd=cwd,
            )
            return False, "Timed out waiting for required CI checks to complete", total_cost

        last_failures = checks
        last_summary = _render_check_summary(last_failures)
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
        ci_failure_logs = _collect_failure_logs(
            repo_owner=repo_owner,
            repo_name=repo_name,
            cwd=cwd,
            head_sha=head_sha,
            failures=last_failures,
        )

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
