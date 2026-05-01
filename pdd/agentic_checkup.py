"""
Agentic checkup: LLM-driven project health check from a GitHub issue.

Entry point for ``pdd checkup <github_issue_url>``. Fetches issue content, loads
project context (architecture.json, .pddrc), then dispatches the multi-step
orchestrator that explores the project, identifies problems, and optionally
fixes them — one step per LLM call for reliability.
"""
from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, Dict, Optional, Tuple

from rich.console import Console

from .agentic_change import (
    _check_gh_cli,
    _escape_format_braces,
    _parse_issue_url,
    _parse_pr_url,
    _run_gh_command,
)
from .agentic_checkup_orchestrator import run_agentic_checkup_orchestrator
from .checkup_review_loop import (
    ReviewLoopConfig,
    ReviewLoopContext,
    parse_reviewers,
    parse_severity_list,
    parse_state_list,
    run_checkup_review_loop,
)
from .agentic_sync import _find_project_root, _load_architecture_json

console = Console()


def _extract_json_from_text(text: str) -> Optional[Dict[str, Any]]:
    """Extract a JSON object from agent output text.

    Handles markdown code blocks and raw JSON.
    """
    if not text or not text.strip():
        return None

    # Try markdown code blocks first
    json_block_pattern = r"```(?:json)?\s*(\{.*?\})\s*```"
    match = re.search(json_block_pattern, text, re.DOTALL)

    if match:
        json_str = match.group(1)
    else:
        # Try to find the first opening brace and last closing brace
        start = text.find("{")
        end = text.rfind("}")
        if start != -1 and end != -1 and end > start:
            json_str = text[start : end + 1]
        else:
            return None

    try:
        result = json.loads(json_str)
        if isinstance(result, dict):
            return result
        return None
    except json.JSONDecodeError:
        return None


def _load_pddrc_content(project_root: Path) -> str:
    """Load .pddrc file content from the project root."""
    pddrc_path = project_root / ".pddrc"
    if not pddrc_path.exists():
        return "No .pddrc found."
    try:
        return pddrc_path.read_text(encoding="utf-8")
    except OSError:
        return "Failed to read .pddrc."


def _post_checkup_comment(
    owner: str,
    repo: str,
    issue_number: int,
    report: Dict[str, Any],
) -> None:
    """Post checkup results as a GitHub issue comment."""
    issues = report.get("issues", [])
    changed_files = report.get("changed_files", [])
    tech_stack = report.get("tech_stack", [])
    success = report.get("success", False)
    message = report.get("message", "")

    status_emoji = "+" if success else "x"

    body_lines = [
        f"## PDD Checkup Report {status_emoji}",
        "",
        f"**Summary:** {message}",
        "",
    ]

    if tech_stack:
        body_lines.append(f"**Tech stack:** {', '.join(tech_stack)}")
        body_lines.append("")

    if issues:
        body_lines.append("### Issues Found")
        body_lines.append("")
        body_lines.append("| Severity | Category | Module | Description | Fixed |")
        body_lines.append("|----------|----------|--------|-------------|-------|")
        for issue in issues:
            sev = issue.get("severity", "?")
            cat = issue.get("category", "?")
            mod = issue.get("module", "?")
            desc = issue.get("description", "?")
            fixed = "yes" if issue.get("fixed", False) else "no"
            body_lines.append(f"| {sev} | {cat} | {mod} | {desc} | {fixed} |")
        body_lines.append("")

    if changed_files:
        body_lines.append("### Changed Files")
        body_lines.append("")
        for f in changed_files:
            body_lines.append(f"- `{f}`")
        body_lines.append("")

    body = "\n".join(body_lines)

    _run_gh_command([
        "api",
        f"repos/{owner}/{repo}/issues/{issue_number}/comments",
        "-X", "POST",
        "-f", f"body={body}",
    ])


def _post_error_comment(owner: str, repo: str, issue_number: int, message: str) -> None:
    """Post an error comment on the GitHub issue."""
    body = (
        "## PDD Checkup - Error\n\n"
        f"```\n{message[:1000]}\n```\n"
    )
    _run_gh_command([
        "api",
        f"repos/{owner}/{repo}/issues/{issue_number}/comments",
        "-X", "POST",
        "-f", f"body={body}",
    ])


def _fetch_pr_context(owner: str, repo: str, pr_number: int) -> str:
    """Fetch PR, comments, reviews, and changed-file context for review-loop prompts."""
    success, output = _run_gh_command(
        ["api", f"repos/{owner}/{repo}/pulls/{pr_number}"]
    )
    if not success:
        return f"Failed to fetch PR context: {output}"
    try:
        data = json.loads(output)
    except json.JSONDecodeError:
        return "Failed to parse PR context JSON."

    head = data.get("head") or {}
    base = data.get("base") or {}
    changed_files = _fetch_pr_changed_files(owner, repo, pr_number)
    conversation = _fetch_pr_conversation(owner, repo, pr_number)
    reviews = _fetch_pr_reviews(owner, repo, pr_number)
    return _truncate_context(
        f"Title: {data.get('title', '')}\n"
        f"Base: {base.get('label') or base.get('ref') or ''}\n"
        f"Head: {head.get('label') or head.get('ref') or ''}\n"
        f"State: {data.get('state', '')}\n"
        f"Mergeable state: {data.get('mergeable_state', '')}\n"
        f"Description:\n{data.get('body') or ''}\n\n"
        f"Changed files:\n{changed_files}\n\n"
        f"PR conversation comments:\n{conversation}\n\n"
        f"PR reviews:\n{reviews}",
        60000,
    )


def _fetch_pr_changed_files(owner: str, repo: str, pr_number: int) -> str:
    """Fetch a concise changed-file inventory for reviewer context."""
    success, output = _run_gh_command(
        ["api", f"repos/{owner}/{repo}/pulls/{pr_number}/files?per_page=100"]
    )
    if not success:
        return f"Failed to fetch changed files: {output}"
    try:
        files = json.loads(output)
    except json.JSONDecodeError:
        return "Failed to parse changed-file JSON."
    if not isinstance(files, list) or not files:
        return "No changed files reported."

    lines = []
    for item in files:
        if not isinstance(item, dict):
            continue
        filename = item.get("filename") or ""
        status = item.get("status") or ""
        additions = item.get("additions", 0)
        deletions = item.get("deletions", 0)
        patch = item.get("patch") or ""
        patch_hint = ""
        if patch:
            patch_hint = " | patch excerpt: " + _one_line(patch, 500)
        lines.append(
            f"- {filename} ({status}, +{additions}/-{deletions}){patch_hint}"
        )
    return "\n".join(lines) if lines else "No changed files reported."


def _fetch_pr_conversation(owner: str, repo: str, pr_number: int) -> str:
    """Fetch PR issue-thread comments, which often explain direction changes."""
    success, output = _run_gh_command(
        ["api", f"repos/{owner}/{repo}/issues/{pr_number}/comments?per_page=100"]
    )
    if not success:
        return f"Failed to fetch PR comments: {output}"
    return _format_github_comment_list(output, body_key="body")


def _fetch_pr_reviews(owner: str, repo: str, pr_number: int) -> str:
    """Fetch submitted PR reviews for reviewer context."""
    success, output = _run_gh_command(
        ["api", f"repos/{owner}/{repo}/pulls/{pr_number}/reviews?per_page=100"]
    )
    if not success:
        return f"Failed to fetch PR reviews: {output}"
    return _format_github_comment_list(output, body_key="body", include_state=True)


def _format_github_comment_list(
    output: str,
    *,
    body_key: str,
    include_state: bool = False,
) -> str:
    try:
        items = json.loads(output)
    except json.JSONDecodeError:
        return "Failed to parse GitHub comment JSON."
    if not isinstance(items, list) or not items:
        return "None."

    lines = []
    for item in items:
        if not isinstance(item, dict):
            continue
        user = item.get("user") or {}
        author = user.get("login") if isinstance(user, dict) else ""
        created = item.get("submitted_at") or item.get("created_at") or ""
        state = f" [{item.get('state')}]" if include_state and item.get("state") else ""
        body = _one_line(item.get(body_key) or "", 1200)
        if not body:
            continue
        lines.append(f"- {author}{state} at {created}: {body}")
    return "\n".join(lines) if lines else "None."


def _one_line(text: str, limit: int) -> str:
    compact = re.sub(r"\s+", " ", text or "").strip()
    if len(compact) <= limit:
        return compact
    return compact[: max(0, limit - 3)].rstrip() + "..."


def _truncate_context(text: str, limit: int) -> str:
    if len(text) <= limit:
        return text
    return text[: max(0, limit - 120)].rstrip() + (
        "\n\n[PR context truncated to keep the reviewer prompt within budget.]"
    )


def _truncate_issue_context(text: str, limit: int) -> str:
    """Truncate issue context while preserving the latest issue comments.

    Issue bodies often become stale while later maintainer/user comments narrow
    or replace the contract. Review-loop prompts must retain that tail context
    when large bot logs force truncation.
    """
    if len(text) <= limit:
        return text
    marker = "\nComments:\n"
    if marker not in text:
        return _truncate_context(text, limit)

    header, comments = text.split(marker, 1)
    notice = "\n\n[Issue context truncated; latest comments preserved.]"
    available = max(0, limit - len(marker) - len(notice))
    tail_budget = min(max(limit // 3, 12000), max(0, available // 2))
    head_budget = max(0, available - tail_budget)

    if len(header) > head_budget:
        header = header[:head_budget].rstrip()
    if len(comments) > tail_budget:
        comment_notice = "[Older issue comments truncated; newest comments retained.]\n"
        retained_budget = max(0, tail_budget - len(comment_notice))
        comments = comment_notice + comments[-retained_budget:].lstrip()

    return f"{header.rstrip()}{marker}{comments.rstrip()}{notice}"


def run_agentic_checkup(
    issue_url: str,
    *,
    verbose: bool = False,
    quiet: bool = False,
    no_fix: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True,
    reasoning_time: Optional[float] = None,
    pr_url: Optional[str] = None,
    review_loop: bool = False,
    review_only: bool = False,
    reviewers: str = "codex,claude",
    reviewer: Optional[str] = None,
    fixer: Optional[str] = None,
    max_review_rounds: int = 5,
    max_review_cost: float = 10.0,
    max_review_minutes: float = 90.0,
    require_all_reviewers_clean: bool = True,
    continue_on_reviewer_limit: bool = False,
    require_final_fresh_review: bool = True,
    blocking_severities: Optional[str] = None,
    clean_reviewer_states: Optional[str] = None,
) -> Tuple[bool, str, float, str]:
    """Run agentic checkup workflow from a GitHub issue URL.

    Args:
        issue_url: GitHub issue URL describing what to check.
        verbose: Enable detailed logging.
        quiet: Suppress standard output.
        no_fix: Report only, don't apply fixes.
        timeout_adder: Additional seconds to add to each step timeout.
        use_github_state: Whether to persist state to GitHub comments.
        pr_url: When set, verify this existing PR against ``issue_url`` instead
            of creating a new branch/PR. Step 8 (create_pr) is skipped and the
            worktree is based on the PR's head branch.
        review_loop: When true in PR mode, run the primary-reviewer/fixer
            loop instead of the legacy single-pass checkup path.
        review_only: When true with ``review_loop``, run only the primary
            reviewer first pass and do not invoke the fixer or push changes.

    Returns:
        Tuple of (success, message, total_cost, model_used).
    """
    # 1. Check gh CLI
    if not _check_gh_cli():
        return (
            False,
            "GitHub CLI (gh) not found. Install from https://cli.github.com/",
            0.0,
            "",
        )

    # 2. Parse URL
    parsed = _parse_issue_url(issue_url)
    if not parsed:
        return False, f"Invalid GitHub issue URL: {issue_url}", 0.0, ""

    owner, repo, issue_number = parsed

    # Parse PR URL once up-front so invalid PR mode fails before any API calls.
    pr_owner: Optional[str] = None
    pr_repo: Optional[str] = None
    pr_number: Optional[int] = None
    if pr_url is not None:
        pr_parsed = _parse_pr_url(pr_url)
        if not pr_parsed:
            return False, f"Invalid GitHub PR URL: {pr_url}", 0.0, ""
        pr_owner, pr_repo, pr_number = pr_parsed

    if not quiet:
        console.print(f"[bold]Fetching issue #{issue_number} from {owner}/{repo}...[/bold]")

    # 3. Fetch issue content
    success, issue_json = _run_gh_command(
        ["api", f"repos/{owner}/{repo}/issues/{issue_number}"]
    )
    if not success:
        return False, f"Failed to fetch issue: {issue_json}", 0.0, ""

    try:
        issue_data = json.loads(issue_json)
    except json.JSONDecodeError:
        return False, "Failed to parse issue JSON", 0.0, ""

    raw_title = issue_data.get("title", "")
    body = issue_data.get("body", "") or ""

    # Fetch comments for full context
    comments_url = issue_data.get("comments_url", "")
    comments_text = _fetch_comments(comments_url) if comments_url else ""

    raw_full_content = (
        f"Title: {raw_title}\n"
        f"Description:\n{body}\n\n"
        f"Comments:\n{comments_text}"
    )

    # Escape braces so .format() doesn't choke on user content
    title = _escape_format_braces(raw_title)
    full_content = _escape_format_braces(raw_full_content)

    # 4. Load project context
    project_root = _find_project_root(Path.cwd())
    architecture, _ = _load_architecture_json(project_root)
    raw_arch_json_str = (
        json.dumps(architecture, indent=2)
        if architecture
        else "No architecture.json available."
    )
    arch_json_str = _escape_format_braces(raw_arch_json_str)
    raw_pddrc_content = _load_pddrc_content(project_root)
    pddrc_content = _escape_format_braces(raw_pddrc_content)

    if not quiet:
        console.print("[bold]Running agentic checkup...[/bold]")

    if review_loop:
        if pr_url is None or pr_owner is None or pr_repo is None or pr_number is None:
            return False, "--review-loop requires --pr and --issue.", 0.0, ""
        loop_issue_content = _truncate_issue_context(raw_full_content, 60000)
        loop_architecture = _truncate_context(raw_arch_json_str, 40000)
        loop_context = ReviewLoopContext(
            issue_url=issue_url,
            issue_content=loop_issue_content,
            repo_owner=owner,
            repo_name=repo,
            issue_number=issue_number,
            issue_title=raw_title,
            architecture_json=loop_architecture,
            pddrc_content=raw_pddrc_content,
            pr_url=pr_url,
            pr_owner=pr_owner,
            pr_repo=pr_repo,
            pr_number=pr_number,
            project_root=project_root,
            pr_content=_fetch_pr_context(pr_owner, pr_repo, pr_number),
        )
        loop_config = ReviewLoopConfig(
            reviewers=parse_reviewers(reviewers),
            reviewer=reviewer,
            fixer=fixer,
            review_only=review_only,
            max_rounds=max_review_rounds,
            max_cost=max_review_cost,
            max_minutes=max_review_minutes,
            require_all_reviewers_clean=require_all_reviewers_clean,
            continue_on_reviewer_limit=continue_on_reviewer_limit,
            require_final_fresh_review=require_final_fresh_review,
            timeout_adder=timeout_adder,
            reasoning_time=reasoning_time,
            blocking_severities=parse_severity_list(blocking_severities),
            clean_reviewer_states=parse_state_list(clean_reviewer_states),
        )
        return run_checkup_review_loop(
            context=loop_context,
            config=loop_config,
            cwd=project_root,
            verbose=verbose,
            quiet=quiet,
            use_github_state=use_github_state,
        )

    # 5. Invoke orchestrator
    try:
        orch_success, orch_message, orch_cost, orch_model = run_agentic_checkup_orchestrator(
            issue_url=issue_url,
            issue_content=full_content,
            repo_owner=owner,
            repo_name=repo,
            issue_number=issue_number,
            issue_title=title,
            architecture_json=arch_json_str,
            pddrc_content=pddrc_content,
            cwd=project_root,
            verbose=verbose,
            quiet=quiet,
            no_fix=no_fix,
            timeout_adder=timeout_adder,
            use_github_state=use_github_state,
            reasoning_time=reasoning_time,
            pr_url=pr_url,
            pr_owner=pr_owner,
            pr_repo=pr_repo,
            pr_number=pr_number,
        )
    except Exception as exc:
        msg = f"Orchestrator failed: {exc}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        _post_error_comment(owner, repo, issue_number, msg)
        return False, msg, 0.0, ""

    if not orch_success:
        return False, orch_message, orch_cost, orch_model

    # 6. Parse JSON report from step 7 output
    step7_output = ""
    # The orchestrator doesn't return step outputs directly, so we try to
    # extract JSON from the final message or rely on what the agent posted.
    # The orchestrator returns "Checkup complete" on success, but the step 7
    # agent should have posted a comment + output JSON. We treat orchestrator
    # success as overall success.

    if not quiet:
        console.print(f"[bold]Checkup complete:[/bold] {orch_message}")

    return orch_success, orch_message, orch_cost, orch_model


def _fetch_comments(comments_url: str) -> str:
    """Fetch comments for an issue to provide full context."""
    success, output = _run_gh_command(["api", comments_url, "--paginate"])
    if not success:
        return ""

    try:
        comments_data = json.loads(output)
        formatted = []
        for comment in comments_data:
            user = comment.get("user", {}).get("login", "Unknown")
            created_at = str(comment.get("created_at") or "").strip()
            body = comment.get("body", "")
            if created_at:
                formatted.append(f"--- Comment by {user} at {created_at} ---\n{body}\n")
            else:
                formatted.append(f"--- Comment by {user} ---\n{body}\n")
        return "\n".join(formatted)
    except (json.JSONDecodeError, TypeError):
        return ""
