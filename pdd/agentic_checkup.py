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
    _run_gh_command,
)
from .agentic_checkup_orchestrator import run_agentic_checkup_orchestrator
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


def run_agentic_checkup(
    issue_url: str,
    *,
    verbose: bool = False,
    quiet: bool = False,
    no_fix: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True,
) -> Tuple[bool, str, float, str]:
    """Run agentic checkup workflow from a GitHub issue URL.

    Args:
        issue_url: GitHub issue URL describing what to check.
        verbose: Enable detailed logging.
        quiet: Suppress standard output.
        no_fix: Report only, don't apply fixes.
        timeout_adder: Additional seconds to add to each step timeout.
        use_github_state: Whether to persist state to GitHub comments.

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

    title = issue_data.get("title", "")
    body = issue_data.get("body", "") or ""

    # Fetch comments for full context
    comments_url = issue_data.get("comments_url", "")
    comments_text = _fetch_comments(comments_url) if comments_url else ""

    full_content = (
        f"Title: {title}\n"
        f"Description:\n{body}\n\n"
        f"Comments:\n{comments_text}"
    )

    # Escape braces so .format() doesn't choke on user content
    title = _escape_format_braces(title)
    full_content = _escape_format_braces(full_content)

    # 4. Load project context
    project_root = _find_project_root(Path.cwd())
    architecture, _ = _load_architecture_json(project_root)
    arch_json_str = json.dumps(architecture, indent=2) if architecture else "No architecture.json available."
    arch_json_str = _escape_format_braces(arch_json_str)
    pddrc_content = _escape_format_braces(_load_pddrc_content(project_root))

    if not quiet:
        console.print("[bold]Running agentic checkup...[/bold]")

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
            body = comment.get("body", "")
            formatted.append(f"--- Comment by {user} ---\n{body}\n")
        return "\n".join(formatted)
    except (json.JSONDecodeError, TypeError):
        return ""
