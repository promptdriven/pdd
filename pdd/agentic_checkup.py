from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from rich.console import Console

from .agentic_change import (
    _check_gh_cli,
    _escape_format_braces,
    _parse_issue_url,
    _parse_pr_url,
)
from .agentic_checkup_orchestrator import run_agentic_checkup_orchestrator
from .agentic_sync import _load_architecture_json
from .architecture_registry import find_project_root

console = Console()


# Truncation budgets for review-loop context construction. Reviewer prompts
# are large already; we don't want to bury the rubric under bot noise.
_REVIEW_LOOP_ISSUE_LIMIT = 20_000
_REVIEW_LOOP_COMMENTS_LIMIT = 20_000
_REVIEW_LOOP_PR_LIMIT = 60_000
_REVIEW_LOOP_PDDRC_LIMIT = 8_000
_REVIEW_LOOP_ARCH_LIMIT = 40_000

_PR_BODY_LIMIT = 8_000
_PR_PATCH_PER_FILE_LIMIT = 4_000
_PR_PATCH_TOTAL_LIMIT = 40_000
_PR_COMMENT_LIMIT = 12_000
_PR_REVIEWS_LIMIT = 12_000


def _truncate(text: str, limit: int, *, label: str = "content") -> str:
    """Truncate text to ``limit`` characters with a clear marker."""
    if text is None:
        return ""
    if len(text) <= limit:
        return text
    head = text[:limit]
    omitted = len(text) - limit
    return f"{head}\n\n... [truncated: {omitted} chars of {label} omitted] ..."


def _extract_json_from_text(text: str) -> Optional[Dict[str, Any]]:
    """Extract a JSON object from raw text or a markdown ```json``` block."""
    if not text:
        return None

    # Try fenced code block first.
    fence_re = re.compile(
        r"```(?:json|JSON)?\s*(\{.*?\})\s*```", re.DOTALL
    )
    match = fence_re.search(text)
    candidates: List[str] = []
    if match:
        candidates.append(match.group(1))

    # Fallback: find the first balanced top-level object.
    stripped = text.strip()
    if stripped.startswith("{"):
        candidates.append(stripped)

    # Last resort: greedy match from first { to last }.
    first = text.find("{")
    last = text.rfind("}")
    if first != -1 and last != -1 and last > first:
        candidates.append(text[first : last + 1])

    for candidate in candidates:
        try:
            parsed = json.loads(candidate)
            if isinstance(parsed, dict):
                return parsed
        except (json.JSONDecodeError, ValueError):
            continue
    return None


def _load_pddrc_content(project_root: Path) -> str:
    """Return raw .pddrc content or a sentinel if missing/unreadable."""
    pddrc_path = project_root / ".pddrc"
    if not pddrc_path.exists():
        return "No .pddrc found."
    try:
        return pddrc_path.read_text(encoding="utf-8")
    except OSError as exc:
        return f"Failed to read .pddrc: {exc}"


def _gh_api(args: List[str]) -> Tuple[bool, str, str]:
    """Run ``gh api ARGS`` and return (success, stdout, stderr)."""
    try:
        result = subprocess.run(
            ["gh", "api", *args],
            capture_output=True,
            text=True,
            check=False,
        )
        return result.returncode == 0, result.stdout or "", result.stderr or ""
    except FileNotFoundError:
        return False, "", "gh CLI not found"
    except OSError as exc:
        return False, "", str(exc)


def _fetch_comments(comments_url: str) -> str:
    """Fetch and format issue comments for context."""
    if not comments_url:
        return "No comments URL available."

    # gh api accepts either the path portion or the full URL.
    success, stdout, stderr = _gh_api([comments_url])
    if not success:
        return f"Failed to fetch comments: {stderr.strip() or 'unknown error'}"

    try:
        comments = json.loads(stdout)
    except (json.JSONDecodeError, ValueError):
        return "Failed to parse issue comments JSON."

    if not isinstance(comments, list) or not comments:
        return "No comments on this issue."

    formatted: List[str] = []
    for idx, comment in enumerate(comments, start=1):
        if not isinstance(comment, dict):
            continue
        author = (comment.get("user") or {}).get("login", "unknown")
        created = comment.get("created_at", "")
        body = comment.get("body", "") or ""
        formatted.append(
            f"--- Comment #{idx} by @{author} at {created} ---\n{body}"
        )
    return "\n\n".join(formatted) if formatted else "No comments on this issue."


def _fetch_pr_context(owner: str, repo: str, pr_number: int) -> str:
    """Fetch and format PR metadata, files, comments, and reviews."""
    sections: List[str] = []

    # 1) PR metadata.
    pr_path = f"repos/{owner}/{repo}/pulls/{pr_number}"
    success, stdout, stderr = _gh_api([pr_path])
    if not success:
        return f"Failed to fetch PR metadata: {stderr.strip() or 'unknown error'}"
    try:
        pr = json.loads(stdout)
    except (json.JSONDecodeError, ValueError):
        return "Failed to parse PR metadata JSON."

    title = pr.get("title", "") or ""
    state = pr.get("state", "") or ""
    draft = pr.get("draft", False)
    base = ((pr.get("base") or {}).get("ref")) or "?"
    head_obj = pr.get("head") or {}
    head_ref = head_obj.get("ref") or "?"
    head_repo = (head_obj.get("repo") or {}).get("full_name") or f"{owner}/{repo}"
    body = _truncate(pr.get("body", "") or "", _PR_BODY_LIMIT, label="PR body")
    author = (pr.get("user") or {}).get("login", "unknown")

    sections.append(
        "## PR Metadata\n"
        f"- Title: {title}\n"
        f"- Number: #{pr_number}\n"
        f"- State: {state}{' (draft)' if draft else ''}\n"
        f"- Author: @{author}\n"
        f"- Base: {base}\n"
        f"- Head: {head_repo}:{head_ref}\n\n"
        f"### PR Body\n{body or '(empty)'}"
    )

    # 2) Changed files with bounded patch excerpts.
    files_path = f"repos/{owner}/{repo}/pulls/{pr_number}/files?per_page=100"
    success, stdout, stderr = _gh_api([files_path])
    if not success:
        sections.append(
            "## Changed Files\n"
            f"(Failed to fetch file list: {stderr.strip() or 'unknown error'})"
        )
    else:
        try:
            files = json.loads(stdout)
        except (json.JSONDecodeError, ValueError):
            files = []
        if not isinstance(files, list) or not files:
            sections.append("## Changed Files\nNo file changes reported.")
        else:
            file_lines: List[str] = ["## Changed Files"]
            patch_budget = _PR_PATCH_TOTAL_LIMIT
            for entry in files:
                if not isinstance(entry, dict):
                    continue
                fname = entry.get("filename", "?")
                status = entry.get("status", "?")
                additions = entry.get("additions", 0)
                deletions = entry.get("deletions", 0)
                file_lines.append(
                    f"\n### {fname} ({status}, +{additions}/-{deletions})"
                )
                patch = entry.get("patch") or ""
                if not patch:
                    file_lines.append("(no patch text — likely binary or too large)")
                    continue
                if patch_budget <= 0:
                    file_lines.append("(patch omitted — total patch budget exhausted)")
                    continue
                excerpt_limit = min(_PR_PATCH_PER_FILE_LIMIT, patch_budget)
                excerpt = _truncate(patch, excerpt_limit, label="patch")
                patch_budget -= len(excerpt)
                file_lines.append("```diff\n" + excerpt + "\n```")
            sections.append("\n".join(file_lines))

    # 3) PR conversation comments (issue-style on the PR).
    comments_path = f"repos/{owner}/{repo}/issues/{pr_number}/comments?per_page=100"
    success, stdout, stderr = _gh_api([comments_path])
    if success:
        try:
            comments = json.loads(stdout)
        except (json.JSONDecodeError, ValueError):
            comments = []
        if isinstance(comments, list) and comments:
            chunks: List[str] = ["## PR Conversation Comments"]
            for idx, comment in enumerate(comments, start=1):
                if not isinstance(comment, dict):
                    continue
                a = (comment.get("user") or {}).get("login", "unknown")
                created = comment.get("created_at", "")
                body_text = comment.get("body", "") or ""
                chunks.append(f"\n--- Comment #{idx} by @{a} at {created} ---\n{body_text}")
            sections.append(_truncate("\n".join(chunks), _PR_COMMENT_LIMIT, label="PR comments"))
        else:
            sections.append("## PR Conversation Comments\n(none)")
    else:
        sections.append(
            "## PR Conversation Comments\n"
            f"(Failed to fetch: {stderr.strip() or 'unknown error'})"
        )

    # 4) Submitted PR reviews.
    reviews_path = f"repos/{owner}/{repo}/pulls/{pr_number}/reviews?per_page=100"
    success, stdout, stderr = _gh_api([reviews_path])
    if success:
        try:
            reviews = json.loads(stdout)
        except (json.JSONDecodeError, ValueError):
            reviews = []
        if isinstance(reviews, list) and reviews:
            chunks = ["## Submitted PR Reviews"]
            for idx, review in enumerate(reviews, start=1):
                if not isinstance(review, dict):
                    continue
                a = (review.get("user") or {}).get("login", "unknown")
                rstate = review.get("state", "")
                submitted = review.get("submitted_at", "")
                body_text = review.get("body", "") or ""
                chunks.append(
                    f"\n--- Review #{idx} by @{a} ({rstate}) at {submitted} ---\n"
                    f"{body_text or '(no body)'}"
                )
            sections.append(_truncate("\n".join(chunks), _PR_REVIEWS_LIMIT, label="PR reviews"))
        else:
            sections.append("## Submitted PR Reviews\n(none)")
    else:
        sections.append(
            "## Submitted PR Reviews\n"
            f"(Failed to fetch: {stderr.strip() or 'unknown error'})"
        )

    return "\n\n".join(sections)


def _post_checkup_comment(
    owner: str,
    repo: str,
    issue_number: int,
    report: Dict[str, Any],
) -> None:
    """Post a structured checkup result comment on the GitHub issue."""
    lines: List[str] = ["## ⚕️ Agentic Checkup Report", ""]
    summary = report.get("summary") or report.get("message") or ""
    if summary:
        lines.append(str(summary))
        lines.append("")

    issues = report.get("issues") or []
    if isinstance(issues, list) and issues:
        lines.append("### Findings")
        lines.append("")
        lines.append("| # | Severity | Area | Description |")
        lines.append("|---|----------|------|-------------|")
        for idx, issue in enumerate(issues, start=1):
            if not isinstance(issue, dict):
                continue
            sev = str(issue.get("severity", "?")).replace("|", "\\|")
            area = str(issue.get("area", "?")).replace("|", "\\|")
            desc = str(issue.get("description", "")).replace("|", "\\|").replace("\n", " ")
            lines.append(f"| {idx} | {sev} | {area} | {desc} |")
        lines.append("")
    else:
        lines.append("_No issues reported._")
        lines.append("")

    body = "\n".join(lines)
    try:
        subprocess.run(
            [
                "gh",
                "api",
                f"repos/{owner}/{repo}/issues/{issue_number}/comments",
                "-f",
                f"body={body}",
            ],
            capture_output=True,
            text=True,
            check=False,
        )
    except (FileNotFoundError, OSError) as exc:
        console.print(f"[yellow]Failed to post checkup comment: {exc}[/yellow]")


def _post_error_comment(
    owner: str,
    repo: str,
    issue_number: int,
    message: str,
) -> None:
    """Post an error message as a GitHub issue comment."""
    body = f"## ❌ Agentic Checkup Failed\n\n{message}"
    try:
        subprocess.run(
            [
                "gh",
                "api",
                f"repos/{owner}/{repo}/issues/{issue_number}/comments",
                "-f",
                f"body={body}",
            ],
            capture_output=True,
            text=True,
            check=False,
        )
    except (FileNotFoundError, OSError) as exc:
        console.print(f"[yellow]Failed to post error comment: {exc}[/yellow]")


def _split_csv(value: Optional[str]) -> Optional[Tuple[str, ...]]:
    """Parse a comma-separated string into a tuple of trimmed tokens."""
    if value is None:
        return None
    parts = [tok.strip() for tok in value.split(",") if tok.strip()]
    return tuple(parts) if parts else None


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
    reviewer_fallback: bool = True,
) -> Tuple[bool, str, float, str]:
    """Entry point for the agentic checkup workflow.

    Fetches the issue (and optional PR) context, loads architecture/.pddrc,
    then dispatches either to the multi-step orchestrator or — when
    ``review_loop=True`` — to the primary-reviewer/fixer review loop.

    Returns:
        Tuple of (success, message, total_cost, model_used).
    """
    # 1) gh CLI availability.
    if not _check_gh_cli():
        msg = (
            "GitHub CLI (gh) not found. Install it from https://cli.github.com/ "
            "and authenticate with `gh auth login`."
        )
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, ""

    # 2) Parse issue URL.
    parsed = _parse_issue_url(issue_url)
    if not parsed:
        msg = f"Invalid GitHub issue URL: {issue_url}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, ""
    repo_owner, repo_name, issue_number = parsed

    # 3) Optional PR URL parsing.
    pr_owner: Optional[str] = None
    pr_repo: Optional[str] = None
    pr_number: Optional[int] = None
    if pr_url:
        pr_parsed = _parse_pr_url(pr_url)
        if not pr_parsed:
            msg = f"Invalid GitHub PR URL: {pr_url}"
            if not quiet:
                console.print(f"[red]{msg}[/red]")
            return False, msg, 0.0, ""
        pr_owner, pr_repo, pr_number = pr_parsed

    # 4) Fetch issue.
    issue_path = f"repos/{repo_owner}/{repo_name}/issues/{issue_number}"
    success, stdout, stderr = _gh_api([issue_path])
    if not success:
        msg = f"Failed to fetch issue: {stderr.strip() or 'unknown error'}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, ""

    try:
        issue_data = json.loads(stdout)
    except (json.JSONDecodeError, ValueError):
        msg = "Failed to parse issue JSON"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        return False, msg, 0.0, ""

    issue_title = issue_data.get("title", "") or ""
    issue_body = issue_data.get("body", "") or ""
    comments_url = issue_data.get("comments_url", "") or ""

    # 5) Fetch comments (best-effort).
    comments_text = _fetch_comments(comments_url)

    # 6) Compose raw issue context (unescaped — used by review loop directly).
    raw_issue_content = (
        f"# Issue #{issue_number}: {issue_title}\n\n"
        f"## Body\n{issue_body or '(no body)'}\n\n"
        f"## Comments\n{comments_text}"
    )

    # 7) Project context.
    project_root = find_project_root()
    pddrc_content_raw = _load_pddrc_content(project_root)

    arch_data, _arch_path = _load_architecture_json(project_root, issue_number=issue_number)
    if arch_data is None:
        architecture_json_raw = "[]"
    else:
        try:
            architecture_json_raw = json.dumps(arch_data, indent=2, default=str)
        except (TypeError, ValueError):
            architecture_json_raw = "[]"

    # 8) Review-loop dispatch.
    if review_loop:
        if pr_owner is None or pr_repo is None or pr_number is None or not pr_url:
            msg = "review_loop requires --pr-url to point at an existing pull request."
            if not quiet:
                console.print(f"[red]{msg}[/red]")
            return False, msg, 0.0, ""

        # Function-scope import to avoid hard dependency at module load time.
        try:
            from .checkup_review_loop import (
                ReviewLoopConfig,
                ReviewLoopContext,
                run_checkup_review_loop,
            )
        except ImportError as exc:
            msg = f"Review-loop dependencies unavailable: {exc}"
            if not quiet:
                console.print(f"[red]{msg}[/red]")
            return False, msg, 0.0, ""

        # Fetch PR context (bounded).
        pr_context_raw = _fetch_pr_context(pr_owner, pr_repo, pr_number)

        # Truncate everything before handing to the loop. The loop's prompt
        # is an f-string, so we do NOT escape braces here.
        issue_content_for_loop = _truncate(
            raw_issue_content, _REVIEW_LOOP_ISSUE_LIMIT + _REVIEW_LOOP_COMMENTS_LIMIT,
            label="issue+comments",
        )
        pr_content_for_loop = _truncate(
            pr_context_raw, _REVIEW_LOOP_PR_LIMIT, label="PR context",
        )
        pddrc_for_loop = _truncate(
            pddrc_content_raw, _REVIEW_LOOP_PDDRC_LIMIT, label=".pddrc",
        )
        arch_for_loop = _truncate(
            architecture_json_raw, _REVIEW_LOOP_ARCH_LIMIT, label="architecture.json",
        )

        # Build config — pass None through where caller didn't customize so
        # the dataclass defaults take effect.
        reviewers_tuple = _split_csv(reviewers)
        blocking_tuple = _split_csv(blocking_severities)
        clean_states_tuple = _split_csv(clean_reviewer_states)

        config_kwargs: Dict[str, Any] = {
            "review_only": review_only,
            "max_rounds": max_review_rounds,
            "max_cost": max_review_cost,
            "max_minutes": max_review_minutes,
            "require_all_reviewers_clean": require_all_reviewers_clean,
            "continue_on_reviewer_limit": continue_on_reviewer_limit,
            "require_final_fresh_review": require_final_fresh_review,
            "timeout_adder": timeout_adder,
            "reasoning_time": reasoning_time,
            "reviewer_fallback": reviewer_fallback,
        }
        if reviewers_tuple is not None:
            config_kwargs["reviewers"] = reviewers_tuple
        if reviewer is not None:
            config_kwargs["reviewer"] = reviewer
        if fixer is not None:
            config_kwargs["fixer"] = fixer
        if blocking_tuple is not None:
            config_kwargs["blocking_severities"] = blocking_tuple
        if clean_states_tuple is not None:
            config_kwargs["clean_reviewer_states"] = clean_states_tuple

        loop_config = ReviewLoopConfig(**config_kwargs)
        loop_context = ReviewLoopContext(
            issue_url=issue_url,
            issue_content=issue_content_for_loop,
            repo_owner=repo_owner,
            repo_name=repo_name,
            issue_number=issue_number,
            issue_title=issue_title,
            architecture_json=arch_for_loop,
            pddrc_content=pddrc_for_loop,
            pr_url=pr_url,
            pr_owner=pr_owner,
            pr_repo=pr_repo,
            pr_number=pr_number,
            project_root=project_root,
            pr_content=pr_content_for_loop,
        )

        try:
            return run_checkup_review_loop(
                context=loop_context,
                config=loop_config,
                cwd=project_root,
                verbose=verbose,
                quiet=quiet,
                use_github_state=use_github_state,
            )
        except Exception as exc:  # pragma: no cover - defensive
            err_msg = f"Review loop crashed: {exc}"
            if not quiet:
                console.print(f"[red]{err_msg}[/red]")
            try:
                _post_error_comment(repo_owner, repo_name, issue_number, err_msg)
            except Exception:  # noqa: BLE001
                pass
            return False, err_msg, 0.0, ""

    # 9) Legacy orchestrator dispatch — escape braces for .format() safety.
    issue_content_for_orchestrator = _escape_format_braces(raw_issue_content)
    pddrc_for_orchestrator = _escape_format_braces(pddrc_content_raw)
    architecture_for_orchestrator = _escape_format_braces(architecture_json_raw)

    try:
        return run_agentic_checkup_orchestrator(
            issue_url=issue_url,
            issue_content=issue_content_for_orchestrator,
            repo_owner=repo_owner,
            repo_name=repo_name,
            issue_number=issue_number,
            issue_title=issue_title,
            architecture_json=architecture_for_orchestrator,
            pddrc_content=pddrc_for_orchestrator,
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
    except Exception as exc:  # noqa: BLE001
        err_msg = f"Agentic checkup orchestrator failed: {exc}"
        if not quiet:
            console.print(f"[red]{err_msg}[/red]")
        try:
            _post_error_comment(repo_owner, repo_name, issue_number, err_msg)
        except Exception:  # noqa: BLE001
            pass
        return False, err_msg, 0.0, ""