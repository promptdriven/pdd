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
from .checkup_review_loop import (
    ReviewLoopConfig,
    ReviewLoopContext,
    run_checkup_review_loop,
)

console = Console()

# Truncation budgets for review-loop context (characters).
_MAX_ISSUE_CONTENT_CHARS = 20_000
_MAX_PR_CONTEXT_CHARS = 40_000
_MAX_PDDRC_CHARS = 8_000
_MAX_ARCH_CHARS = 30_000
_MAX_COMMENTS_CHARS = 20_000
_MAX_PATCH_EXCERPT_CHARS = 1_500
_MAX_PR_FILES = 50
_MAX_PR_COMMENTS = 30
_MAX_PR_REVIEWS = 30


def _truncate(text: str, limit: int, label: str = "") -> str:
    """Truncate ``text`` to ``limit`` characters with a marker."""
    if len(text) <= limit:
        return text
    suffix = f"\n\n... [truncated {len(text) - limit} chars" + (
        f" of {label}" if label else ""
    ) + "]"
    return text[:limit] + suffix


def _extract_json_from_text(text: str) -> Optional[Dict[str, Any]]:
    """Extract JSON object from text — try fenced code blocks then raw."""
    if not text:
        return None

    # Try fenced ```json ... ``` blocks first.
    fence_pattern = re.compile(
        r"```(?:json)?\s*(\{.*?\})\s*```", re.DOTALL | re.IGNORECASE
    )
    for match in fence_pattern.finditer(text):
        candidate = match.group(1)
        try:
            obj = json.loads(candidate)
            if isinstance(obj, dict):
                return obj
        except (json.JSONDecodeError, ValueError):
            continue

    # Try raw JSON object — find first { and last }.
    first = text.find("{")
    last = text.rfind("}")
    if first != -1 and last != -1 and last > first:
        candidate = text[first : last + 1]
        try:
            obj = json.loads(candidate)
            if isinstance(obj, dict):
                return obj
        except (json.JSONDecodeError, ValueError):
            pass

    return None


def _load_pddrc_content(project_root: Path) -> str:
    """Load .pddrc content from project root, return placeholder if missing."""
    pddrc_path = project_root / ".pddrc"
    if not pddrc_path.exists():
        return "No .pddrc found."
    try:
        return pddrc_path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        return f"Failed to read .pddrc: {exc}"


def _gh_api(args: List[str]) -> Tuple[bool, str, str]:
    """Run a `gh api` command. Returns (success, stdout, stderr)."""
    try:
        result = subprocess.run(
            ["gh", "api"] + args,
            capture_output=True,
            text=True,
            check=False,
            timeout=120,
        )
        return result.returncode == 0, result.stdout, result.stderr
    except (subprocess.TimeoutExpired, OSError) as exc:
        return False, "", str(exc)


def _fetch_comments(comments_url: str) -> str:
    """Fetch and format issue comments from a comments URL."""
    if not comments_url:
        return "No comments."

    # Convert API URL to gh api path. comments_url usually looks like:
    # https://api.github.com/repos/{owner}/{repo}/issues/{n}/comments
    path = comments_url
    prefix = "https://api.github.com/"
    if path.startswith(prefix):
        path = path[len(prefix):]

    ok, stdout, stderr = _gh_api([path, "--paginate"])
    if not ok:
        return f"Failed to fetch comments: {stderr.strip()}"

    try:
        comments = json.loads(stdout) if stdout.strip() else []
    except (json.JSONDecodeError, ValueError):
        return "Failed to parse comments JSON."

    if not isinstance(comments, list) or not comments:
        return "No comments."

    parts: List[str] = []
    for c in comments:
        if not isinstance(c, dict):
            continue
        user = (c.get("user") or {}).get("login", "unknown")
        created = c.get("created_at", "")
        body = c.get("body", "") or ""
        parts.append(f"--- @{user} ({created}) ---\n{body}")

    return "\n\n".join(parts) if parts else "No comments."


def _fetch_pr_context(owner: str, repo: str, pr_number: int) -> str:
    """Fetch PR metadata, files, comments, reviews and format as text."""
    sections: List[str] = []

    # 1. PR metadata.
    ok, stdout, stderr = _gh_api([f"repos/{owner}/{repo}/pulls/{pr_number}"])
    if not ok:
        return f"Failed to fetch PR #{pr_number}: {stderr.strip()}"
    try:
        pr = json.loads(stdout)
    except (json.JSONDecodeError, ValueError):
        return f"Failed to parse PR #{pr_number} JSON."

    title = pr.get("title", "")
    body = pr.get("body", "") or ""
    state = pr.get("state", "")
    base_ref = (pr.get("base") or {}).get("ref", "")
    head_ref = (pr.get("head") or {}).get("ref", "")
    head_sha = (pr.get("head") or {}).get("sha", "")
    author = (pr.get("user") or {}).get("login", "")
    draft = pr.get("draft", False)
    merged = pr.get("merged", False)

    sections.append(
        "## PR Metadata\n"
        f"- Number: #{pr_number}\n"
        f"- Title: {title}\n"
        f"- Author: @{author}\n"
        f"- State: {state} (draft={draft}, merged={merged})\n"
        f"- Base: {base_ref}\n"
        f"- Head: {head_ref} @ {head_sha}\n\n"
        "### Body\n"
        f"{body}".rstrip()
    )

    # 2. Changed files (with patch excerpts).
    ok, stdout, stderr = _gh_api(
        [f"repos/{owner}/{repo}/pulls/{pr_number}/files", "--paginate"]
    )
    files_section = "## Changed Files\n"
    if not ok:
        files_section += f"Failed to fetch files: {stderr.strip()}"
    else:
        try:
            files = json.loads(stdout) if stdout.strip() else []
        except (json.JSONDecodeError, ValueError):
            files = []
        if not isinstance(files, list) or not files:
            files_section += "No changed files."
        else:
            file_parts: List[str] = []
            total = len(files)
            for f in files[:_MAX_PR_FILES]:
                if not isinstance(f, dict):
                    continue
                fname = f.get("filename", "")
                status = f.get("status", "")
                additions = f.get("additions", 0)
                deletions = f.get("deletions", 0)
                patch = f.get("patch", "") or ""
                patch_excerpt = _truncate(patch, _MAX_PATCH_EXCERPT_CHARS, "patch")
                file_parts.append(
                    f"### {fname} ({status}, +{additions}/-{deletions})\n"
                    f"```diff\n{patch_excerpt}\n```"
                )
            if total > _MAX_PR_FILES:
                file_parts.append(
                    f"\n... [{total - _MAX_PR_FILES} more file(s) omitted]"
                )
            files_section += "\n\n".join(file_parts)
    sections.append(files_section)

    # 3. PR conversation comments.
    ok, stdout, stderr = _gh_api(
        [f"repos/{owner}/{repo}/issues/{pr_number}/comments", "--paginate"]
    )
    comments_section = "## PR Comments\n"
    if not ok:
        comments_section += f"Failed to fetch PR comments: {stderr.strip()}"
    else:
        try:
            comments = json.loads(stdout) if stdout.strip() else []
        except (json.JSONDecodeError, ValueError):
            comments = []
        if not isinstance(comments, list) or not comments:
            comments_section += "No PR comments."
        else:
            cparts: List[str] = []
            for c in comments[:_MAX_PR_COMMENTS]:
                if not isinstance(c, dict):
                    continue
                user = (c.get("user") or {}).get("login", "unknown")
                created = c.get("created_at", "")
                cbody = c.get("body", "") or ""
                cparts.append(f"--- @{user} ({created}) ---\n{cbody}")
            if len(comments) > _MAX_PR_COMMENTS:
                cparts.append(
                    f"\n... [{len(comments) - _MAX_PR_COMMENTS} more comment(s) omitted]"
                )
            comments_section += "\n\n".join(cparts)
    sections.append(comments_section)

    # 4. PR reviews.
    ok, stdout, stderr = _gh_api(
        [f"repos/{owner}/{repo}/pulls/{pr_number}/reviews", "--paginate"]
    )
    reviews_section = "## PR Reviews\n"
    if not ok:
        reviews_section += f"Failed to fetch PR reviews: {stderr.strip()}"
    else:
        try:
            reviews = json.loads(stdout) if stdout.strip() else []
        except (json.JSONDecodeError, ValueError):
            reviews = []
        if not isinstance(reviews, list) or not reviews:
            reviews_section += "No reviews submitted."
        else:
            rparts: List[str] = []
            for r in reviews[:_MAX_PR_REVIEWS]:
                if not isinstance(r, dict):
                    continue
                user = (r.get("user") or {}).get("login", "unknown")
                rstate = r.get("state", "")
                submitted = r.get("submitted_at", "")
                rbody = r.get("body", "") or ""
                rparts.append(
                    f"--- @{user} [{rstate}] ({submitted}) ---\n{rbody}"
                )
            if len(reviews) > _MAX_PR_REVIEWS:
                rparts.append(
                    f"\n... [{len(reviews) - _MAX_PR_REVIEWS} more review(s) omitted]"
                )
            reviews_section += "\n\n".join(rparts)
    sections.append(reviews_section)

    full = "\n\n".join(sections)
    return _truncate(full, _MAX_PR_CONTEXT_CHARS, "PR context")


def _fetch_pr_metadata_struct(
    owner: str, repo: str, pr_number: int
) -> Optional[Dict[str, Any]]:
    """Fetch raw PR JSON for ReviewLoopContext fields."""
    ok, stdout, _stderr = _gh_api([f"repos/{owner}/{repo}/pulls/{pr_number}"])
    if not ok:
        return None
    try:
        data = json.loads(stdout)
        if isinstance(data, dict):
            return data
    except (json.JSONDecodeError, ValueError):
        pass
    return None


def _fetch_pr_files_list(
    owner: str, repo: str, pr_number: int
) -> Tuple[str, ...]:
    """Fetch list of changed filenames."""
    ok, stdout, _stderr = _gh_api(
        [f"repos/{owner}/{repo}/pulls/{pr_number}/files", "--paginate"]
    )
    if not ok:
        return ()
    try:
        files = json.loads(stdout) if stdout.strip() else []
    except (json.JSONDecodeError, ValueError):
        return ()
    if not isinstance(files, list):
        return ()
    names: List[str] = []
    for f in files:
        if isinstance(f, dict) and f.get("filename"):
            names.append(f["filename"])
    return tuple(names)


def _fetch_pr_comments_list(
    owner: str, repo: str, pr_number: int
) -> Tuple[Dict[str, Any], ...]:
    ok, stdout, _stderr = _gh_api(
        [f"repos/{owner}/{repo}/issues/{pr_number}/comments", "--paginate"]
    )
    if not ok:
        return ()
    try:
        items = json.loads(stdout) if stdout.strip() else []
    except (json.JSONDecodeError, ValueError):
        return ()
    if not isinstance(items, list):
        return ()
    return tuple(c for c in items if isinstance(c, dict))


def _fetch_pr_reviews_list(
    owner: str, repo: str, pr_number: int
) -> Tuple[Dict[str, Any], ...]:
    ok, stdout, _stderr = _gh_api(
        [f"repos/{owner}/{repo}/pulls/{pr_number}/reviews", "--paginate"]
    )
    if not ok:
        return ()
    try:
        items = json.loads(stdout) if stdout.strip() else []
    except (json.JSONDecodeError, ValueError):
        return ()
    if not isinstance(items, list):
        return ()
    return tuple(r for r in items if isinstance(r, dict))


def _post_checkup_comment(
    owner: str, repo: str, issue_number: int, report: Dict[str, Any]
) -> None:
    """Post a structured checkup report as a GitHub issue comment."""
    try:
        lines: List[str] = ["## ⚕ Checkup Report\n"]
        summary = report.get("summary", "")
        if summary:
            lines.append(f"**Summary:** {summary}\n")

        issues = report.get("issues") or []
        if isinstance(issues, list) and issues:
            lines.append("\n### Issues Found\n")
            lines.append("| # | Severity | Area | Description |")
            lines.append("|---|----------|------|-------------|")
            for i, issue in enumerate(issues, 1):
                if not isinstance(issue, dict):
                    continue
                sev = str(issue.get("severity", "")).replace("|", "\\|")
                area = str(issue.get("area", "")).replace("|", "\\|")
                desc = str(issue.get("description", "")).replace("|", "\\|").replace(
                    "\n", " "
                )
                lines.append(f"| {i} | {sev} | {area} | {desc} |")
        else:
            lines.append("\n_No issues found._\n")

        cost = report.get("total_cost")
        if cost is not None:
            try:
                lines.append(f"\n**Total cost:** ${float(cost):.4f}")
            except (TypeError, ValueError):
                pass

        body = "\n".join(lines)
        subprocess.run(
            [
                "gh", "api",
                f"repos/{owner}/{repo}/issues/{issue_number}/comments",
                "-f", f"body={body}",
            ],
            capture_output=True,
            text=True,
            check=False,
            timeout=60,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        console.print(f"[yellow]Failed to post checkup comment: {exc}[/yellow]")


def _post_error_comment(
    owner: str, repo: str, issue_number: int, message: str
) -> None:
    """Post an error message as a GitHub issue comment."""
    try:
        body = f"## ❌ Checkup Error\n\n{message}"
        subprocess.run(
            [
                "gh", "api",
                f"repos/{owner}/{repo}/issues/{issue_number}/comments",
                "-f", f"body={body}",
            ],
            capture_output=True,
            text=True,
            check=False,
            timeout=60,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        console.print(f"[yellow]Failed to post error comment: {exc}[/yellow]")


def _parse_csv(value: Optional[str]) -> Tuple[str, ...]:
    """Parse a comma-separated string into a tuple of trimmed non-empty parts."""
    if not value:
        return ()
    return tuple(p.strip() for p in value.split(",") if p.strip())


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
    """Entry point for the agentic checkup workflow."""

    # 1. gh CLI availability.
    if not _check_gh_cli():
        return (
            False,
            "GitHub CLI (gh) not found. Please install gh and authenticate "
            "with 'gh auth login'.",
            0.0,
            "",
        )

    # 2. Parse issue URL.
    parsed = _parse_issue_url(issue_url)
    if parsed is None:
        return (False, f"Invalid GitHub issue URL: {issue_url}", 0.0, "")
    repo_owner, repo_name, issue_number = parsed

    # 3. PR mode parsing.
    pr_owner: Optional[str] = None
    pr_repo: Optional[str] = None
    pr_number: Optional[int] = None
    if pr_url:
        pr_parsed = _parse_pr_url(pr_url)
        if pr_parsed is None:
            return (False, f"Invalid GitHub PR URL: {pr_url}", 0.0, "")
        pr_owner, pr_repo, pr_number = pr_parsed

    # 4. Review-loop precondition: requires PR mode.
    if review_loop and pr_number is None:
        return (
            False,
            "--review-loop requires --pr-url (PR-mode is mandatory for the "
            "review loop).",
            0.0,
            "",
        )

    # 5. Fetch issue content.
    if not quiet:
        console.print(
            f"[blue]Fetching issue #{issue_number} from {repo_owner}/{repo_name}...[/blue]"
        )
    ok, stdout, stderr = _gh_api(
        [f"repos/{repo_owner}/{repo_name}/issues/{issue_number}"]
    )
    if not ok:
        return (False, f"Failed to fetch issue: {stderr.strip()}", 0.0, "")

    try:
        issue_data = json.loads(stdout)
    except (json.JSONDecodeError, ValueError):
        return (False, "Failed to parse issue JSON", 0.0, "")

    issue_title = issue_data.get("title", "") or ""
    issue_body = issue_data.get("body", "") or ""
    comments_url = issue_data.get("comments_url", "") or ""

    # 6. Fetch comments.
    comments_text = _fetch_comments(comments_url)

    # 7. Build raw issue content (title + body + comments).
    issue_content_raw = (
        f"# {issue_title}\n\n"
        f"{issue_body}\n\n"
        f"## Comments\n\n{comments_text}"
    )

    # 8. Find project root and load architecture + .pddrc.
    project_root = find_project_root()
    arch_data, _arch_path = _load_architecture_json(project_root, issue_number)
    if arch_data is None:
        architecture_json_raw = "[]"
    else:
        try:
            architecture_json_raw = json.dumps(arch_data, indent=2)
        except (TypeError, ValueError):
            architecture_json_raw = "[]"

    pddrc_content_raw = _load_pddrc_content(project_root)

    # ==================================================================
    # Review-loop dispatch
    # ==================================================================
    if review_loop:
        assert pr_owner is not None and pr_repo is not None and pr_number is not None

        if not quiet:
            console.print(
                f"[blue]Fetching PR context for #{pr_number}...[/blue]"
            )

        pr_meta = _fetch_pr_metadata_struct(pr_owner, pr_repo, pr_number) or {}
        pr_files = _fetch_pr_files_list(pr_owner, pr_repo, pr_number)
        pr_comments_list = _fetch_pr_comments_list(pr_owner, pr_repo, pr_number)
        pr_reviews_list = _fetch_pr_reviews_list(pr_owner, pr_repo, pr_number)

        pr_context_text = _fetch_pr_context(pr_owner, pr_repo, pr_number)

        # Truncate raw fields for prompt budget. The review-loop prompt is an
        # f-string, not .format(), so we do NOT escape braces here.
        truncated_issue = _truncate(
            issue_content_raw, _MAX_ISSUE_CONTENT_CHARS, "issue content"
        )
        truncated_pr_ctx = _truncate(
            pr_context_text, _MAX_PR_CONTEXT_CHARS, "PR context"
        )
        truncated_pddrc = _truncate(
            pddrc_content_raw, _MAX_PDDRC_CHARS, ".pddrc"
        )
        truncated_arch = _truncate(
            architecture_json_raw, _MAX_ARCH_CHARS, "architecture.json"
        )

        extra_context = (
            f"## Issue #{issue_number}\n{truncated_issue}\n\n"
            f"## PR Context\n{truncated_pr_ctx}\n\n"
            f"## .pddrc\n{truncated_pddrc}"
        )

        rl_context = ReviewLoopContext(
            issue_number=issue_number,
            issue_url=issue_url,
            issue_title=issue_title,
            issue_body=_truncate(issue_body, _MAX_ISSUE_CONTENT_CHARS, "issue body"),
            pr_number=pr_number,
            pr_url=pr_url or "",
            pr_owner=pr_owner,
            pr_repo=pr_repo,
            pr_title=pr_meta.get("title", "") or "",
            pr_body=_truncate(pr_meta.get("body", "") or "", _MAX_ISSUE_CONTENT_CHARS, "PR body"),
            pr_head_ref=(pr_meta.get("head") or {}).get("ref", "") or "",
            pr_base_ref=(pr_meta.get("base") or {}).get("ref", "") or "",
            pr_changed_files=pr_files,
            pr_comments=pr_comments_list,
            pr_reviews=pr_reviews_list,
            repo_owner=repo_owner,
            repo_name=repo_name,
            architecture=truncated_arch,
            extra_context=extra_context,
        )

        rl_kwargs: Dict[str, Any] = {
            "reviewers": _parse_csv(reviewers),
            "reviewer": reviewer,
            "fixer": fixer,
            "review_only": review_only,
            "max_rounds": max_review_rounds,
            "max_cost": max_review_cost,
            "max_minutes": max_review_minutes,
            "require_all_reviewers_clean": require_all_reviewers_clean,
            "continue_on_reviewer_limit": continue_on_reviewer_limit,
            "require_final_fresh_review": require_final_fresh_review,
            "reviewer_fallback": reviewer_fallback,
            "timeout_adder": timeout_adder,
            "reasoning_time": reasoning_time,
        }
        blocking_tuple = _parse_csv(blocking_severities)
        if blocking_tuple:
            rl_kwargs["blocking_severities"] = blocking_tuple
        clean_tuple = _parse_csv(clean_reviewer_states)
        if clean_tuple:
            rl_kwargs["clean_reviewer_states"] = clean_tuple

        rl_config = ReviewLoopConfig(**rl_kwargs)

        try:
            return run_checkup_review_loop(
                context=rl_context,
                config=rl_config,
                cwd=project_root,
                verbose=verbose,
                quiet=quiet,
                use_github_state=use_github_state,
            )
        except Exception as exc:  # pylint: disable=broad-except
            err_msg = f"Review-loop failed: {exc}"
            if not quiet:
                console.print(f"[red]{err_msg}[/red]")
            if use_github_state:
                _post_error_comment(repo_owner, repo_name, issue_number, err_msg)
            return (False, err_msg, 0.0, "")

    # ==================================================================
    # Legacy orchestrator dispatch
    # ==================================================================
    issue_content = _escape_format_braces(issue_content_raw)
    architecture_json = _escape_format_braces(architecture_json_raw)
    pddrc_content = _escape_format_braces(pddrc_content_raw)

    try:
        return run_agentic_checkup_orchestrator(
            issue_url=issue_url,
            issue_content=issue_content,
            repo_owner=repo_owner,
            repo_name=repo_name,
            issue_number=issue_number,
            issue_title=issue_title,
            architecture_json=architecture_json,
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
    except Exception as exc:  # pylint: disable=broad-except
        err_msg = f"Checkup orchestrator failed: {exc}"
        if not quiet:
            console.print(f"[red]{err_msg}[/red]")
        if use_github_state:
            _post_error_comment(repo_owner, repo_name, issue_number, err_msg)
        return (False, err_msg, 0.0, "")
