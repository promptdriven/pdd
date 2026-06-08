"""
Agentic checkup: LLM-driven project health check from a GitHub issue.

Entry point for ``pdd checkup <github_issue_url>``. Fetches issue content, loads
project context (architecture.json, .pddrc), then dispatches the multi-step
orchestrator that explores the project, identifies problems, and optionally
fixes them — one step per LLM call for reliability.
"""
from __future__ import annotations

import json
import math
import re
from pathlib import Path
from typing import Any, Dict, Optional, Tuple, Union

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
    clear_final_state,
    load_final_state,
    parse_reviewers,
    parse_severity_list,
    parse_state_list,
    run_checkup_review_loop,
)
from .ci_validation import (
    _get_pr_head_sha as _get_ci_pr_head_sha,
    _poll_required_checks,
    _render_check_summary,
)
from .agentic_sync import _find_project_root, _load_architecture_json

console = Console()


def _extract_json_from_text(text: str) -> Optional[Dict[str, Any]]:
    """Extract the LAST top-level JSON object from agent output text.

    Matches the Step 7 prompt contract ("The JSON report MUST be the
    last output") so earlier intermediate-reasoning blocks never mask
    the final verdict. Handles fenced JSON, raw JSON, and the mixed
    case (fenced earlier blocks followed by an unfenced final verdict)
    uniformly — ``json.JSONDecoder.raw_decode`` ignores markdown fences
    and just looks for valid JSON starting at a ``{``.
    """
    if not text or not text.strip():
        return None

    decoder = json.JSONDecoder()
    last_match: Optional[Dict[str, Any]] = None
    search_from = 0
    while True:
        idx = text.find("{", search_from)
        if idx == -1:
            break
        try:
            obj, end = decoder.raw_decode(text, idx)
        except json.JSONDecodeError:
            search_from = idx + 1
            continue
        if isinstance(obj, dict):
            last_match = obj
        search_from = end if end > idx else idx + 1
    return last_match


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


# Reviewer statuses that count as "this reviewer accepted the PR". The hard
# not-clean states (failed/degraded/missing) must never satisfy the gate even
# if a caller widens ``clean_reviewer_states``; the final gate uses the strict
# "clean" sentinel to stay conservative (a false non-ship is recoverable by a
# re-run; a false ship is not).
_SHIP_REVIEWER_STATES = ("clean",)
_FULL_SUITE_SOURCES = {"local", "github-checks", "none"}
_FULL_SUITE_SOURCE_ALIASES = {
    "github": "github-checks",
    "github-actions": "github-checks",
    "checks": "github-checks",
    "off": "none",
    "disabled": "none",
    "no-gate": "none",
}


def _normalize_full_suite_source(value: str) -> str:
    raw = str(value or "local").strip().lower().replace("_", "-")
    normalized = _FULL_SUITE_SOURCE_ALIASES.get(raw, raw)
    if normalized not in _FULL_SUITE_SOURCES:
        raise ValueError(
            "full_suite_source must be one of: local, github-checks, none"
        )
    return normalized


def _review_loop_ship_verdict(
    final_state: Optional[Dict[str, Any]], *, has_issue: bool
) -> bool:
    """Derive a real ship/no-ship verdict from a review-loop ``final-state.json``.

    ``run_checkup_review_loop`` returns ``success=True`` whenever it produces a
    trustworthy report — even when findings remain — so the boolean alone is NOT
    a ship gate (the rendered report carries the authoritative markers). The
    canonical final gate (issue #1406) needs a true pass/fail, so this predicate
    replicates the canonical ship markers against the persisted verdict:

    - ``fresh_final_status == "clean"`` — the verifier's clean pass survived the
      stale-head re-check ``_finalize`` performs (issue #1088). A head that
      advanced after verification is downgraded to ``missing`` there, so this
      field already encodes "the clean verdict matches the current remote head".
    - the active reviewer's status is a hard ``clean`` (not failed/degraded/
      missing/findings).
    - no finding is still ``open``.
    - when an issue is in scope, the PR is reported as issue-aligned.

    Fails closed: a missing/unparsable state, or any unmet condition, returns
    ``False``. A false non-ship is recoverable by re-running; a false ship is
    not.
    """
    if not isinstance(final_state, dict):
        return False
    if final_state.get("fresh_final_status") != "clean":
        return False
    reviewer_status = final_state.get("reviewer_status")
    active = final_state.get("active_reviewer")
    # ``active_reviewer`` must be a real string key; a non-string (or empty)
    # value is a malformed verdict — fail closed instead of raising on the
    # unhashable ``dict.get`` lookup below.
    if not isinstance(reviewer_status, dict) or not isinstance(active, str) or not active:
        return False
    if reviewer_status.get(active) not in _SHIP_REVIEWER_STATES:
        return False
    # The canonical ``_write_final_state`` ALWAYS serializes ``findings`` as a
    # list of dicts (``ReviewFinding.to_dict()``) whose ``status`` is a non-empty
    # string ("open" while unresolved, "fixed" once resolved). The canonical
    # ship gate blocks on any ``open`` row, so we mirror that; a non-list value,
    # a non-dict entry, or a missing/non-string/empty ``status`` means the
    # verdict file is malformed or not from a real run — fail closed rather than
    # treat the absence of an ``open`` row as "no findings".
    findings = final_state.get("findings")
    if not isinstance(findings, list):
        return False
    for finding in findings:
        if not isinstance(finding, dict):
            return False
        status = finding.get("status")
        if not isinstance(status, str) or not status or status == "open":
            return False
    if has_issue and str(final_state.get("issue_aligned")).lower() != "true":
        return False
    return True


def run_agentic_checkup(
    issue_url: Optional[str] = None,
    *,
    verbose: bool = False,
    quiet: bool = False,
    no_fix: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True,
    reasoning_time: Optional[float] = None,
    pr_url: Optional[str] = None,
    test_scope: str = "full",
    full_suite_source: str = "local",
    review_loop: bool = False,
    final_gate: bool = False,
    review_only: bool = False,
    reviewers: str = "codex,claude",
    reviewer: Optional[str] = None,
    fixer: Optional[str] = None,
    reviewer_fallback: Optional[str] = None,
    fixer_fallback: Optional[str] = None,
    max_review_rounds: int = 5,
    max_review_cost: float = 50.0,
    max_review_minutes: float = 90.0,
    require_all_reviewers_clean: bool = True,
    continue_on_reviewer_limit: bool = False,
    require_final_fresh_review: bool = True,
    blocking_severities: Optional[str] = None,
    clean_reviewer_states: Optional[str] = None,
    fallback_reviewer_on_failure: bool = False,
    enable_gates: bool = True,
    gate_timeout: float = 60.0,
    gate_allow: Tuple[str, ...] = (),
    start_step_override: Optional[Union[int, float]] = None,
    cwd: Optional[Path] = None,
) -> Tuple[bool, str, float, str]:
    """Run agentic checkup workflow from a GitHub issue URL.

    Args:
        issue_url: GitHub issue URL describing what to check. Optional in PR
            mode (``pr_url`` set): when ``None``, the PR is reviewed on its
            own merits and the issue-alignment gate is skipped (#1292).
        verbose: Enable detailed logging.
        quiet: Suppress standard output.
        no_fix: Report only, don't apply fixes.
        timeout_adder: Additional seconds to add to each step timeout.
        use_github_state: Whether to persist state to GitHub comments.
        cwd: Project working directory to use when loading local context.
        pr_url: When set, review this existing PR instead of creating a new
            branch/PR. With ``issue_url`` provided, the PR is verified against
            that issue; with ``issue_url`` omitted (#1292), the PR is reviewed
            on its own merits. Step 8 (create_pr) is skipped and the worktree
            is based on the PR's head branch.
        review_loop: When true in PR mode, run the primary-reviewer/fixer
            loop instead of the legacy single-pass checkup path.
        final_gate: When true in PR mode (requires an issue), run the canonical
            two-layer final gate (issue #1406): Layer 1 is the PR-scoped checkup
            orchestrator (no new PR), Layer 2 is the primary-reviewer/fixer
            review loop on the resulting PR head. Unlike ``review_loop`` — whose
            success only means "trustworthy report produced" — the returned
            ``success`` is a real ship verdict derived from the review-loop's
            current-run ``final-state.json``. A Layer 1 failure short-circuits
            before Layer 2; either layer's failure fails the gate.
        full_suite_source: Final-gate full-suite evidence source. ``local`` keeps
            the original behavior and runs full local tests in Layer 1.
            ``github-checks`` uses targeted Layer 1 plus required GitHub checks.
            ``none`` uses targeted Layer 1 when no CI/full-suite source exists.
        review_only: When true with ``review_loop``, run only the primary
            reviewer first pass and do not invoke the fixer or push changes.
        reviewer_fallback: Optional secondary reviewer role to try once when
            the primary reviewer cannot complete.
        fixer_fallback: Optional secondary fixer role to try once when the
            primary fixer cannot address the reviewer's findings (e.g. a
            subscription-tier credential is exhausted). Must differ from
            both the primary fixer and the active reviewer.
        start_step_override: Optional recovery override for the legacy
            orchestrator resume point. Used to start from a later step when
            cached state already contains earlier step outputs.

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

    # 2. Parse PR URL up-front (when in PR mode) so an invalid PR fails before
    #    any issue work, and so a no-issue run can alias its comment/state
    #    thread to the PR (GitHub treats PRs as issues for the comments API).
    pr_owner: Optional[str] = None
    pr_repo: Optional[str] = None
    pr_number: Optional[int] = None
    if pr_url is not None:
        pr_parsed = _parse_pr_url(pr_url)
        if not pr_parsed:
            return False, f"Invalid GitHub PR URL: {pr_url}", 0.0, ""
        pr_owner, pr_repo, pr_number = pr_parsed

    # 3. Resolve the source issue. The issue is OPTIONAL in PR mode (#1292):
    #    with no issue the PR is reviewed on its own merits, the issue fetch
    #    is skipped, and the issue context stays empty (never the literal
    #    "None") so the step prompts do merit review.
    # None, "", whitespace, or null-like strings all mean merit-review mode,
    # matching the orchestrator's own has_issue derivation at line 1846.
    has_issue = bool((issue_url or "").strip()) and issue_url not in ("null", "None")
    if has_issue:
        parsed = _parse_issue_url(issue_url)
        if not parsed:
            return False, f"Invalid GitHub issue URL: {issue_url}", 0.0, ""

        owner, repo, issue_number = parsed

        if not quiet:
            console.print(
                f"[bold]Fetching issue #{issue_number} from {owner}/{repo}...[/bold]"
            )

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
        effective_issue_url = issue_url
    else:
        # No issue: the comment/state thread is the PR itself.
        if pr_url is None or pr_owner is None or pr_repo is None or pr_number is None:
            return (
                False,
                "No issue URL and no PR URL provided; nothing to check.",
                0.0,
                "",
            )
        owner, repo, issue_number = pr_owner, pr_repo, pr_number
        raw_title = ""
        raw_full_content = ""
        effective_issue_url = ""

    # Escape braces so .format() doesn't choke on user content
    title = _escape_format_braces(raw_title)
    full_content = _escape_format_braces(raw_full_content)

    # 4. Load project context
    project_root = _find_project_root(cwd if cwd is not None else Path.cwd())
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

    # Layer 2 (review-loop) runner, shared by ``--review-loop`` (Layer 2 only)
    # and the canonical ``--final-gate`` (Layer 1 then Layer 2). Defined as a
    # closure so it captures the already-fetched issue/PR context instead of
    # re-threading the full config surface. ``pr_content`` is fetched lazily by
    # default, but the final gate passes a pre-Layer-1 snapshot so Layer 2 does
    # not ingest Layer 1's own freshly-posted checkup report.
    def _run_review_loop_layer(
        pr_content: Optional[str] = None,
    ) -> Tuple[bool, str, float, str]:
        loop_context = ReviewLoopContext(
            issue_url=issue_url,
            issue_content=_truncate_issue_context(raw_full_content, 60000),
            repo_owner=owner,
            repo_name=repo,
            issue_number=issue_number,
            issue_title=raw_title,
            architecture_json=_truncate_context(raw_arch_json_str, 40000),
            pddrc_content=raw_pddrc_content,
            pr_url=pr_url,
            pr_owner=pr_owner,
            pr_repo=pr_repo,
            pr_number=pr_number,
            project_root=project_root,
            pr_content=(
                pr_content
                if pr_content is not None
                else _fetch_pr_context(pr_owner, pr_repo, pr_number)
            ),
        )
        loop_config = ReviewLoopConfig(
            reviewers=parse_reviewers(reviewers),
            reviewer=reviewer,
            fixer=fixer,
            reviewer_fallback=reviewer_fallback,
            fixer_fallback=fixer_fallback,
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
            fallback_reviewer_on_failure=fallback_reviewer_on_failure,
            enable_gates=enable_gates,
            gate_timeout=gate_timeout,
            gate_allow=tuple(gate_allow),
        )
        return run_checkup_review_loop(
            context=loop_context,
            config=loop_config,
            cwd=project_root,
            verbose=verbose,
            quiet=quiet,
            use_github_state=use_github_state,
        )

    pr_context_ready = (
        has_issue
        and pr_url is not None
        and pr_owner is not None
        and pr_repo is not None
        and pr_number is not None
    )

    if final_gate and not pr_context_ready:
        # The final gate is the two-layer PR-readiness path; it is issue-coupled
        # and PR-scoped, so it never runs in plain issue mode.
        return False, "--final-gate requires --pr and --issue.", 0.0, ""

    try:
        final_gate_full_suite_source = _normalize_full_suite_source(full_suite_source)
    except ValueError as exc:
        return False, str(exc), 0.0, ""

    if final_gate:
        # The CLI rejects these combinations, but ``run_agentic_checkup`` is the
        # real contract boundary (the e2e/pdd-issue path and pdd_cloud call it
        # directly). Enforce the same gate-owned-knobs rule here so a direct
        # caller cannot run a non-canonical "final gate" — e.g. Layer 1
        # inheriting ``no_fix`` or a resume override, Layer 2 running with the
        # deterministic gates disabled, or Layer 1 skipping the full suite — and
        # silently get a weaker verdict than the canonical gate promises.
        conflicts = [
            name
            for name, set_ in (
                ("no_fix", no_fix),
                ("review_only", review_only),
                ("review_loop", review_loop),
                ("start_step_override", start_step_override is not None),
                ("enable_gates=False (--no-gates)", not enable_gates),
                ("test_scope!=full (--test-scope targeted)", test_scope != "full"),
            )
            if set_
        ]
        if conflicts:
            return (
                False,
                (
                    "--final-gate cannot be combined with: "
                    f"{', '.join(conflicts)}; the gate owns the fix/review steps, "
                    "requires the deterministic gates and owns the full-suite "
                    "evidence source, "
                    "and runs the review-loop as Layer 2."
                ),
                0.0,
                "",
            )
        # The gate runs the review loop as Layer 2, so its budget knobs must be
        # valid BEFORE Layer 1 spends cost / mutates the PR — otherwise a direct
        # caller could push Layer-1 fixes and then have Layer 2 die via a runtime
        # cap (e.g. "Max review rounds reached: 0"). Mirror the CLI's checks.
        budget_errors = []
        # ``max_review_rounds`` is typed ``int`` but a direct library caller is
        # not bound by the hint: ``1.5``/``nan``/``inf`` all slip past a bare
        # ``< 1`` (and a float ``max_rounds`` later breaks ``range(1, n + 1)`` in
        # the loop). Require an actual positive integer — and reject ``bool``,
        # which is an ``int`` subclass — BEFORE Layer 1 spends cost / mutates.
        if (
            isinstance(max_review_rounds, bool)
            or not isinstance(max_review_rounds, int)
            or max_review_rounds < 1
        ):
            budget_errors.append("max_review_rounds must be a positive integer")
        if not math.isfinite(max_review_cost) or max_review_cost <= 0:
            budget_errors.append("max_review_cost must be a finite value > 0")
        if not math.isfinite(max_review_minutes) or max_review_minutes <= 0:
            budget_errors.append("max_review_minutes must be a finite value > 0")
        if budget_errors:
            return (
                False,
                f"--final-gate review budget invalid: {'; '.join(budget_errors)}.",
                0.0,
                "",
            )

    if review_loop and not final_gate:
        if not pr_context_ready:
            # Review-loop is issue-coupled; review-loop-without-issue is a
            # deferred follow-up (#1292).
            return False, "--review-loop requires --pr and --issue.", 0.0, ""
        return _run_review_loop_layer()

    # For the final gate, snapshot PR context BEFORE Layer 1 so Layer 2 reviews
    # the PR's human context without ingesting Layer 1's own posted report.
    final_gate_pr_content: Optional[str] = None
    if final_gate:
        final_gate_pr_content = _fetch_pr_context(pr_owner, pr_repo, pr_number)

    layer1_test_scope = test_scope
    if final_gate and final_gate_full_suite_source in {"github-checks", "none"}:
        layer1_test_scope = "targeted"

    # 5. Invoke orchestrator (Layer 1 of the final gate; the only layer for a
    #    plain checkup run).
    try:
        orch_success, orch_message, orch_cost, orch_model = run_agentic_checkup_orchestrator(
            issue_url=effective_issue_url,
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
            test_scope=layer1_test_scope,
            start_step_override=start_step_override,
            suppress_progress_comments=final_gate,
        )
    except Exception as exc:
        msg = f"Orchestrator failed: {exc}"
        if not quiet:
            console.print(f"[red]{msg}[/red]")
        _post_error_comment(owner, repo, issue_number, msg)
        return False, msg, 0.0, ""

    if not orch_success:
        # Layer 1 failure short-circuits the final gate before Layer 2 runs.
        return False, orch_message, orch_cost, orch_model

    if final_gate:
        if final_gate_full_suite_source == "github-checks":
            assert pr_owner is not None and pr_repo is not None and pr_number is not None
            checked_head_sha = _get_ci_pr_head_sha(
                pr_owner, pr_repo, pr_number, project_root
            )
            if not checked_head_sha:
                return (
                    False,
                    (
                        "Final gate Layer 1 targeted PR checkup passed, but "
                        "the GitHub-checks full-suite source could not read the "
                        "current PR head SHA.\n\n"
                        "final-gate-stage: github-checks\n"
                        "final-gate-status: failed"
                    ),
                    orch_cost,
                    orch_model,
                )
            check_status, checks = _poll_required_checks(
                pr_owner,
                pr_repo,
                pr_number,
                project_root,
                expected_head_sha=checked_head_sha,
                quiet=quiet,
            )
            if check_status != "passed":
                return (
                    False,
                    (
                        "Final gate Layer 1 targeted PR checkup passed, but "
                        "required GitHub checks did not pass "
                        f"(status={check_status}).\n\n"
                        f"{_render_check_summary(checks)}\n\n"
                        "final-gate-stage: github-checks\n"
                        "final-gate-status: failed"
                    ),
                    orch_cost,
                    orch_model,
                )

        # Layer 2: the maintainer-style reviewer/fixer loop on the (possibly
        # Layer-1-pushed) PR head. Clear any stale verdict first so the
        # post-run read reflects THIS run only (a role/setup error returns
        # before ``_finalize`` writes a fresh one, which then reads as
        # fail-closed). ``issue_number`` is the PR number when no issue was
        # given, but the final gate always has an issue (validated above).
        clear_final_state(project_root, issue_number, pr_number)
        if load_final_state(project_root, issue_number, pr_number) is not None:
            # ``clear_final_state`` swallows a non-fatal unlink error; if a stale
            # verdict still survives, a Layer 2 that exits before finalizing
            # (e.g. a role error) would let us read the PRIOR run's clean verdict
            # as this run's. Fail closed rather than risk a false ship.
            return (
                False,
                (
                    "Final gate could not clear the stale review-loop verdict at "
                    ".pdd/checkup-review-loop/; refusing to run Layer 2 to avoid "
                    "trusting a prior run's verdict. Remove the artifact and "
                    "re-run."
                ),
                orch_cost,
                orch_model,
            )
        if not quiet:
            console.print(
                "[bold]Final gate Layer 1 (PR checkup) passed; running "
                "Layer 2 (review-loop)...[/bold]"
            )
        loop_success, loop_message, loop_cost, loop_model = _run_review_loop_layer(
            pr_content=final_gate_pr_content
        )
        ship = _review_loop_ship_verdict(
            load_final_state(project_root, issue_number, pr_number),
            has_issue=has_issue,
        )
        total_cost = orch_cost + loop_cost
        source_note = (
            ""
            if final_gate_full_suite_source == "local"
            else f"; full-suite source={final_gate_full_suite_source}"
        )
        message = (
            f"Final gate: Layer 1 (PR checkup{source_note}) passed; "
            f"Layer 2 (review-loop): {loop_message}"
        )
        if not ship and loop_success:
            # The loop produced a trustworthy report but the verdict is not
            # shippable; surface that distinctly from a loop that errored.
            message += " — verdict: not shippable (findings remain or "
            message += "verification is unverified)."
        return ship, message, total_cost, (loop_model or orch_model)

    # 6. Parse JSON report from step 7 output
    # The orchestrator returns "Checkup complete" only after enforcing Step 7's
    # structured verdict. In PR mode it owns the final report comment after a
    # successful push/reverify, so callers can trust the return tuple.

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
