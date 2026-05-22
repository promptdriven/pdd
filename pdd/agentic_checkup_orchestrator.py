"""
Multi-step orchestrator for ``pdd checkup``.

Modeled on :pymod:`agentic_bug_orchestrator` — each of the 8 checkup steps
gets its own LLM call with a focused prompt, per-step timeout, and resume
support via workflow state persistence.

Steps 3-7 (build, interfaces, test, fix, verify) run in an iterative loop
so that if verification finds remaining failures the workflow loops back to
re-check/fix until clean or ``MAX_FIX_VERIFY_ITERATIONS`` is reached.

Steps 6-8 operate in an isolated git worktree to keep fixes on a separate
branch; the worktree is created before the first loop iteration.
"""
from __future__ import annotations

import hashlib
import re
import shutil
import subprocess
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple, Union

from rich.console import Console

from .agentic_common import (
    DEFAULT_MAX_RETRIES,
    _sanitize_comment_body,
    clear_workflow_state,
    extract_step_report,
    load_workflow_state,
    normalize_step_comments_state,
    post_pr_comment,
    post_step_comment,
    post_step_comment_once,
    run_agentic_task,
    save_workflow_state,
    substitute_template_variables,
)
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess

console = Console()

# Per-step timeouts for the 8-step checkup workflow.
# Step 6 is split into 6.1 (fix), 6.2 (regression tests), 6.3 (e2e tests).
CHECKUP_STEP_TIMEOUTS: Dict[Union[int, float], float] = {
    1: 340.0,    # Discover
    2: 600.0,    # Deps
    3: 600.0,    # Build
    4: 600.0,    # Interfaces
    5: 600.0,    # Test
    6.1: 600.0,  # Fix issues
    6.2: 600.0,  # Regression tests
    6.3: 600.0,  # E2E / integration tests
    7: 1200.0,   # Verify (re-runs full test suite, needs extra time)
    8: 340.0,    # Create PR
}

TOTAL_STEPS = 8

# Ordered list of all steps (including fractional sub-steps).
STEP_ORDER: List[Union[int, float]] = [1, 2, 3, 4, 5, 6.1, 6.2, 6.3, 7, 8]

# Maximum number of build-fix-verify loop iterations before giving up.
MAX_FIX_VERIFY_ITERATIONS = 3

# Issue #1116: when the remote PR head advances mid-checkup we discard the
# stale work and restart the inner orchestrator against the new head. The
# restart budget is bounded so a PR that keeps moving cannot make us loop
# forever; once exhausted we surface a clear failure and the operator
# reruns once the branch stabilizes.
MAX_PR_HEAD_REFRESHES = 2


class _PRHeadAdvancedRestart(Exception):
    """Signal that the remote PR head moved mid-checkup.

    Raised by the inner orchestrator (``_run_agentic_checkup_orchestrator_
    inner``) when a refetch of the PR metadata reveals the head SHA
    advanced after we began verifying. The outer wrapper
    (``run_agentic_checkup_orchestrator``) catches the exception,
    consumes one slot of the refresh budget, and re-enters the inner
    against the new head — bounded by :data:`MAX_PR_HEAD_REFRESHES`.

    Carries the cost and model accumulated by the inner before the
    restart so the outer can produce an honest cumulative-cost return.

    External review Finding 2: also carries the inner's ``step_comments``
    set so the outer wrapper can replay it into the next iteration and
    prevent duplicate per-step issue comments (the iteration's
    composite-key dedup set would otherwise reset to empty after
    ``clear_workflow_state`` wipes the stored ``step_comments`` field).
    """

    def __init__(
        self,
        old_sha: str,
        new_sha: str,
        reason: str,
        cost_so_far: float = 0.0,
        model: str = "unknown",
        step_comments: Optional[Set[int]] = None,
    ) -> None:
        super().__init__(
            f"PR head advanced from {old_sha[:8]} to {new_sha[:8]}: {reason}"
        )
        self.old_sha = old_sha
        self.new_sha = new_sha
        self.reason = reason
        self.cost_so_far = cost_so_far
        self.model = model
        self.step_comments = set(step_comments) if step_comments else set()


def _refresh_count_path(cwd: Path, pr_number: int) -> Path:
    """Sidecar path holding the per-PR consumed-restart count.

    Stored under ``.pdd/checkup-pr-{pr_number}/pr_head_refreshes`` rather
    than the workflow-state file so a Ctrl-C + manual resume can't
    accidentally unbound the rerun budget — the inner discards cached
    step state on SHA mismatch already (identity guard), so we don't
    need to couple this to workflow-state semantics.
    """
    return cwd / ".pdd" / f"checkup-pr-{pr_number}" / "pr_head_refreshes"


def _load_persisted_refresh_count(cwd: Path, pr_number: int) -> int:
    """Read the persisted restart count for *pr_number*; ``0`` on miss."""
    path = _refresh_count_path(cwd, pr_number)
    try:
        if path.exists():
            return max(0, int(path.read_text(encoding="utf-8").strip() or "0"))
    except (OSError, ValueError):
        pass
    return 0


def _save_persisted_refresh_count(
    cwd: Path, pr_number: int, count: int
) -> None:
    """Best-effort persist of the restart count.

    Failures are swallowed: the in-process counter in the outer wrapper
    is authoritative for the current run; persistence is belt-and-
    suspenders for cross-process resumes.
    """
    path = _refresh_count_path(cwd, pr_number)
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(str(count), encoding="utf-8")
    except OSError:
        pass


def _clear_persisted_refresh_count(cwd: Path, pr_number: int) -> None:
    """Remove the sidecar after a clean run so the next checkup starts fresh."""
    path = _refresh_count_path(cwd, pr_number)
    try:
        if path.exists():
            path.unlink()
    except OSError:
        pass


def _next_step(current: Union[int, float]) -> Union[int, float]:
    """Return the step that follows *current* in ``STEP_ORDER``.

    Falls back to the first step whose value is strictly greater than
    *current* so that legacy state files (e.g. ``last_completed_step: 6``)
    resolve gracefully.
    """
    try:
        idx = STEP_ORDER.index(current)
        if idx + 1 < len(STEP_ORDER):
            return STEP_ORDER[idx + 1]
        return STEP_ORDER[-1]  # Already at end
    except ValueError:
        # Legacy / unknown value — find the first step strictly greater.
        for s in STEP_ORDER:
            if s > current:
                return s
        return STEP_ORDER[-1]


# ---------------------------------------------------------------------------
# Git helpers
# ---------------------------------------------------------------------------

def _get_git_root(cwd: Path) -> Optional[Path]:
    """Get the root directory of the git repository."""
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=cwd,
            capture_output=True,
            text=True,
            check=True,
        )
        return Path(result.stdout.strip())
    except subprocess.CalledProcessError:
        return None


def _get_state_dir(cwd: Path) -> Path:
    """Return path to state directory relative to git root."""
    root = _get_git_root(cwd) or cwd
    return root / ".pdd" / "checkup-state"


def _worktree_exists(cwd: Path, worktree_path: Path) -> bool:
    """Check if a path is a registered git worktree."""
    try:
        result = subprocess.run(
            ["git", "worktree", "list", "--porcelain"],
            cwd=cwd,
            capture_output=True,
            text=True,
            check=True,
        )
        return str(worktree_path.resolve()) in result.stdout
    except subprocess.CalledProcessError:
        return False


def _branch_exists(cwd: Path, branch: str) -> bool:
    """Check if a local git branch exists."""
    try:
        subprocess.run(
            ["git", "show-ref", "--verify", f"refs/heads/{branch}"],
            cwd=cwd,
            capture_output=True,
            check=True,
        )
        return True
    except subprocess.CalledProcessError:
        return False


def _remove_worktree(cwd: Path, worktree_path: Path) -> Tuple[bool, str]:
    """Remove a git worktree."""
    try:
        subprocess.run(
            ["git", "worktree", "remove", "--force", str(worktree_path)],
            cwd=cwd,
            capture_output=True,
            check=True,
        )
        return True, ""
    except subprocess.CalledProcessError as e:
        return False, e.stderr.decode("utf-8") if isinstance(e.stderr, bytes) else str(e.stderr)


def _delete_branch(cwd: Path, branch: str) -> Tuple[bool, str]:
    """Force delete a git branch."""
    try:
        subprocess.run(
            ["git", "branch", "-D", branch],
            cwd=cwd,
            capture_output=True,
            check=True,
        )
        return True, ""
    except subprocess.CalledProcessError as e:
        return False, e.stderr.decode("utf-8") if isinstance(e.stderr, bytes) else str(e.stderr)


def _pr_worktree_branch_name(git_root: Path, pr_number: int) -> str:
    """Return a PR worktree branch name scoped to this checkout root."""
    root_scope = hashlib.sha1(str(git_root.resolve()).encode("utf-8")).hexdigest()[:8]
    return f"checkup/pr-{pr_number}-{root_scope}"


def _pr_base_tracking_ref(pr_number: int) -> str:
    """Return the refreshed local ref used for PR merge-base diffs."""
    return f"refs/remotes/pdd-checkup/pr-{pr_number}/base"


def _refresh_pr_base_ref(
    worktree: Path,
    pr_owner: str,
    pr_repo: str,
    pr_number: int,
    pr_metadata: Dict[str, str],
    quiet: bool,
) -> None:
    """Fetch the PR base branch into a dedicated local ref for diff scoping."""
    pr_metadata.pop("base_local_ref", None)
    pr_metadata.pop("base_ref_fetch_error", None)
    base_ref = str(pr_metadata.get("base_ref") or "").strip()
    if not base_ref:
        return

    git_root = _get_git_root(worktree)
    if not git_root:
        pr_metadata["base_ref_fetch_error"] = "worktree is not a git repository"
        return

    remote_target = _resolve_pr_remote(git_root, pr_owner, pr_repo)
    if remote_target is None:
        remote_target = f"https://github.com/{pr_owner}/{pr_repo}.git"

    base_local_ref = _pr_base_tracking_ref(pr_number)
    try:
        subprocess.run(
            [
                "git",
                "fetch",
                remote_target,
                f"refs/heads/{base_ref}:{base_local_ref}",
                "--force",
            ],
            cwd=git_root,
            capture_output=True,
            text=True,
            check=True,
        )
    except subprocess.CalledProcessError as exc:
        safe_err = (exc.stderr or str(exc)).strip()
        token = _github_token_from_env()
        if token:
            safe_err = _redact_secret(safe_err, token)
        pr_metadata["base_ref_fetch_error"] = safe_err or "git fetch failed"
        if not quiet:
            console.print(
                f"[yellow]Warning: failed to refresh PR base ref {base_ref}: "
                f"{pr_metadata['base_ref_fetch_error']}[/yellow]"
            )
        return

    pr_metadata["base_local_ref"] = base_local_ref


def _copy_uncommitted_changes(
    git_root: Path,
    worktree_path: Path,
    quiet: bool,
) -> None:
    """Copy uncommitted and untracked files from the main repo into the worktree.

    This ensures the worktree matches the user's working directory, not just
    what's committed to HEAD. Copies:
    1. Modified/staged tracked files (via ``git diff HEAD``)
    2. Untracked files (via ``git ls-files --others --exclude-standard``)
    """
    # 1. Apply uncommitted changes to tracked files.
    try:
        diff_result = subprocess.run(
            ["git", "diff", "HEAD"],
            cwd=git_root,
            capture_output=True,
            check=True,
        )
        if diff_result.stdout:
            subprocess.run(
                ["git", "apply", "--allow-empty"],
                cwd=worktree_path,
                input=diff_result.stdout,
                capture_output=True,
                check=True,
            )
            if not quiet:
                console.print("[blue]Applied uncommitted changes to worktree[/blue]")
    except subprocess.CalledProcessError:
        # Best-effort: if diff/apply fails, continue without it.
        if not quiet:
            console.print("[yellow]Warning: Could not apply uncommitted changes to worktree[/yellow]")

    # 2. Copy untracked files.
    try:
        ls_result = subprocess.run(
            ["git", "ls-files", "--others", "--exclude-standard"],
            cwd=git_root,
            capture_output=True,
            text=True,
            check=True,
            timeout=30,
        )
        untracked_files = [f.strip() for f in ls_result.stdout.splitlines() if f.strip()]
        copied = 0
        for rel_path in untracked_files:
            src = git_root / rel_path
            dst = worktree_path / rel_path
            if not src.is_file():
                continue
            # Skip files inside .pdd/ to avoid recursive worktree copies.
            if rel_path.startswith(".pdd/"):
                continue
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(str(src), str(dst))
            copied += 1
        if copied and not quiet:
            console.print(f"[blue]Copied {copied} untracked file(s) to worktree[/blue]")
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired):
        if not quiet:
            console.print("[yellow]Warning: Could not copy untracked files to worktree[/yellow]")


def _resolve_pr_remote(
    git_root: Path,
    pr_owner: str,
    pr_repo: str,
) -> Optional[str]:
    """Find a configured git remote whose URL points at ``pr_owner/pr_repo``.

    Walks ``git remote -v`` looking for a remote URL containing the PR's
    owner/repo path. Returns the remote NAME (e.g. ``"upstream"``), or
    ``None`` if no configured remote matches — in which case callers should
    fall back to fetching directly from the explicit GitHub URL.

    Why this exists: a clone of ``myfork/repo`` cannot fetch
    ``pull/N/head`` from ``origin`` when the PR lives on ``upstream/repo``.
    Hardcoding ``origin`` was the bug the reviewer flagged.
    """
    try:
        result = subprocess.run(
            ["git", "remote", "-v"],
            cwd=git_root,
            capture_output=True,
            check=True,
            text=True,
        )
    except subprocess.CalledProcessError:
        return None

    needle = f"{pr_owner.lower()}/{pr_repo.lower()}"
    # Match `.git` and non-`.git` suffixes, http(s) and ssh forms.
    seen: set[str] = set()
    for line in result.stdout.splitlines():
        # Each line: "<name>\t<url> (<fetch|push>)"
        parts = line.split()
        if len(parts) < 2:
            continue
        name, url = parts[0], parts[1].lower()
        if name in seen:
            continue
        # Strip optional ``.git`` for comparison.
        if url.endswith(".git"):
            url = url[:-4]
        if needle in url:
            return name
        seen.add(name)
    return None


def _fetch_pr_metadata(owner: str, repo: str, pr_number: int) -> Dict[str, str]:
    """Lazy wrapper around the review-loop PR metadata helper."""
    from .checkup_review_loop import (  # pylint: disable=import-outside-toplevel
        _fetch_pr_metadata as fetch,
    )

    return fetch(owner, repo, pr_number, include_changed_files=True)


def _commit_and_push_if_changed(
    worktree: Path,
    pr_metadata: Dict[str, str],
    message: str,
) -> Tuple[bool, str]:
    """Lazy wrapper around the shared PR-head commit/push helper."""
    from .checkup_review_loop import (  # pylint: disable=import-outside-toplevel
        _commit_and_push_if_changed as commit_and_push,
    )

    return commit_and_push(worktree, pr_metadata, message)


def _is_remote_advanced_push_error(error: str) -> bool:
    """Lazy wrapper around the shared remote-advanced push-error detector.

    Re-exported at module scope so the orchestrator's Checkpoint B can
    recognize the generic ``Failed to push fixes to PR branch: <stderr>``
    surface — which is what the push helper returns once its internal
    3-attempt retry loop exhausts on remote-advance.
    """
    from .checkup_review_loop import (  # pylint: disable=import-outside-toplevel
        _is_remote_advanced_push_error as detector,
    )

    return detector(error)


def _git_changed_files(worktree: Path) -> List[str]:
    """Lazy wrapper around the review-loop changed-files helper.

    Re-exported at module scope so tests can patch
    ``pdd.agentic_checkup_orchestrator._git_changed_files`` without
    monkey-patching across module boundaries.
    """
    from .checkup_review_loop import (  # pylint: disable=import-outside-toplevel
        _git_changed_files as fn,
    )

    return fn(worktree)


def _git_rev_parse_head(worktree: Path) -> str:
    """Lazy wrapper around the review-loop HEAD-SHA helper."""
    from .checkup_review_loop import (  # pylint: disable=import-outside-toplevel
        _git_rev_parse_head as fn,
    )

    return fn(worktree)


def _check_prompt_source_guard(
    worktree: Path, changed_files: List[str]
) -> Optional[str]:
    """Lazy wrapper around the review-loop prompt-source guard (clause 10a).

    PDD's source-of-truth contract is that prompts generate code. Bare PR-mode
    used to push fixer-generated edits directly to the PR head without ever
    running this guard, so a code-only patch could land and silently violate
    #1063 until the next ``pdd sync`` overwrote the bot's edits. Re-exporting
    the review-loop guard here lets the orchestrator enforce the same policy
    BEFORE the push (matching the review-loop call site).
    """
    from .checkup_review_loop import (  # pylint: disable=import-outside-toplevel
        _check_prompt_source_guard as fn,
    )

    return fn(worktree, changed_files)


def _check_architecture_registry_edit_guard(
    worktree: Path, changed_files: List[str]
) -> Optional[str]:
    """Lazy wrapper around the review-loop architecture-registry guard (clause 10b).

    Sibling of ``_check_prompt_source_guard``. Catches the coordinated
    rename + prompt delete + registry rewrite shape (issue #1081) that
    10a alone cannot detect.
    """
    from .checkup_review_loop import (  # pylint: disable=import-outside-toplevel
        _check_architecture_registry_edit_guard as fn,
    )

    return fn(worktree, changed_files)


def _redact_secret(text: str, secret: str) -> str:
    """Lazy wrapper around the review-loop secret-redaction helper."""
    from .checkup_review_loop import (  # pylint: disable=import-outside-toplevel
        _redact_secret as fn,
    )

    return fn(text, secret)


def _github_token_from_env() -> str:
    """Lazy wrapper around the review-loop env-token helper."""
    from .checkup_review_loop import (  # pylint: disable=import-outside-toplevel
        _github_token_from_env as fn,
    )

    return fn()


def _step7_passed(step7_output: str, pr_mode: bool) -> Tuple[bool, str]:
    """Parse Step 7's JSON report and decide whether the checkup may proceed.

    The Step 7 prompt (``agentic_checkup_step7_verify_LLM.prompt``) requires
    a structured JSON report as the last block of output, shaped like::

        {{
          "success": true/false,
          "issue_aligned": true/false,    # PR mode only — REQUIRED
          "issues": [
            {{"severity": "critical|medium|low", "fixed": true/false, ...}},
            ...
          ],
          ...
        }}

    Returns ``(passed, failure_reason)`` where ``passed`` is True iff:

    * ``success`` is ``True``;
    * in PR mode, ``issue_aligned`` is ``True``;
    * no entry in ``issues`` has ``severity == "critical"`` and ``fixed != True``.

    Fails closed: if no JSON object can be extracted, returns
    ``(False, "Step 7 verdict JSON could not be parsed: ...")`` so the
    orchestrator never proceeds on an ambiguous verdict (Finding 1 of the
    round-3 external review). Reuses the JSON-extraction helper defined in
    :mod:`pdd.agentic_checkup` via a lazy import to avoid a circular module
    dependency at orchestrator import time.
    """
    from .agentic_checkup import (  # pylint: disable=import-outside-toplevel
        _extract_json_from_text,
    )

    if not step7_output or not step7_output.strip():
        return (
            False,
            "Step 7 verdict JSON could not be parsed: empty step 7 output.",
        )

    payload = _extract_json_from_text(step7_output)
    if payload is None:
        snippet = step7_output.strip()
        if len(snippet) > 200:
            snippet = snippet[:200] + "..."
        return (
            False,
            f"Step 7 verdict JSON could not be parsed (fail-closed): {snippet}",
        )

    if payload.get("success") is not True:
        return (
            False,
            f"Step 7 reported success=false. "
            f"Message: {payload.get('message') or '<no message>'}",
        )

    if pr_mode and payload.get("issue_aligned") is not True:
        return (
            False,
            f"Step 7 reported issue_aligned=false — PR does not resolve the "
            f"source issue. Message: "
            f"{payload.get('message') or '<no message>'}",
        )

    issues = payload.get("issues")
    if isinstance(issues, list):
        unfixed_critical: List[str] = []
        for issue in issues:
            if not isinstance(issue, dict):
                continue
            severity = str(issue.get("severity", "")).lower()
            if severity != "critical":
                continue
            if issue.get("fixed") is True:
                continue
            module = issue.get("module") or issue.get("file") or "<unknown>"
            desc = (
                issue.get("description")
                or issue.get("fix_description")
                or "<no description>"
            )
            unfixed_critical.append(f"{module}: {desc}")
        if unfixed_critical:
            joined = "; ".join(unfixed_critical[:5])
            more = "" if len(unfixed_critical) <= 5 else (
                f" (+{len(unfixed_critical) - 5} more)"
            )
            return (
                False,
                f"Step 7 reported unfixed critical issues: {joined}{more}",
            )

    return True, ""


def _format_pr_mode_final_report(step7_output: str, push_message: str) -> str:
    """Build the trusted post-push PR/issue comment body."""
    body = step7_output.strip()
    push_message = push_message.strip()
    if push_message:
        body = f"{body}\n\n### PR Push Status\n{push_message}"
    return _sanitize_comment_body(body)


def _refresh_pr_context_from_worktree(
    context: Dict[str, str],
    worktree_path: Path,
) -> None:
    """Re-load project context from the PR worktree.

    ``run_agentic_checkup`` loads architecture.json / .pddrc from the
    *pre-worktree* checkout before the orchestrator runs (round-5
    Finding 3). When ``pdd checkup --pr`` checks out the PR head into
    ``.pdd/worktrees/checkup-pr-<n>``, any architecture/config changes
    the PR makes are invisible to downstream prompts unless we refresh
    the context here.

    Overwrites ``project_root``, ``architecture_json``, and
    ``pddrc_content`` in place. Falls back to the canonical "missing"
    string when the worktree lacks either file — stale caller content
    must not leak through.

    Imports are lazy because :mod:`agentic_checkup` imports this module
    at top level; eager imports would form a cycle.
    """
    import json as _json  # pylint: disable=import-outside-toplevel

    from .agentic_checkup import (  # pylint: disable=import-outside-toplevel
        _escape_format_braces,
        _load_pddrc_content,
    )
    from .agentic_sync import (  # pylint: disable=import-outside-toplevel
        _find_project_root,
        _load_architecture_json,
    )

    pr_project_root = _find_project_root(worktree_path)
    context["project_root"] = str(pr_project_root)

    try:
        architecture, _arch_path = _load_architecture_json(pr_project_root)
    except Exception:  # pylint: disable=broad-except
        architecture = None
    if architecture:
        raw_arch_json_str = _json.dumps(architecture, indent=2)
    else:
        raw_arch_json_str = "No architecture.json available."
    context["architecture_json"] = _escape_format_braces(raw_arch_json_str)

    raw_pddrc_content = _load_pddrc_content(pr_project_root)
    context["pddrc_content"] = _escape_format_braces(raw_pddrc_content)


def _setup_pr_worktree(
    cwd: Path,
    pr_owner: str,
    pr_repo: str,
    pr_number: int,
    quiet: bool,
    resume_existing: bool = False,
) -> Tuple[Optional[Path], Optional[str]]:
    """Create an isolated worktree checked out to an existing PR's head branch.

    Used by ``pdd checkup --pr`` so that verification runs against the code the
    PR actually proposes (not a fresh branch off HEAD). Resolves the PR's
    source remote via ``pr_owner``/``pr_repo`` instead of hardcoding
    ``origin`` — this is what makes fork-PR verification work when the
    local clone's ``origin`` is not the upstream PR repo.

    Returns ``(worktree_path, error_message)``.
    """
    git_root = _get_git_root(cwd)
    if not git_root:
        return None, "Current directory is not a git repository."

    worktree_rel_path = Path(".pdd") / "worktrees" / f"checkup-pr-{pr_number}"
    worktree_path = git_root / worktree_rel_path
    branch_name = _pr_worktree_branch_name(git_root, pr_number)

    # 1. Clean up existing worktree at path
    if worktree_path.exists():
        if _worktree_exists(git_root, worktree_path):
            if not quiet:
                console.print(f"[yellow]Removing existing worktree at {worktree_path}[/yellow]")
            success, err = _remove_worktree(git_root, worktree_path)
            if not success:
                return None, f"Failed to remove existing worktree: {err}"
        else:
            if not quiet:
                console.print(f"[yellow]Removing stale directory at {worktree_path}[/yellow]")
            shutil.rmtree(worktree_path)

    # 2. Fetch the PR's head into a local branch.
    #    Always refresh (force) so a re-run picks up new pushes to the PR.
    if _branch_exists(git_root, branch_name) and not resume_existing:
        _delete_branch(git_root, branch_name)

    # Resolve which remote actually has this PR. Prefer a configured remote
    # (uses the user's auth + caching); fall back to the explicit GitHub URL
    # so fork-PR verification works even when no matching remote is wired.
    remote_target = _resolve_pr_remote(git_root, pr_owner, pr_repo)
    if remote_target is None:
        remote_target = f"https://github.com/{pr_owner}/{pr_repo}.git"

    try:
        subprocess.run(
            ["git", "fetch", remote_target, f"pull/{pr_number}/head:{branch_name}", "--force"],
            cwd=git_root,
            capture_output=True,
            check=True,
        )
    except subprocess.CalledProcessError as e:
        err_msg = e.stderr.decode("utf-8") if isinstance(e.stderr, bytes) else str(e.stderr)
        # Redact any GH token that git may echo back from a tokenized remote
        # URL (e.g. when callers seed ``https://x-access-token:...@github.com``
        # into the resolved remote). Matches the push-failure redaction at
        # ``checkup_review_loop._commit_and_push_if_changed``.
        token = _github_token_from_env()
        safe_err = _redact_secret(err_msg.strip(), token) if token else err_msg.strip()
        safe_remote = _redact_secret(remote_target, token) if token else remote_target
        return None, (
            f"Failed to fetch PR #{pr_number} from {safe_remote}: {safe_err}. "
            f"Confirm the PR exists and you have read access to "
            f"{pr_owner}/{pr_repo}."
        )

    # 3. Create worktree on the fetched branch.
    try:
        worktree_path.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["git", "worktree", "add", str(worktree_path), branch_name],
            cwd=git_root,
            capture_output=True,
            check=True,
        )
    except subprocess.CalledProcessError as e:
        err_msg = e.stderr.decode("utf-8") if isinstance(e.stderr, bytes) else str(e.stderr)
        return None, f"Failed to create PR worktree: {err_msg}"

    # Do NOT copy uncommitted changes here — PR-mode must reflect the PR's
    # actual state, not the developer's local edits.

    return worktree_path, None


def _setup_worktree(
    cwd: Path,
    issue_number: int,
    quiet: bool,
    resume_existing: bool = False,
) -> Tuple[Optional[Path], Optional[str]]:
    """Create an isolated git worktree for the checkup fix.

    After creation the worktree is populated with uncommitted and untracked
    files from the main working directory so that all steps see the same
    files the user is working with.

    Returns ``(worktree_path, error_message)``.
    """
    git_root = _get_git_root(cwd)
    if not git_root:
        return None, "Current directory is not a git repository."

    worktree_rel_path = Path(".pdd") / "worktrees" / f"checkup-issue-{issue_number}"
    worktree_path = git_root / worktree_rel_path
    branch_name = f"checkup/issue-{issue_number}"

    # 1. Clean up existing worktree at path
    if worktree_path.exists():
        if _worktree_exists(git_root, worktree_path):
            if not quiet:
                console.print(f"[yellow]Removing existing worktree at {worktree_path}[/yellow]")
            success, err = _remove_worktree(git_root, worktree_path)
            if not success:
                return None, f"Failed to remove existing worktree: {err}"
        else:
            if not quiet:
                console.print(f"[yellow]Removing stale directory at {worktree_path}[/yellow]")
            shutil.rmtree(worktree_path)

    # 2. Handle existing branch
    has_branch = _branch_exists(git_root, branch_name)
    if has_branch:
        if resume_existing:
            if not quiet:
                console.print(f"[blue]Resuming with existing branch: {branch_name}[/blue]")
        else:
            if not quiet:
                console.print(f"[yellow]Removing existing branch {branch_name}[/yellow]")
            _delete_branch(git_root, branch_name)
            has_branch = False

    # 3. Create worktree
    try:
        worktree_path.parent.mkdir(parents=True, exist_ok=True)

        if has_branch and resume_existing:
            subprocess.run(
                ["git", "worktree", "add", str(worktree_path), branch_name],
                cwd=git_root,
                capture_output=True,
                check=True,
            )
        else:
            subprocess.run(
                ["git", "worktree", "add", "-b", branch_name, str(worktree_path), "HEAD"],
                cwd=git_root,
                capture_output=True,
                check=True,
            )
    except subprocess.CalledProcessError as e:
        err_msg = e.stderr.decode("utf-8") if isinstance(e.stderr, bytes) else str(e.stderr)
        return None, f"Failed to create worktree: {err_msg}"

    # 4. Copy uncommitted + untracked files so the worktree matches
    #    the user's working directory (not just HEAD).
    if not resume_existing:
        _copy_uncommitted_changes(git_root, worktree_path, quiet)

    return worktree_path, None


def _parse_changed_files(output: str) -> List[str]:
    """Extract file paths from FILES_CREATED / FILES_MODIFIED lines."""
    files: List[str] = []
    for line in output.splitlines():
        if line.startswith("FILES_CREATED:") or line.startswith("FILES_MODIFIED:"):
            file_list = line.split(":", 1)[1].strip()
            files.extend([f.strip() for f in file_list.split(",") if f.strip()])
    return files


def _is_provider_failure(output: str) -> bool:
    """Return true when the agent runner exhausted every provider."""
    return "All agent providers failed" in output


def _is_step_timeout_failure(output: str) -> bool:
    """Return true when a step failed because the agent process timed out."""
    return bool(
        re.search(
            r"(Timeout expired|TimeoutExpired|agent(?:ic)? execution timed out|Agent timed out|step \d+(?:\.\d+)? timed out)",
            output or "",
            flags=re.IGNORECASE,
        )
    )


def _format_step_abort_message(step_num: Union[int, float], output: str) -> str:
    """Format a no-fix hard-stop message with the real failure class."""
    if _is_step_timeout_failure(output):
        return (
            f"Aborting after Step {step_num}: agent execution timed out "
            "before the step could complete"
        )
    if _is_provider_failure(output):
        return f"Aborting after Step {step_num}: agent providers unavailable"
    return f"Aborting after Step {step_num}: step failed"


def _format_pr_changed_files_for_prompt(
    worktree: Path,
    pr_metadata: Optional[Dict[str, str]] = None,
) -> str:
    """Return a concise merge-base changed-file summary for PR-mode prompts."""
    base_candidates: List[str] = []
    api_changed_files = (
        str((pr_metadata or {}).get("api_changed_files") or "").strip()
        if pr_metadata is not None
        else ""
    )
    api_changed_files_full = (
        str((pr_metadata or {}).get("api_changed_files_full") or "").strip()
        if pr_metadata is not None
        else ""
    )
    artifact_note = ""
    if api_changed_files_full:
        artifact_rel = Path(".pdd") / "checkup-context" / "pr-changed-files-api.txt"
        try:
            artifact_path = worktree / artifact_rel
            artifact_path.parent.mkdir(parents=True, exist_ok=True)
            artifact_path.write_text(api_changed_files_full + "\n", encoding="utf-8")
            artifact_note = (
                "\nFull API changed-file list artifact: "
                f"{artifact_rel.as_posix()}"
            )
        except OSError:
            artifact_note = "\nFull API changed-file list artifact: unavailable"
    api_fallback = (
        "Source: GitHub PR files API\n" + api_changed_files + artifact_note
        if api_changed_files
        else ""
    )
    if pr_metadata is not None:
        base_ref = str(pr_metadata.get("base_ref") or "").strip()
        if base_ref:
            base_local_ref = str(pr_metadata.get("base_local_ref") or "").strip()
            if base_local_ref:
                base_candidates.append(base_local_ref)
            else:
                if api_fallback:
                    return api_fallback
                fetch_error = str(pr_metadata.get("base_ref_fetch_error") or "").strip()
                reason = f" Fetch error: {fetch_error}" if fetch_error else ""
                return (
                    "PR changed files unavailable: PR base ref "
                    f"'{base_ref}' was not refreshed into a local tracking ref."
                    f"{reason} Do not use stale origin/{base_ref}; run targeted "
                    "tests conservatively or refresh the PR base ref."
                )
        else:
            if api_fallback:
                return api_fallback
            return (
                "PR changed files unavailable: PR base metadata is missing. "
                "Do not use stale origin/main; run targeted tests conservatively "
                "or refresh PR metadata."
            )
    else:
        base_candidates.extend([
            "origin/main",
            "origin/master",
            "main",
            "master",
        ])

    seen_bases: Set[str] = set()
    for base in base_candidates:
        if not base or base in seen_bases:
            continue
        seen_bases.add(base)
        try:
            verify = subprocess.run(
                ["git", "rev-parse", "--verify", base],
                cwd=worktree,
                capture_output=True,
                text=True,
            )
        except (OSError, subprocess.SubprocessError):
            continue
        if verify.returncode != 0:
            continue

        try:
            diff = subprocess.run(
                [
                    "git",
                    "diff",
                    "--name-status",
                    "--find-renames",
                    f"{base}...HEAD",
                ],
                cwd=worktree,
                capture_output=True,
                text=True,
            )
        except (OSError, subprocess.SubprocessError):
            continue
        if diff.returncode != 0:
            continue

        lines: List[str] = []
        for raw_line in diff.stdout.splitlines():
            parts = [part.strip() for part in raw_line.split("\t") if part.strip()]
            if len(parts) < 2:
                continue
            status = parts[0]
            if status.startswith("R") and len(parts) >= 3:
                path = f"{parts[1]} -> {parts[2]}"
            else:
                path = parts[-1]
            lines.append(f"- {status}: {path}")

        if lines:
            return "Base: " + base + "\n" + "\n".join(lines)
        return f"Base: {base}\nNo changed files found against this base."

    if api_fallback:
        return api_fallback

    tried = ", ".join(seen_bases) if seen_bases else "none"
    return (
        "PR changed files unavailable: no local PR base ref could be resolved "
        f"(tried: {tried}). Do not infer PR scope from HEAD~1; run targeted "
        "tests conservatively or fetch the PR base ref."
    )


# ---------------------------------------------------------------------------
# Internal: run a single step
# ---------------------------------------------------------------------------

def _run_single_step(
    step_num: Union[int, float],
    name: str,
    context: Dict[str, str],
    *,
    cwd: Path,
    step_cwd: Path,
    verbose: bool,
    quiet: bool,
    label: str,
    timeout_adder: float,
    reasoning_time: Optional[float] = None,
) -> Optional[Tuple[bool, str, float, str]]:
    """Load template, preprocess, format, and run a single LLM step.

    Returns ``(success, output, cost, model)`` on success, or
    ``None`` if the template could not be loaded (caller should abort).
    The *label* parameter is forwarded to :func:`run_agentic_task` so that
    iteration-suffixed labels like ``step3_iter1`` can be used.
    """
    # Fractional steps use underscores in template names: step6_1 -> step6_1
    step_str = str(step_num).replace(".", "_")
    template_name = f"agentic_checkup_step{step_str}_{name}_LLM"
    prompt_template = load_prompt_template(template_name)

    if not prompt_template:
        return None  # Signals missing template — caller returns error.

    exclude_keys = list(context.keys())
    prompt_template = preprocess(
        prompt_template,
        recursive=True,
        double_curly_brackets=True,
        exclude_keys=exclude_keys,
    )

    formatted_prompt = substitute_template_variables(prompt_template, context)

    success, output, cost, model = run_agentic_task(
        instruction=formatted_prompt,
        cwd=step_cwd,
        verbose=verbose,
        quiet=quiet,
        label=label,
        timeout=CHECKUP_STEP_TIMEOUTS.get(step_num, 600.0) + timeout_adder,
        max_retries=DEFAULT_MAX_RETRIES,
        reasoning_time=reasoning_time,
    )
    return (success, output, cost, model)


# ---------------------------------------------------------------------------
# Orchestrator
# ---------------------------------------------------------------------------


def _run_agentic_checkup_orchestrator_inner(
    issue_url: str,
    issue_content: str,
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    issue_title: str,
    architecture_json: str,
    pddrc_content: str,
    *,
    cwd: Path,
    verbose: bool = False,
    quiet: bool = False,
    no_fix: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True,
    reasoning_time: Optional[float] = None,
    pr_url: Optional[str] = None,
    pr_owner: Optional[str] = None,
    pr_repo: Optional[str] = None,
    pr_number: Optional[int] = None,
    test_scope: str = "full",
    start_step_override: Optional[Union[int, float]] = None,
    # External review (issue #1116). Both default to "off"; set only by
    # the outer wrapper on restart iterations.
    _force_skip_state_load: bool = False,
    _carried_step_comments: Optional[Set[int]] = None,
) -> Tuple[bool, str, float, str]:
    """Orchestrate the 8-step agentic checkup workflow.

    When ``pr_url`` is provided, the workflow runs in PR-verification mode:
    the worktree is based on the PR's head branch, step 8 (create PR) is
    skipped, and step 7's context is augmented with issue-alignment signals
    so the verify step can report whether the PR actually resolves the
    source issue.

    Returns:
        (success, final_message, total_cost, model_used)
    """
    pr_mode = pr_url is not None and pr_number is not None
    if test_scope not in ("full", "targeted"):
        raise ValueError(
            f"test_scope must be 'full' or 'targeted', got {test_scope!r}"
        )
    pr_test_scope = test_scope if pr_mode else "full"
    if not quiet:
        console.print(
            f"[bold]Running checkup for issue #{issue_number}: "
            f"\"{issue_title}\"[/bold]"
        )

    # Context accumulation — grows across steps.
    context: Dict[str, str] = {
        "issue_url": issue_url,
        "issue_content": issue_content,
        "repo_owner": repo_owner,
        "repo_name": repo_name,
        "issue_number": str(issue_number),
        "issue_title": issue_title,
        "architecture_json": architecture_json,
        "pddrc_content": pddrc_content,
        "project_root": str(cwd),
        "no_fix": "true" if no_fix else "false",
        # PR-mode signals (empty strings when not in PR mode so .format()
        # substitution never KeyErrors on a prompt that references them).
        "pr_mode": "true" if pr_mode else "false",
        "pr_url": pr_url or "",
        "pr_owner": pr_owner or "",
        "pr_repo": pr_repo or "",
        "pr_number": str(pr_number) if pr_number is not None else "",
        "pr_push_output": "",
        "pr_changed_files": "",
        "pr_test_scope": pr_test_scope,
        "manual_start_step": str(start_step_override or ""),
        "worktree_path": "",
        "files_to_stage": "",
        "fix_verify_iteration": "1",
        "max_fix_verify_iterations": str(MAX_FIX_VERIFY_ITERATIONS),
        "previous_fixes": "",
    }
    for step in STEP_ORDER:
        step_key = str(step).replace(".", "_")
        context[f"step{step_key}_output"] = ""

    total_cost = 0.0
    last_model_used = "unknown"
    changed_files: List[str] = []
    current_cwd = cwd
    worktree_path: Optional[Path] = None
    github_comment_id: Optional[int] = None

    # Resume: load existing state if available.
    state_dir = _get_state_dir(cwd)
    # External review Finding 3: on restart iterations the outer wrapper
    # sets ``_force_skip_state_load=True`` so a flaky GitHub state load
    # cannot reload stale cached step outputs even if ``clear_workflow_
    # state``'s GitHub DELETE silently failed. Defense-in-depth around
    # the clear-then-reload path.
    if _force_skip_state_load:
        state = None
        loaded_gh_id = None
    else:
        state, loaded_gh_id = load_workflow_state(
            cwd=cwd,
            issue_number=issue_number,
            workflow_type="checkup",
            state_dir=state_dir,
            repo_owner=repo_owner,
            repo_name=repo_name,
            use_github_state=use_github_state,
        )

    step_outputs: Dict[str, str] = {}
    last_completed_step = 0
    fix_verify_iteration = 0
    previous_fixes = ""

    # Round-5 Finding 4: accumulates a suffix when the canonical PR-mode
    # final report could not be posted to GitHub. The gate outcome stays
    # source-of-truth — gh / network flakiness must not flip a clean
    # code-verification — but the suffix is appended to the returned
    # ``message`` on success paths so consumers (pdd-issue, pdd_cloud)
    # see the partial-post condition.
    pending_post_suffix: str = ""

    # PR head SHA observed for the CURRENT invocation. Captured once via
    # ``_fetch_pr_metadata`` when entering PR mode so the resume path can
    # invalidate cached step outputs whose verification ran against a
    # different (older) head. Empty/None when metadata is unavailable —
    # callers degrade gracefully rather than block.
    current_pr_head_sha: str = ""
    metadata_for_guard: Dict[str, str] = {}
    if pr_mode:
        assert pr_owner is not None and pr_repo is not None and pr_number is not None
        try:
            metadata_for_guard = _fetch_pr_metadata(pr_owner, pr_repo, pr_number)
        except Exception:  # noqa: BLE001 — metadata is best-effort
            metadata_for_guard = {}
        current_pr_head_sha = str(metadata_for_guard.get("head_sha", "") or "")

    if state is not None:
        # State-identity guard. A state from a prior run on the same
        # issue_number must match the current invocation across FOUR
        # axes before reuse:
        #   (a) mode (issue vs pr) — different worktree paths
        #   (b) pr_number — same issue can verify different PRs over time
        #   (c) pr_owner/pr_repo — fork-PR identity (same pr_number could
        #       refer to different upstream/fork combos)
        #   (d) pr_head_sha — the PR branch can advance between runs
        #       (maintainer push, auto-heal, etc.). Cached step outputs
        #       describing build/test/verify results from the OLD SHA
        #       would otherwise be silently replayed against new code
        #       (codex round-1 blocker #1).
        # Any mismatch carries stale step outputs and a stale
        # `.pdd/worktrees/checkup-pr-A` path into a verification of PR B,
        # silently running all subsequent steps against the wrong code.
        cached_mode = state.get("mode", "issue")
        current_mode = "pr" if pr_mode else "issue"
        identity_mismatch_reasons: list[str] = []
        if cached_mode != current_mode:
            identity_mismatch_reasons.append(
                f"mode (cached={cached_mode}, current={current_mode})"
            )
        if current_mode == "pr":
            cached_pr_number = state.get("pr_number")
            if cached_pr_number != pr_number:
                identity_mismatch_reasons.append(
                    f"pr_number (cached={cached_pr_number}, current={pr_number})"
                )
            cached_pr_owner = state.get("pr_owner")
            cached_pr_repo = state.get("pr_repo")
            if (
                cached_pr_owner is not None
                and cached_pr_repo is not None
                and (cached_pr_owner, cached_pr_repo) != (pr_owner, pr_repo)
            ):
                identity_mismatch_reasons.append(
                    f"pr_repo "
                    f"(cached={cached_pr_owner}/{cached_pr_repo}, "
                    f"current={pr_owner}/{pr_repo})"
                )
            # Head-SHA invalidation — FAIL CLOSED (codex round-2
            # follow-through). Reuse cached PR step outputs ONLY when both
            # the cached and current ``pr_head_sha`` are non-empty AND
            # equal. Every other combination — missing cached SHA (state
            # predates this axis), missing current SHA (metadata fetch
            # unavailable), or different non-empty SHAs — discards cache.
            #
            # Fail-open is the bug the SHA axis was added to prevent:
            # silently replaying step outputs verified against an unknown
            # or older PR head against new code. A first-PR-run with
            # cached state predating this field also gets re-verified
            # rather than reused; since the field isn't released yet, the
            # one-time cost is acceptable to preserve "if you can't prove
            # it's the same code, don't trust the verification".
            cached_pr_head_sha = state.get("pr_head_sha") or ""
            if not (
                cached_pr_head_sha
                and current_pr_head_sha
                and cached_pr_head_sha == current_pr_head_sha
            ):
                identity_mismatch_reasons.append(
                    f"pr_head_sha "
                    f"(cached={cached_pr_head_sha[:8] or '<empty>'}, "
                    f"current={current_pr_head_sha[:8] or '<empty>'})"
                )
        if identity_mismatch_reasons:
            if not quiet:
                console.print(
                    f"[yellow]State identity mismatch — discarding cached "
                    f"state to avoid running in the wrong worktree. "
                    f"Reasons: {'; '.join(identity_mismatch_reasons)}[/yellow]"
                )
            state = None

    if state is not None:
        last_completed_step = state.get("last_completed_step", 0)
        cached_outputs = state.get("step_outputs", {})

        # Validate cached state — find actual last successful step.
        if cached_outputs:
            actual_last_success: Union[int, float] = 0
            for sn in STEP_ORDER:
                # Fractional steps use "_" in state keys: 6.1 -> "6_1"
                state_key = str(sn).replace(".", "_")
                output_val = cached_outputs.get(state_key, "")
                if not output_val:
                    break
                if output_val.startswith("FAILED:"):
                    break
                actual_last_success = sn
            if actual_last_success < last_completed_step:
                if not quiet:
                    console.print(
                        f"[yellow]State validation: correcting last_completed_step "
                        f"from {last_completed_step} to {actual_last_success} "
                        f"(found FAILED steps in cache)[/yellow]"
                    )
                last_completed_step = actual_last_success

        resume_start_step = _next_step(last_completed_step) if last_completed_step > 0 else 1
        if not quiet:
            console.print(
                f"[yellow]Resuming from step {resume_start_step} "
                f"(through step {last_completed_step} cached)[/yellow]"
            )

        total_cost = state.get("total_cost", 0.0)
        last_model_used = state.get("model_used", "unknown")
        step_outputs = state.get("step_outputs", {})
        changed_files = state.get("changed_files", [])
        github_comment_id = loaded_gh_id
        fix_verify_iteration = state.get("fix_verify_iteration", 0)
        previous_fixes = state.get("previous_fixes", "")

        # Restore worktree path from state
        wt_path_str = state.get("worktree_path")
        if wt_path_str:
            worktree_path = Path(wt_path_str)
            if worktree_path.exists():
                current_cwd = worktree_path
            else:
                # Recreate worktree with existing branch — use the right
                # setup helper for the mode. PR-mode worktrees check out
                # the PR's head ref via _setup_pr_worktree; reusing
                # _setup_worktree here would silently re-create a fresh
                # issue-mode worktree from HEAD instead of the PR's code,
                # so all subsequent verification steps would run against
                # the wrong tree.
                if pr_mode:
                    assert pr_number is not None and pr_owner is not None and pr_repo is not None
                    wt_path, err = _setup_pr_worktree(
                        cwd, pr_owner, pr_repo, pr_number, quiet, resume_existing=True
                    )
                else:
                    wt_path, err = _setup_worktree(cwd, issue_number, quiet, resume_existing=True)
                if err:
                    return False, f"Failed to recreate worktree on resume: {err}", total_cost, last_model_used
                worktree_path = wt_path
                current_cwd = worktree_path
            context["worktree_path"] = str(worktree_path)
            # Round-5 Finding 3: refresh project context on resume too.
            # The state dict does not persist architecture_json/pddrc/
            # project_root; on resume the caller-supplied (pre-worktree)
            # values land in ``context`` and post-resume steps would
            # otherwise audit stale architecture/config.
            if pr_mode:
                _refresh_pr_context_from_worktree(context, worktree_path)
                assert pr_owner is not None and pr_repo is not None and pr_number is not None
                _refresh_pr_base_ref(
                    worktree_path,
                    pr_owner,
                    pr_repo,
                    pr_number,
                    metadata_for_guard,
                    quiet,
                )
                if pr_test_scope == "targeted":
                    context["pr_changed_files"] = _format_pr_changed_files_for_prompt(
                        worktree_path,
                        metadata_for_guard,
                    )

        # Restore context from cached step outputs.
        # State keys use underscores (e.g. "6_1"); context keys follow suit.
        for step_key, output in step_outputs.items():
            context[f"step{step_key}_output"] = output

        # Restore files_to_stage if available
        if changed_files:
            context["files_to_stage"] = ", ".join(changed_files)

    if state is None:
        # External review Finding 2: when re-entering after a restart,
        # the outer wrapper passes the previous iteration's
        # ``step_comments_set`` so per-step issue comments aren't
        # re-posted on the new iteration. Defaults to a fresh empty set
        # when not provided (every non-restart entry path).
        step_comments_set: Set[int] = (
            set(_carried_step_comments) if _carried_step_comments else set()
        )
    else:
        step_comments_set = normalize_step_comments_state(state.get("step_comments"))

    # Step definitions (step 6 split into 6.1/6.2/6.3 sub-steps).
    steps: List[Tuple[Union[int, float], str, str]] = [
        (1,   "discover",         "Discovering project structure and tech stack"),
        (2,   "deps",             "Auditing dependencies"),
        (3,   "build",            "Running build/compile checks"),
        (4,   "interfaces",       "Checking cross-module interfaces"),
        (5,   "test",             "Running tests"),
        (6.1, "fix",              "Fixing discovered issues"),
        (6.2, "regression_tests", "Writing regression tests"),
        (6.3, "e2e_tests",       "Writing e2e/integration tests"),
        (7,   "verify",           "Verifying fixes and generating report"),
        (8,   "create_pr",        "Creating pull request"),
    ]
    step_map: Dict[Union[int, float], Tuple[str, str]] = {
        s[0]: (s[1], s[2]) for s in steps
    }

    # Display mapping for fractional steps (user-facing console).
    _display_step: Dict[float, str] = {6.1: "6a", 6.2: "6b", 6.3: "6c"}

    start_step = _next_step(last_completed_step) if last_completed_step > 0 else 1
    if start_step_override is not None:
        if start_step_override not in STEP_ORDER:
            return (
                False,
                f"Invalid start step: {start_step_override}",
                total_cost,
                last_model_used,
            )
        start_step = start_step_override
    last_completed_step_to_save = last_completed_step
    consecutive_provider_failures = 0

    # ---- Helper closures for state management ----

    def _save_state() -> None:
        """Persist current workflow state."""
        nonlocal github_comment_id
        new_state = _build_state(
            issue_number, issue_url, last_completed_step_to_save,
            step_outputs, total_cost, last_model_used, github_comment_id,
            changed_files, worktree_path,
            fix_verify_iteration=fix_verify_iteration,
            previous_fixes=previous_fixes,
            mode="pr" if pr_mode else "issue",
            pr_number=pr_number,
            pr_owner=pr_owner,
            pr_repo=pr_repo,
            pr_head_sha=current_pr_head_sha if pr_mode else None,
            step_comments=sorted(step_comments_set),
        )
        github_comment_id = save_workflow_state(
            cwd=cwd, issue_number=issue_number, workflow_type="checkup",
            state=new_state, state_dir=state_dir,
            repo_owner=repo_owner, repo_name=repo_name,
            use_github_state=use_github_state,
            github_comment_id=github_comment_id,
        )

    def _step_comment_key(step_num: Union[int, float], iteration: int = 1) -> int:
        """Project (step_num, iteration) -> deterministic non-negative int.

        Encoding ``iteration * 10000 + int(round(step_num * 10))`` handles
        fractional steps (6.1 -> 61) and the iterated fix-verify loop.
        """
        return iteration * 10000 + int(round(float(step_num) * 10))

    def _maybe_post_step_comment(
        step_num: Union[int, float],
        description: str,
        step_output: str,
        iteration: int = 1,
    ) -> None:
        """Post a trusted per-step success comment; log-and-continue on error."""
        try:
            report_body = extract_step_report(step_output)
            if not report_body:
                report_body = (
                    f"_Step {step_num} completed; no `<step_report>` block "
                    "returned by agent. Raw output retained in workflow state._"
                )
            comment_body = (
                f"## Step {step_num}/{TOTAL_STEPS}: {description}\n\n{report_body}"
            )
            post_step_comment_once(
                repo_owner=repo_owner,
                repo_name=repo_name,
                issue_number=issue_number,
                step_num=_step_comment_key(step_num, iteration),
                body=comment_body,
                posted_steps=step_comments_set,
                cwd=current_cwd,
            )
        except Exception as exc:  # pylint: disable=broad-except
            console.print(f"[yellow]post_step_comment_once failed: {exc}[/yellow]")

    def _handle_step_result(
        step_num: Union[int, float],
        success: bool,
        output: str,
        cost: float,
        model: str,
        description: str = "",
        iteration: int = 1,
    ) -> Optional[Tuple[bool, str, float, str]]:
        """Process a step result — update context, save state.

        Returns an abort tuple if consecutive provider failures are hit,
        otherwise None.
        """
        nonlocal total_cost, last_model_used, last_completed_step_to_save
        nonlocal consecutive_provider_failures

        total_cost += cost
        last_model_used = model

        # Use underscore-based key for fractional steps: 6.1 -> "6_1"
        step_key = str(step_num).replace(".", "_")
        context[f"step{step_key}_output"] = output

        # Steps 6.1/6.2/6.3: parse changed files.
        if step_num in (6.1, 6.2, 6.3) and success:
            extracted_files = _parse_changed_files(output)
            changed_files.extend(extracted_files)
            # Deduplicate preserving order
            changed_files[:] = list(dict.fromkeys(changed_files))
            context["files_to_stage"] = ", ".join(changed_files)

        if not success and not quiet:
            console.print(
                f"[yellow]Warning: Step {step_num} reported failure, "
                f"but proceeding as no hard stop condition met.[/yellow]"
            )
        elif not quiet:
            console.print(f"  -> Step {step_num} complete.")

        if success:
            step_outputs[step_key] = output
            last_completed_step_to_save = step_num
            consecutive_provider_failures = 0
            if description:
                _maybe_post_step_comment(step_num, description, output, iteration)
        else:
            step_outputs[step_key] = f"FAILED: {output}"
            if _is_provider_failure(output):
                consecutive_provider_failures += 1
                if consecutive_provider_failures >= 3:
                    _save_state()
                    failure_kind = (
                        "agent execution timed out before the steps could complete"
                        if _is_step_timeout_failure(output)
                        else "agent providers unavailable"
                    )
                    return (
                        False,
                        f"Aborting: {consecutive_provider_failures} consecutive "
                        f"steps failed - {failure_kind}",
                        total_cost,
                        last_model_used,
                    )
            else:
                consecutive_provider_failures = 0

        _save_state()
        return None

    def _run_post_push_reverify_if_needed(
        push_message: str,
    ) -> Optional[Tuple[bool, str, float, str]]:
        """Re-run Step 7 when push rebased local fixes onto a newer PR head."""
        if "after rebasing onto updated PR head" not in push_message:
            return None

        name7, desc7 = step_map[7]
        if not quiet:
            console.print(
                f"[bold][Step 7/{TOTAL_STEPS}][/bold] {desc7} "
                f"(post-push reverify)..."
            )

        result = _run_single_step(
            7,
            name7,
            context,
            cwd=cwd,
            step_cwd=current_cwd if worktree_path else cwd,
            verbose=verbose,
            quiet=quiet,
            label="step7_post_push_reverify",
            timeout_adder=timeout_adder,
            reasoning_time=reasoning_time,
        )
        if result is None:
            template_name = f"agentic_checkup_step7_{name7}_LLM"
            return (
                False,
                f"Missing prompt template: {template_name}",
                total_cost,
                last_model_used,
            )

        success, output, cost, model = result
        abort = _handle_step_result(7, success, output, cost, model)
        if abort is not None:
            return abort
        if not success or "All Issues Fixed" not in output:
            return (
                False,
                "Post-push verification did not confirm the final rebased PR head is clean.",
                total_cost,
                last_model_used,
            )
        # Round-4 Finding 1 follow-through: re-apply the strict JSON gate
        # to the post-push reverify output. The "All Issues Fixed" string
        # alone is just a loop-exit sentinel; the structured verdict is
        # what tells us the rebased tree actually satisfies the contract.
        passed, reason = _step7_passed(output, pr_mode=pr_mode)
        if not passed:
            return (
                False,
                f"Post-push verification failed Step 7 gate: {reason}",
                total_cost,
                last_model_used,
            )
        return None

    def _post_pr_mode_final_report(final_step7_output: str) -> str:
        """Post the canonical PR-mode final report to PR + issue threads.

        Returns a ``status_suffix`` (empty when reporting is not applicable
        or both posts succeeded). On failure, the rendered body is also
        persisted under ``.pdd/checkup-pr-<n>/final-report.md`` and a
        human-readable status is written into
        ``step_outputs["pr_post_status"]`` so downstream consumers can
        detect the partial-post condition without parsing the message.

        The gate outcome is NOT flipped by a post failure — gh / network
        flakiness must remain decoupled from code-verification truth
        (round-5 Finding 4). Callers should append the returned suffix
        to whatever message they return so pdd-issue / pdd_cloud see the
        partial-post in their summary surface.
        """
        if not (
            pr_mode
            and use_github_state
            and pr_owner
            and pr_repo
            and pr_number is not None
            and final_step7_output.strip()
        ):
            return ""

        body = _format_pr_mode_final_report(
            final_step7_output,
            context.get("pr_push_output", ""),
        )
        pr_posted = post_pr_comment(pr_owner, pr_repo, pr_number, body, cwd)
        step_posted = post_step_comment(
            repo_owner=repo_owner,
            repo_name=repo_name,
            issue_number=issue_number,
            step_num=7,
            total_steps=TOTAL_STEPS,
            description="Verification & Final Report",
            output=final_step7_output,
            cwd=cwd,
            body=body,
        )
        if pr_posted and step_posted:
            return ""

        # Comment-post failed: persist the body so the report is not lost.
        artifact_dir = cwd / ".pdd" / f"checkup-pr-{pr_number}"
        artifact_path: Optional[Path] = artifact_dir / "final-report.md"
        try:
            artifact_dir.mkdir(parents=True, exist_ok=True)
            artifact_path.write_text(body, encoding="utf-8")
        except OSError as exc:
            if not quiet:
                console.print(
                    f"[yellow]Warning: failed to persist final report "
                    f"artifact at {artifact_path}: {exc}[/yellow]"
                )
            artifact_path = None

        failed_surfaces: List[str] = []
        if not pr_posted:
            failed_surfaces.append("PR")
        if not step_posted:
            failed_surfaces.append("issue")
        surfaces_str = " and ".join(failed_surfaces)
        if artifact_path is not None:
            persisted = (
                f"Final report post failed for {surfaces_str} surface; "
                f"saved to {artifact_path}"
            )
            suffix = (
                f" (report post failed for {surfaces_str} surface; "
                f"saved to {artifact_path})"
            )
        else:
            persisted = (
                f"Final report post failed for {surfaces_str} surface; "
                f"artifact also could not be persisted"
            )
            suffix = (
                f" (report post failed for {surfaces_str} surface; "
                f"artifact could not be saved)"
            )
        step_outputs["pr_post_status"] = persisted
        _save_state()
        if not quiet:
            console.print(f"[yellow]{persisted}[/yellow]")
        return suffix

    # ==================================================================
    # PR mode: create the PR-branch worktree up-front. All subsequent steps
    # (including no-fix verification) then see the PR's code, not HEAD.
    # ==================================================================
    if pr_mode and worktree_path is None and start_step <= 7:
        assert pr_number is not None  # mypy — pr_mode guarantees this
        assert pr_owner is not None and pr_repo is not None
        wt_path, err = _setup_pr_worktree(
            cwd, pr_owner, pr_repo, pr_number, quiet, resume_existing=False
        )
        if not wt_path:
            return (
                False,
                f"Failed to set up PR worktree: {err}",
                total_cost,
                last_model_used,
            )
        worktree_path = wt_path
        current_cwd = worktree_path
        context["worktree_path"] = str(worktree_path)

        # Round-5 Finding 3: refresh project context from the PR worktree
        # so downstream prompts audit the PR's project state. Caller
        # passed architecture/pddrc loaded from the pre-PR-worktree
        # ``cwd``; if the PR modifies either file, the audit otherwise
        # never sees the change.
        _refresh_pr_context_from_worktree(context, worktree_path)
        assert pr_owner is not None and pr_repo is not None and pr_number is not None
        _refresh_pr_base_ref(
            worktree_path,
            pr_owner,
            pr_repo,
            pr_number,
            metadata_for_guard,
            quiet,
        )
        if pr_test_scope == "targeted":
            context["pr_changed_files"] = _format_pr_changed_files_for_prompt(
                worktree_path,
                metadata_for_guard,
            )

        if not quiet:
            console.print(
                f"[blue]PR-mode worktree (PR #{pr_number}): {worktree_path}[/blue]"
            )

        _save_state()

    # ==================================================================
    # Section 1: Steps 1-2 (linear, run once)
    # ==================================================================

    for step_num in (1, 2):
        if step_num < start_step:
            continue

        name, description = step_map[step_num]
        if not quiet:
            console.print(f"[bold][Step {step_num}/{TOTAL_STEPS}][/bold] {description}...")

        # PR-mode runs discovery in the PR worktree so project-shape matches
        # the PR's code (e.g. new files appear, deleted files don't).
        step_cwd_12 = current_cwd if pr_mode and worktree_path else cwd

        result = _run_single_step(
            step_num, name, context,
            cwd=cwd, step_cwd=step_cwd_12,
            verbose=verbose, quiet=quiet,
            label=f"step{step_num}",
            timeout_adder=timeout_adder,
            reasoning_time=reasoning_time,
        )

        if result is None:
            template_name = f"agentic_checkup_step{step_num}_{name}_LLM"
            return (False, f"Missing prompt template: {template_name}", total_cost, last_model_used)

        success, output, cost, model = result

        abort = _handle_step_result(step_num, success, output, cost, model, description=description)
        if abort is not None:
            return abort

    # ==================================================================
    # Section 2: Steps 3-7 (iterative loop or linear for --no-fix)
    # ==================================================================

    loop_steps: List[Tuple[Union[int, float], str, str]] = [
        (3,   "build",            "Running build/compile checks"),
        (4,   "interfaces",       "Checking cross-module interfaces"),
        (5,   "test",             "Running tests"),
        (6.1, "fix",              "Fixing discovered issues"),
        (6.2, "regression_tests", "Writing regression tests"),
        (6.3, "e2e_tests",       "Writing e2e/integration tests"),
        (7,   "verify",           "Verifying fixes and generating report"),
    ]

    if no_fix:
        # --no-fix: run steps 3, 4, 5 linearly, skip 6, run 7, skip 8.
        # In PR mode the linear steps run inside the PR worktree.
        nofix_step_cwd = current_cwd if pr_mode and worktree_path else cwd
        for step_num in (3, 4, 5):
            if step_num < start_step:
                continue
            name, description = step_map[step_num]
            if not quiet:
                console.print(
                    f"[bold][Step {step_num}/{TOTAL_STEPS}][/bold] "
                    f"{description}..."
                )

            result = _run_single_step(
                step_num, name, context,
                cwd=cwd, step_cwd=nofix_step_cwd,
                verbose=verbose, quiet=quiet,
                label=f"step{step_num}",
                timeout_adder=timeout_adder,
                reasoning_time=reasoning_time,
            )

            if result is None:
                template_name = f"agentic_checkup_step{step_num}_{name}_LLM"
                return (False, f"Missing prompt template: {template_name}", total_cost, last_model_used)

            success, output, cost, model = result
            abort = _handle_step_result(step_num, success, output, cost, model, description=description)
            if abort is not None:
                return abort
            if not success and (
                _is_provider_failure(output) or _is_step_timeout_failure(output)
            ):
                return (
                    False,
                    _format_step_abort_message(step_num, output),
                    total_cost,
                    last_model_used,
                )

        # Skip step 6 sub-steps.
        for sub_step in (6.1, 6.2, 6.3):
            if sub_step >= start_step:
                sub_key = str(sub_step).replace(".", "_")
                disp = _display_step.get(sub_step, str(sub_step))
                if not quiet:
                    console.print(
                        f"[bold][Step {disp}/{TOTAL_STEPS}][/bold] Skipped (--no-fix mode)"
                    )
                skipped_output = "Skipped: --no-fix mode"
                step_outputs[sub_key] = skipped_output
                context[f"step{sub_key}_output"] = skipped_output
                last_completed_step_to_save = sub_step
        if any(s >= start_step for s in (6.1, 6.2, 6.3)):
            _save_state()

        # Run step 7.
        nofix_step7_output = ""
        if 7 >= start_step:
            name7, desc7 = step_map[7]
            if not quiet:
                console.print(f"[bold][Step 7/{TOTAL_STEPS}][/bold] {desc7}...")

            result = _run_single_step(
                7, name7, context,
                cwd=cwd, step_cwd=nofix_step_cwd,
                verbose=verbose, quiet=quiet,
                label="step7",
                timeout_adder=timeout_adder,
                reasoning_time=reasoning_time,
            )

            if result is None:
                template_name = f"agentic_checkup_step7_{name7}_LLM"
                return (False, f"Missing prompt template: {template_name}", total_cost, last_model_used)

            success, output, cost, model = result
            nofix_step7_output = output
            abort = _handle_step_result(7, success, output, cost, model, description=desc7)
            if abort is not None:
                return abort
        else:
            # Resume path that already cached step 7's output.
            nofix_step7_output = step_outputs.get("7", "")

        # Round-4 Finding 1: gate the --no-fix verification path too.
        # No push happens here, but pdd-issue / pdd_cloud consume the
        # return tuple. Returning success when Step 7 reported failure
        # would be the same anti-pattern as the fix-mode push case.
        nofix_gate_passed, nofix_gate_reason = _step7_passed(
            nofix_step7_output, pr_mode=pr_mode
        )

        # Skip step 8.
        if 8 >= start_step:
            if not quiet:
                console.print(f"[bold][Step 8/{TOTAL_STEPS}][/bold] Skipped (--no-fix mode)")
            skipped_output = "Skipped: --no-fix mode"
            step_outputs["8"] = skipped_output
            context["step8_output"] = skipped_output
            last_completed_step_to_save = 8
            _save_state()

        if not nofix_gate_passed:
            if not quiet:
                console.print(
                    f"[red]Step 7 gate failed (--no-fix): {nofix_gate_reason}[/red]"
                )
            # Post the canonical PR/issue final report even when the gate
            # fails: Step 7's PR-mode prompt suppresses agent commenting
            # because the orchestrator owns the report. Skipping the post
            # here leaves downstream consumers (pdd-issue, reviewers) with
            # no record of what was checked or why it failed.
            post_suffix = _post_pr_mode_final_report(nofix_step7_output)
            return (
                False,
                f"{nofix_gate_reason}{post_suffix}",
                total_cost,
                last_model_used,
            )

        # External review Finding 1: in --no-fix --pr mode the orchestrator
        # is the only authority — ``_finalize``'s fail-closed downgrade only
        # runs under --review-loop, and the fix-mode freshness lease's
        # checkpoints all explicitly skip ``no_fix``. Refetch the remote PR
        # head before publishing the canonical verification report; if the
        # head advanced during the run, downgrade to failure with a
        # diagnostic so a stale clean verdict isn't posted as fresh.
        # Fail-closed (no rerun budget consumed) — the lease is fix-mode
        # only by design.
        if pr_mode and worktree_path is not None and no_fix and nofix_gate_passed:
            assert pr_owner is not None and pr_repo is not None
            assert pr_number is not None
            try:
                nofix_fresh_metadata = _fetch_pr_metadata(pr_owner, pr_repo, pr_number)
            except Exception:  # noqa: BLE001 — metadata is best-effort
                nofix_fresh_metadata = {}
            nofix_fresh_sha = str(
                (nofix_fresh_metadata or {}).get("head_sha", "") or ""
            )
            if (
                nofix_fresh_sha
                and current_pr_head_sha
                and nofix_fresh_sha != current_pr_head_sha
            ):
                stale_msg = (
                    f"--no-fix verification on PR #{pr_number} produced a "
                    f"clean Step 7 verdict but the PR head advanced during "
                    f"the run ({current_pr_head_sha[:8]}->{nofix_fresh_sha[:8]}). "
                    f"Verdict treated as unverified; rerun pdd checkup --pr "
                    f"--no-fix."
                )
                if not quiet:
                    console.print(f"[red]{stale_msg}[/red]")
                # Post the canonical report so the PR thread shows what was
                # verified and why it was downgraded — same pattern as the
                # gate-fail path above.
                stale_post_suffix = _post_pr_mode_final_report(nofix_step7_output)
                return (
                    False,
                    f"{stale_msg}{stale_post_suffix}",
                    total_cost,
                    last_model_used,
                )

        # No-fix gate passed: post the canonical report so PR consumers see
        # the verification verdict. The fix-mode equivalent runs after the
        # push at the bottom of this function; the no-fix path never pushes,
        # so we post here.
        pending_post_suffix = _post_pr_mode_final_report(nofix_step7_output)

    else:
        # --- Fix mode: iterative loop over steps 3-7 ---

        # Create worktree before first loop iteration. In PR mode the worktree
        # was already created above; skip this issue-based setup.
        if not pr_mode and worktree_path is None and start_step <= 7:
            wt_path, err = _setup_worktree(cwd, issue_number, quiet, resume_existing=False)
            if not wt_path:
                return False, f"Failed to create worktree: {err}", total_cost, last_model_used

            worktree_path = wt_path
            current_cwd = worktree_path
            context["worktree_path"] = str(worktree_path)

            if not quiet:
                console.print(f"[blue]Working in worktree: {worktree_path}[/blue]")

            # Bug A fix: persist worktree_path immediately so Ctrl+C
            # during step 3 can resume without recreating it.
            _save_state()

        is_first_loop_pass = True
        # If resuming mid-iteration, fix_verify_iteration is already > 0
        # from state; don't increment on the first pass.
        resuming_mid_iteration = fix_verify_iteration > 0

        # Bug B fix: between-iterations resume.
        # If start_step > 7 and we're mid-loop, the previous iteration's
        # step 7 completed without "All Issues Fixed" — start a fresh
        # iteration.
        if (start_step > 7 and fix_verify_iteration > 0
                and fix_verify_iteration < MAX_FIX_VERIFY_ITERATIONS):
            step6_1_out = step_outputs.get("6_1", step_outputs.get("6", ""))
            previous_fixes += f"\n\nIteration {fix_verify_iteration} fixes:\n{step6_1_out}"
            fix_verify_iteration += 1
            start_step = 3
            resuming_mid_iteration = True  # Already incremented

        step7_output = ""

        while fix_verify_iteration < MAX_FIX_VERIFY_ITERATIONS:
            if resuming_mid_iteration:
                resuming_mid_iteration = False
            else:
                fix_verify_iteration += 1
            context["fix_verify_iteration"] = str(fix_verify_iteration)
            context["max_fix_verify_iterations"] = str(MAX_FIX_VERIFY_ITERATIONS)
            context["previous_fixes"] = previous_fixes

            if not quiet and not is_first_loop_pass:
                console.print(
                    f"\n[bold cyan]--- Fix-Verify Iteration {fix_verify_iteration}"
                    f"/{MAX_FIX_VERIFY_ITERATIONS} ---[/bold cyan]"
                )

            step7_output = ""

            for step_num, name, description in loop_steps:
                # On first pass through the loop, honour resume (skip
                # already-done steps). Subsequent iterations run all steps.
                if is_first_loop_pass and step_num < start_step:
                    continue

                # Label uses underscores: step6_1_iter1
                step_str = str(step_num).replace(".", "_")
                iter_label = f"step{step_str}_iter{fix_verify_iteration}"

                # All loop steps (3-7) run in worktree.
                step_cwd = current_cwd if worktree_path else cwd

                # User-facing display: fractional steps show as 6a/6b/6c.
                disp = _display_step.get(step_num, str(step_num))
                if not quiet:
                    console.print(
                        f"[bold][Step {disp}/{TOTAL_STEPS}][/bold] "
                        f"{description} (iter {fix_verify_iteration})..."
                    )

                result = _run_single_step(
                    step_num, name, context,
                    cwd=cwd, step_cwd=step_cwd,
                    verbose=verbose, quiet=quiet,
                    label=iter_label,
                    timeout_adder=timeout_adder,
                    reasoning_time=reasoning_time,
                )

                if result is None:
                    tmpl_name = f"agentic_checkup_step{step_str}_{name}_LLM"
                    return (False, f"Missing prompt template: {tmpl_name}", total_cost, last_model_used)

                success, output, cost, model = result
                abort = _handle_step_result(
                    step_num, success, output, cost, model,
                    description=description, iteration=fix_verify_iteration,
                )
                if abort is not None:
                    return abort

                if step_num == 7:
                    step7_output = output

            # Check exit condition: "All Issues Fixed" in step 7 output.
            if "All Issues Fixed" in step7_output:
                if not quiet:
                    console.print("[green]All issues fixed — exiting loop.[/green]")
                break

            # Accumulate previous fixes for next iteration.
            step6_1_out = step_outputs.get("6_1", "")
            previous_fixes += f"\n\nIteration {fix_verify_iteration} fixes:\n{step6_1_out}"
            is_first_loop_pass = False
            _save_state()

        if fix_verify_iteration >= MAX_FIX_VERIFY_ITERATIONS and "All Issues Fixed" not in step7_output:
            max_msg = (
                f"Checkup did not verify all issues fixed after "
                f"{MAX_FIX_VERIFY_ITERATIONS} fix-verify iterations."
            )
            max_reason = max_msg
            max_gate_passed, max_gate_reason = _step7_passed(
                step7_output, pr_mode=pr_mode
            )
            if not max_gate_passed:
                max_reason = f"{max_msg} {max_gate_reason}"
            if not quiet:
                console.print(
                    f"[red]{max_reason} Not pushing fixes or creating a PR.[/red]"
                )
            if pr_mode:
                step_outputs["pr_push"] = f"Skipped push because: {max_reason}"
                context["pr_push_output"] = step_outputs["pr_push"]
            else:
                step_outputs["8"] = f"Skipped step 8 because: {max_reason}"
                context["step8_output"] = step_outputs["8"]
            _save_state()
            # Step 7's PR-mode prompt suppresses agent commenting because
            # the orchestrator owns the canonical report. Post it here so
            # the PR thread records the max-iteration verdict instead of
            # going silent.
            post_suffix = _post_pr_mode_final_report(
                step_outputs.get("7", step7_output)
            )
            return (
                False,
                f"{max_reason}{post_suffix}",
                total_cost,
                last_model_used,
            )

        # --------------------------------------------------------------
        # Round-4 Finding 1: gate the orchestrator on Step 7's structured
        # verdict BEFORE pushing to a PR or creating one. Without this
        # gate, the loop printed a warning and pushed anyway, so a PR
        # with `issue_aligned: false` or unfixed critical issues could be
        # marked green by downstream consumers.
        # --------------------------------------------------------------
        gate_passed, gate_reason = _step7_passed(step7_output, pr_mode=pr_mode)
        if not gate_passed:
            if not quiet:
                console.print(
                    f"[red]Step 7 gate failed: {gate_reason}[/red]"
                )
            if pr_mode:
                skip_msg = f"Skipped push because: {gate_reason}"
                step_outputs["pr_push"] = skip_msg
                context["pr_push_output"] = skip_msg
            else:
                skip_msg = f"Skipped step 8 because: {gate_reason}"
                step_outputs["8"] = skip_msg
                context["step8_output"] = skip_msg
            # Persist the gate signal but do NOT clear workflow state — an
            # operator may want to resume after fixing the underlying
            # issue. Return failure so callers (pdd-issue, pdd_cloud,
            # operators) see the gate fired instead of receiving a
            # success message for a checkup that did not pass.
            _save_state()
            # Step 7's PR-mode prompt suppresses agent commenting because
            # the orchestrator owns the canonical report. Post it on the
            # gate-fail path too so the PR thread shows the verdict
            # instead of going silent.
            post_suffix = _post_pr_mode_final_report(
                step_outputs.get("7", step7_output)
            )
            return (
                False,
                f"{gate_reason}{post_suffix}",
                total_cost,
                last_model_used,
            )

        # --------------------------------------------------------------
        # Issue #1116 — Checkpoint A: the gate just passed, but if the
        # remote PR head advanced since we entered the run, every cached
        # step result (build, test, verify) was produced against the OLD
        # code. Pushing now would land our fixes on top of unverified
        # remote changes. Refetch the head SHA; if it moved, raise the
        # restart signal so the outer wrapper can rerun against the new
        # head (bounded by ``MAX_PR_HEAD_REFRESHES``).
        #
        # Only fires in fix mode. ``--no-fix`` falls through to the
        # existing flow because no push is forthcoming. Transient
        # ``_fetch_pr_metadata`` failures (empty fresh SHA) fail-degrade
        # to current behavior to avoid false-positive restarts.
        # --------------------------------------------------------------
        if pr_mode and worktree_path is not None and not no_fix:
            assert pr_owner is not None and pr_repo is not None
            assert pr_number is not None
            try:
                fresh_metadata = _fetch_pr_metadata(pr_owner, pr_repo, pr_number)
            except Exception:  # noqa: BLE001 — metadata is best-effort
                fresh_metadata = {}
            fresh_head_sha = str((fresh_metadata or {}).get("head_sha", "") or "")
            if (
                fresh_head_sha
                and current_pr_head_sha
                and fresh_head_sha != current_pr_head_sha
            ):
                raise _PRHeadAdvancedRestart(
                    old_sha=current_pr_head_sha,
                    new_sha=fresh_head_sha,
                    reason="Step 7 gate passed but PR head advanced before push",
                    cost_so_far=total_cost,
                    model=last_model_used,
                    step_comments=step_comments_set,
                )

        # ==============================================================
        # Section 3: Step 8 (create PR) — after the loop
        # In PR mode we SKIP step 8 entirely — the PR already exists; our
        # job was to verify it (and optionally push fix commits, not open a
        # new PR).
        # ==============================================================

        if pr_mode:
            assert pr_owner is not None
            assert pr_repo is not None
            assert pr_number is not None
            if worktree_path is not None:
                pr_metadata = _fetch_pr_metadata(pr_owner, pr_repo, pr_number)

                # Codex round-1 blocker #3: prompt-source + architecture-
                # registry guards. The review-loop runs these BEFORE its
                # push (checkup_review_loop.py:1183/:1194); bare PR-mode
                # used to skip them, opening a #1063/#1081 bypass. Run
                # 10b first (registry-edit) and 10a second (prompt-
                # source) to mirror the review-loop ordering.
                guard_changed_files = _git_changed_files(worktree_path)
                pr_artifacts_dir = cwd / ".pdd" / f"checkup-pr-{pr_number}"

                registry_refusal = _check_architecture_registry_edit_guard(
                    worktree_path, guard_changed_files
                )
                if registry_refusal:
                    pr_artifacts_dir.mkdir(parents=True, exist_ok=True)
                    (
                        pr_artifacts_dir
                        / "architecture-registry-guard-refusal.txt"
                    ).write_text(registry_refusal + "\n")
                    step_outputs["pr_push"] = registry_refusal
                    context["pr_push_output"] = registry_refusal
                    _save_state()
                    # Step 7 already ran successfully; the registry guard
                    # blocks the push, not the verdict. Post the canonical
                    # report so the PR records why the push was refused.
                    post_suffix = _post_pr_mode_final_report(
                        step_outputs.get("7", step7_output)
                    )
                    return (
                        False,
                        f"{registry_refusal}{post_suffix}",
                        total_cost,
                        last_model_used,
                    )

                prompt_refusal = _check_prompt_source_guard(
                    worktree_path, guard_changed_files
                )
                if prompt_refusal:
                    pr_artifacts_dir.mkdir(parents=True, exist_ok=True)
                    (
                        pr_artifacts_dir / "prompt-source-guard-refusal.txt"
                    ).write_text(prompt_refusal + "\n")
                    step_outputs["pr_push"] = prompt_refusal
                    context["pr_push_output"] = prompt_refusal
                    _save_state()
                    # Step 7 already ran successfully; the prompt-source
                    # guard blocks the push, not the verdict. Post the
                    # canonical report so the PR records why the push was
                    # refused.
                    post_suffix = _post_pr_mode_final_report(
                        step_outputs.get("7", step7_output)
                    )
                    return (
                        False,
                        f"{prompt_refusal}{post_suffix}",
                        total_cost,
                        last_model_used,
                    )

                push_ok, push_message = _commit_and_push_if_changed(
                    worktree_path,
                    pr_metadata,
                    f"fix: apply checkup fixes for #{issue_number}",
                )
                step_outputs["pr_push"] = push_message
                context["pr_push_output"] = push_message
                _save_state()
                if not push_ok:
                    # Codex round-1 blocker #2 / round-2 nit A: enrich the
                    # failure message so the operator can recover the
                    # unpushed local fix.
                    # ``_commit_and_push_if_changed`` can fail at any of
                    # several points: ``git add`` (no commit yet), ``git
                    # commit`` (no commit yet), missing PR metadata after
                    # commit, or ``push`` after commit. We don't try to
                    # distinguish; instead we point the operator at the
                    # worktree HEAD with neutral wording so they can
                    # inspect for an unpushed fix commit regardless of
                    # which leg failed.
                    local_sha = _git_rev_parse_head(worktree_path)
                    sha_clause = (
                        f" at SHA {local_sha}" if local_sha else ""
                    )
                    recovery = (
                        f" Local HEAD in worktree: {worktree_path}"
                        f"{sha_clause}; check for an unpushed fix commit "
                        f"before re-running."
                    )
                    sep = "" if push_message.rstrip().endswith(".") else "."
                    enriched = push_message + sep + recovery
                    step_outputs["pr_push"] = enriched
                    context["pr_push_output"] = enriched
                    _save_state()
                    # ------------------------------------------------------
                    # Issue #1116 — Checkpoint B: restart if the push failed
                    # because we couldn't rebase onto an updated remote
                    # head. Only consume budget after a fresh refetch
                    # confirms the head actually moved — generic auth /
                    # network errors must not trigger a rerun.
                    #
                    # Codex round-1 Finding 1: also match the generic
                    # ``Failed to push fixes to PR branch: <stderr>``
                    # surface that ``_commit_and_push_if_changed`` returns
                    # once its internal 3-attempt retry loop exhausts on
                    # remote-advance. Without the
                    # ``_is_remote_advanced_push_error`` co-trigger, a
                    # legitimate auth/network failure with the same
                    # prefix would falsely restart, so the embedded git
                    # stderr must carry recognized markers (fetch-first /
                    # non-fast-forward / etc.).
                    # ------------------------------------------------------
                    if not no_fix and (
                        "Failed to rebase fixes onto updated PR branch"
                        in push_message
                        or "Failed to refresh PR branch before retrying push"
                        in push_message
                        # Codex round-2 Finding 2: _rebase_onto_updated_
                        # pr_head emits this prefix when the pre-rebase
                        # ``git reset --hard <fixer_sha>`` fails. The
                        # reset only runs in the remote-advance recovery
                        # path, so a refetch-confirmed advance still
                        # qualifies for the bounded restart.
                        or "Failed to reset to original fixer commit before rebase"
                        in push_message
                        or (
                            push_message.startswith(
                                "Failed to push fixes to PR branch:"
                            )
                            and _is_remote_advanced_push_error(push_message)
                        )
                    ):
                        try:
                            fresh_meta_b = _fetch_pr_metadata(
                                pr_owner, pr_repo, pr_number
                            )
                        except Exception:  # noqa: BLE001
                            fresh_meta_b = {}
                        fresh_head_sha_b = str(
                            (fresh_meta_b or {}).get("head_sha", "") or ""
                        )
                        if (
                            fresh_head_sha_b
                            and current_pr_head_sha
                            and fresh_head_sha_b != current_pr_head_sha
                        ):
                            raise _PRHeadAdvancedRestart(
                                old_sha=current_pr_head_sha,
                                new_sha=fresh_head_sha_b,
                                reason="Push rebase failed against advanced PR head",
                                cost_so_far=total_cost,
                                model=last_model_used,
                                step_comments=step_comments_set,
                            )
                    # Step 7 already ran successfully; the push itself
                    # failed. Post the canonical report so the PR records
                    # the verdict and the enriched failure context.
                    post_suffix = _post_pr_mode_final_report(
                        step_outputs.get("7", step7_output)
                    )
                    return (
                        False,
                        f"{enriched}{post_suffix}",
                        total_cost,
                        last_model_used,
                    )
                if not quiet:
                    console.print(f"[green]{push_message}[/green]")
                post_push_abort = _run_post_push_reverify_if_needed(push_message)
                if post_push_abort is not None:
                    # Step 7 ran twice (pre-push + post-rebase reverify).
                    # The reverify produced a verdict before failing; post
                    # the canonical report so PR consumers see the failure
                    # context. ``step_outputs["7"]`` is refreshed by
                    # ``_run_single_step``'s persistence so it reflects the
                    # latest (post-rebase) verdict.
                    abort_ok, abort_reason, abort_cost, abort_model = post_push_abort
                    post_suffix = _post_pr_mode_final_report(
                        step_outputs.get("7", step7_output)
                    )
                    return (
                        abort_ok,
                        f"{abort_reason}{post_suffix}",
                        abort_cost,
                        abort_model,
                    )
                # ------------------------------------------------------
                # Codex round-1 Finding 2 — Checkpoint C: a no-change
                # push outcome means we never actually touched the PR
                # branch. The head could have advanced between
                # Checkpoint A's refetch and now, and neither
                # Checkpoint B (only fires on push failure) nor the
                # post-push reverify (only fires on rebase-success
                # marker) covers this gap. Refetch one more time
                # before publishing the Step 7 verdict; restart if
                # the head moved so we don't post a stale verdict as
                # fresh.
                # ------------------------------------------------------
                if push_message in (
                    "No changes to push.",
                    "No eligible changes to push.",
                ):
                    try:
                        fresh_meta_c = _fetch_pr_metadata(
                            pr_owner, pr_repo, pr_number
                        )
                    except Exception:  # noqa: BLE001
                        fresh_meta_c = {}
                    fresh_head_sha_c = str(
                        (fresh_meta_c or {}).get("head_sha", "") or ""
                    )
                    if (
                        fresh_head_sha_c
                        and current_pr_head_sha
                        and fresh_head_sha_c != current_pr_head_sha
                    ):
                        raise _PRHeadAdvancedRestart(
                            old_sha=current_pr_head_sha,
                            new_sha=fresh_head_sha_c,
                            reason=(
                                "No-change push completed but PR head "
                                "advanced before final report"
                            ),
                            cost_so_far=total_cost,
                            model=last_model_used,
                            step_comments=step_comments_set,
                        )
                pending_post_suffix = _post_pr_mode_final_report(
                    step_outputs.get("7", step7_output)
                )
            if 8 >= start_step:
                if not quiet:
                    console.print(
                        f"[bold][Step 8/{TOTAL_STEPS}][/bold] Skipped "
                        f"(PR-mode: verifying existing PR #{pr_number})"
                    )
                step_outputs["8"] = f"Skipped: PR-mode verification of PR #{pr_number}"
                context["step8_output"] = step_outputs["8"]
                last_completed_step_to_save = 8
                _save_state()
        elif 8 >= start_step or fix_verify_iteration > 0:
            name8, desc8 = step_map[8]
            step_cwd_8 = current_cwd if worktree_path else cwd

            if not quiet:
                console.print(f"[bold][Step 8/{TOTAL_STEPS}][/bold] {desc8}...")

            result = _run_single_step(
                8, name8, context,
                cwd=cwd, step_cwd=step_cwd_8,
                verbose=verbose, quiet=quiet,
                label="step8",
                timeout_adder=timeout_adder,
                reasoning_time=reasoning_time,
            )

            if result is None:
                template_name = f"agentic_checkup_step8_{name8}_LLM"
                return (False, f"Missing prompt template: {template_name}", total_cost, last_model_used)

            success, output, cost, model = result
            abort = _handle_step_result(8, success, output, cost, model, description=desc8)
            if abort is not None:
                return abort

    # All steps complete — clear state.
    clear_workflow_state(
        cwd=cwd,
        issue_number=issue_number,
        workflow_type="checkup",
        state_dir=state_dir,
        repo_owner=repo_owner,
        repo_name=repo_name,
        use_github_state=use_github_state,
    )

    final_msg = "Checkup complete"
    if not quiet:
        console.print(f"[green]{final_msg}[/green]")
        console.print(f"   Total cost: ${total_cost:.4f}")
        if changed_files:
            console.print(f"   Files changed: {', '.join(changed_files)}")
        if worktree_path:
            console.print(f"   Worktree: {worktree_path}")

    return (
        True,
        f"{final_msg}{pending_post_suffix}",
        total_cost,
        last_model_used,
    )


def run_agentic_checkup_orchestrator(
    issue_url: str,
    issue_content: str,
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    issue_title: str,
    architecture_json: str,
    pddrc_content: str,
    *,
    cwd: Path,
    verbose: bool = False,
    quiet: bool = False,
    no_fix: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True,
    reasoning_time: Optional[float] = None,
    pr_url: Optional[str] = None,
    pr_owner: Optional[str] = None,
    pr_repo: Optional[str] = None,
    pr_number: Optional[int] = None,
) -> Tuple[bool, str, float, str]:
    """Public entry point for the agentic checkup orchestrator.

    Wraps :func:`_run_agentic_checkup_orchestrator_inner`. In non-PR mode
    this is a straight pass-through. In PR mode it catches
    :class:`_PRHeadAdvancedRestart` and re-enters the inner against the
    new head, bounded by :data:`MAX_PR_HEAD_REFRESHES` (issue #1116).

    The retry budget is durable: the consumed count lives in a sidecar
    file at ``.pdd/checkup-pr-{pr_number}/pr_head_refreshes`` so a
    Ctrl-C + manual rerun cannot bypass the bound. The counter is
    cleared on a clean terminal success.

    Returns ``(success, message, total_cost, model_used)`` — same shape
    as the inner.
    """
    pr_mode = pr_url is not None and pr_number is not None
    if not pr_mode:
        return _run_agentic_checkup_orchestrator_inner(
            issue_url=issue_url,
            issue_content=issue_content,
            repo_owner=repo_owner,
            repo_name=repo_name,
            issue_number=issue_number,
            issue_title=issue_title,
            architecture_json=architecture_json,
            pddrc_content=pddrc_content,
            cwd=cwd,
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

    # PR-mode rerun loop. ``refresh_count`` is initialized from disk so a
    # resumed run picks up where a prior process left off.
    assert pr_number is not None
    refresh_count = _load_persisted_refresh_count(cwd, pr_number)
    refresh_history: List[Tuple[str, str]] = []
    cumulative_cost = 0.0
    last_model = "unknown"
    # External review Finding 2: carry the per-step issue-comment dedup
    # set across restart iterations so we don't re-post each step's
    # comment after ``clear_workflow_state`` wipes the stored field.
    preserved_step_comments: Set[int] = set()

    while True:
        is_restart_iteration = refresh_count > 0
        try:
            success, message, cost, model = _run_agentic_checkup_orchestrator_inner(
                issue_url=issue_url,
                issue_content=issue_content,
                repo_owner=repo_owner,
                repo_name=repo_name,
                issue_number=issue_number,
                issue_title=issue_title,
                architecture_json=architecture_json,
                pddrc_content=pddrc_content,
                cwd=cwd,
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
                # External review Finding 3: bypass load_workflow_state
                # on restarts so a flaky GH state load can't reload
                # stale cached step outputs even if clear_workflow_state's
                # DELETE silently failed.
                _force_skip_state_load=is_restart_iteration,
                # External review Finding 2: replay the previous
                # iteration's posted-step-comments set so dedup is
                # honored across restarts.
                _carried_step_comments=(
                    preserved_step_comments if is_restart_iteration else None
                ),
            )
        except _PRHeadAdvancedRestart as restart:
            cumulative_cost += restart.cost_so_far
            last_model = restart.model
            refresh_history.append((restart.old_sha, restart.new_sha))
            # External review Finding 2: capture the inner's
            # step_comments_set so the next iteration sees the same dedup
            # state and doesn't re-post comments for steps that already
            # commented on this PR.
            preserved_step_comments = set(restart.step_comments)
            # Codex round-2 Finding 1: belt-and-suspenders. The restart
            # exception already proves the head advanced; don't depend
            # on the next inner's _fetch_pr_metadata to re-prove it via
            # the SHA identity guard. A flaky refetch returning the old
            # SHA would otherwise let the inner reuse stale step
            # outputs. Clear cached workflow state outright so the next
            # iteration sets up a fresh worktree from the latest head.
            # The sidecar at .pdd/checkup-pr-{N}/pr_head_refreshes lives
            # outside workflow state, so the refresh counter survives.
            try:
                clear_workflow_state(
                    cwd=cwd,
                    issue_number=issue_number,
                    workflow_type="checkup",
                    state_dir=_get_state_dir(cwd),
                    repo_owner=repo_owner,
                    repo_name=repo_name,
                    use_github_state=use_github_state,
                )
            except Exception:  # noqa: BLE001 — best-effort
                pass
            if refresh_count >= MAX_PR_HEAD_REFRESHES:
                history_lines = ", ".join(
                    f"{old[:8]}->{new[:8]}" for old, new in refresh_history
                )
                return (
                    False,
                    (
                        f"PR head kept advancing during checkup "
                        f"({history_lines}); exhausted "
                        f"max_pr_head_refreshes={MAX_PR_HEAD_REFRESHES}. "
                        f"Rerun pdd checkup once the PR branch stabilizes."
                    ),
                    cumulative_cost,
                    last_model,
                )
            refresh_count += 1
            _save_persisted_refresh_count(cwd, pr_number, refresh_count)
            if not quiet:
                console.print(
                    f"[yellow]PR head advanced "
                    f"({restart.old_sha[:8]}->{restart.new_sha[:8]}); "
                    f"restarting from new head "
                    f"(attempt {refresh_count}/{MAX_PR_HEAD_REFRESHES}).[/yellow]"
                )
            continue
        # Inner returned normally — clear persisted counter so the next
        # checkup on this PR begins with a full budget.
        _clear_persisted_refresh_count(cwd, pr_number)
        return success, message, cumulative_cost + cost, model


def _build_state(
    issue_number: int,
    issue_url: str,
    last_completed_step: Union[int, float],
    step_outputs: Dict[str, str],
    total_cost: float,
    model_used: str,
    github_comment_id: Optional[int],
    changed_files: Optional[List[str]] = None,
    worktree_path: Optional[Path] = None,
    fix_verify_iteration: int = 0,
    previous_fixes: str = "",
    mode: str = "issue",
    pr_number: Optional[int] = None,
    pr_owner: Optional[str] = None,
    pr_repo: Optional[str] = None,
    pr_head_sha: Optional[str] = None,
    step_comments: Optional[List[int]] = None,
) -> Dict:
    """Build a serialisable state dict for persistence.

    ``mode`` is "issue" (default — TARGET-driven invocations) or "pr"
    (--pr/--issue invocations). The resume path validates that a loaded
    state's mode matches the current invocation; mismatches are treated
    as stale and force a fresh worktree setup. Without this tag, an
    issue-mode worktree could be silently reused by a subsequent PR-mode
    run on the same issue_number (or vice versa) and all steps would
    execute against the wrong code.

    ``pr_head_sha`` (codex round-1 blocker #1) records the PR head SHA the
    cached step outputs were verified against. On resume, ``run_agentic_
    checkup_orchestrator`` invalidates the cache when this differs from
    the fresh remote head SHA so a maintainer push to the PR branch
    cannot leave stale build/test/verify outputs in place.
    """
    return {
        "workflow": "checkup",
        "issue_number": issue_number,
        "issue_url": issue_url,
        "last_completed_step": last_completed_step,
        "step_outputs": step_outputs.copy(),
        "total_cost": total_cost,
        "model_used": model_used,
        "github_comment_id": github_comment_id,
        "changed_files": list(changed_files) if changed_files else [],
        "worktree_path": str(worktree_path) if worktree_path else None,
        "fix_verify_iteration": fix_verify_iteration,
        "previous_fixes": previous_fixes,
        "mode": mode,
        "pr_number": pr_number,
        "pr_owner": pr_owner,
        "pr_repo": pr_repo,
        "pr_head_sha": pr_head_sha,
        "step_comments": list(step_comments) if step_comments else [],
    }
