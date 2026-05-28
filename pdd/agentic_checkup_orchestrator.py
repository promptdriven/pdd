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
import os
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

def _get_git_root(
    cwd: Path,
    *,
    git_cmd: str = "git",
    git_env: Optional[Dict[str, str]] = None,
) -> Optional[Path]:
    """Get the root directory of the git repository."""
    try:
        result = subprocess.run(
            [git_cmd, "rev-parse", "--show-toplevel"],
            cwd=cwd,
            capture_output=True,
            env=git_env,
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


def _trusted_gate_git(worktree: Path) -> Tuple[Optional[str], Optional[Dict[str, str]]]:
    """Resolve git for gate-layer subprocesses without trusting worktree PATH."""
    from .checkup_gates import _build_subprocess_env, _resolve_trusted_git

    git_cmd = _resolve_trusted_git(worktree)
    if not git_cmd:
        return None, None
    return git_cmd, _build_subprocess_env(worktree)


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

    git_cmd, git_env = _trusted_gate_git(worktree)
    if not git_cmd or git_env is None:
        pr_metadata["base_ref_fetch_error"] = (
            "trusted git binary not found on sanitized PATH"
        )
        return

    git_root = _get_git_root(worktree, git_cmd=git_cmd, git_env=git_env)
    if not git_root:
        pr_metadata["base_ref_fetch_error"] = "worktree is not a git repository"
        return

    remote_target = _resolve_pr_remote(
        git_root,
        pr_owner,
        pr_repo,
        git_cmd=git_cmd,
        git_env=git_env,
    )
    if remote_target is None:
        remote_target = f"https://github.com/{pr_owner}/{pr_repo}.git"

    base_local_ref = _pr_base_tracking_ref(pr_number)
    try:
        # Bounded timeout so a stalled transport (auth prompt, dead
        # remote, transient hang) cannot hold the review loop forever.
        # The deterministic-gate layer's own ``gate_timeout`` does not
        # apply to this fetch because the fetch runs BEFORE gate
        # discovery. 60s matches the default per-gate timeout so the
        # operator sees a single consistent upper bound.
        subprocess.run(
            [
                git_cmd,
                "fetch",
                remote_target,
                f"refs/heads/{base_ref}:{base_local_ref}",
                "--force",
            ],
            cwd=git_root,
            capture_output=True,
            env=git_env,
            text=True,
            check=True,
            timeout=60,
        )
    except subprocess.TimeoutExpired:
        # Surface as ``base_ref_fetch_error`` so the review loop's
        # ``_enforce_gates_before_clean`` converts it into a synthetic
        # ``gate:base-ref`` blocker finding (iter-19 fail-closed path).
        # Without this branch a timeout would leak as an unhandled
        # ``TimeoutExpired`` from ``_refresh_pr_base_ref`` and the loop
        # would abort with a stack trace instead of a clean refusal.
        pr_metadata["base_ref_fetch_error"] = (
            f"git fetch timed out after 60s for base ref {base_ref!r}"
        )
        if not quiet:
            console.print(
                f"[yellow]Warning: PR base ref fetch timed out: "
                f"{pr_metadata['base_ref_fetch_error']}[/yellow]"
            )
        return
    except subprocess.CalledProcessError as exc:
        # Env-token redaction alone is insufficient.
        # Git stderr on a failed fetch can carry
        # credentials that did NOT come from the process env — a
        # credential-helper-supplied PAT, a GitHub App installation
        # token minted at runtime, a remote URL with embedded
        # `https://<user>:<token>@host` basic-auth, or a `Bearer`
        # header from a verbose transport. The console.print and
        # `pr_metadata["base_ref_fetch_error"]` surfaces both flow
        # into long-term log capture (rich console → stdout → CI
        # log) and the rendered checkup report. Scrub through the
        # full regex catch-all BEFORE either surface sees the
        # string. Keep the env-token `_redact_secret` pass for
        # belt-and-braces: regex patterns are best-effort and a
        # token that does not match a known shape (e.g. a 16-char
        # custom internal token) still falls through; the explicit
        # secret subtraction guarantees the env value is gone.
        raw_err = (exc.stderr or str(exc)).strip()
        safe_err = _scrub_secrets(raw_err)
        token = _github_token_from_env()
        if token:
            safe_err = _redact_secret(safe_err, token)
        # The remote URL fallback `https://github.com/<owner>/<repo>.git`
        # is non-sensitive, but a configured remote NAME may also be
        # echoed verbatim. Names are not secret. URLs WITH embedded
        # credentials would have been caught above by the regex
        # patterns (`ghp_`/`ghs_`/`gho_`/…) and the env-token strip.
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
    *,
    git_cmd: str = "git",
    git_env: Optional[Dict[str, str]] = None,
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
            [git_cmd, "remote", "-v"],
            cwd=git_root,
            capture_output=True,
            env=git_env,
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


# Codex round-3 Finding 5: diff size sanity gate. A fixer push that adds
# more than ``DIFF_SIZE_ADDED_LOC_LIMIT`` lines without an explicit
# EXPANSION_ITEMS justification is treated as an oversized change and
# refused. Threshold chosen as a deliberate conservative ceiling tied to a
# typical bug-fix surface — larger fixes should declare themselves via
# EXPANSION_ITEMS so the operator can see the scope expansion. Override via
# the ``PDD_CHECKUP_DIFF_LOC_LIMIT`` env var (positive int; falls back to
# the default on parse error). Set to ``0`` to disable the gate entirely.
DIFF_SIZE_ADDED_LOC_LIMIT = 800

# Codex round-9 Finding 2: a path is treated as "oversized" — and
# therefore required to carry its OWN justified EXPANSION_ITEMS entry
# when the total diff exceeds ``DIFF_SIZE_ADDED_LOC_LIMIT`` — when its
# added lines alone meet or exceed this floor. Small companion edits
# (e.g. a 5-line test update next to a 600-line refactor) are exempt:
# the docs and Step 6 prompt both promise "every oversized dirty path",
# not "every dirty path".
OVERSIZED_PATH_ADDED_LOC_FLOOR = 50


def _diff_size_added_lines_by_path(worktree: Path) -> Optional[Dict[str, int]]:
    """Return per-path added line counts for uncommitted + untracked files.

    Same probe shape as :func:`_diff_size_added_lines` (which delegates to
    this helper for the total) but reports the count per file so the
    pre-push gate can isolate which paths individually pushed the diff
    over the limit. ``None`` indicates the git probe itself failed —
    callers fail-degrade rather than blocking pushes on a flaky git
    invocation.
    """
    try:
        from .checkup_gates import (  # pylint: disable=import-outside-toplevel
            _build_subprocess_env,
            _resolve_trusted_git,
        )

        git_bin = _resolve_trusted_git(worktree)
        if not git_bin:
            return None
        env = _build_subprocess_env(worktree)
        result = subprocess.run(
            [git_bin, "diff", "--numstat", "HEAD"],
            cwd=str(worktree),
            env=env,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
        if result.returncode != 0:
            return None
        per_path: Dict[str, int] = {}
        for line in result.stdout.splitlines():
            parts = line.split("\t")
            if len(parts) < 3:
                continue
            added_field = parts[0].strip()
            path_field = parts[-1].strip()
            if not path_field:
                continue
            # Rename rows look like ``10\t5\told -> new``; the destination
            # is what's in the working tree, so prefer the post-rename
            # path for matching against ``guard_changed_files``.
            if " -> " in path_field:
                path_field = path_field.split(" -> ", 1)[1].strip()
            if added_field in ("", "-"):
                # Binary files contribute zero; still record so the gate
                # sees the path.
                per_path[path_field] = per_path.get(path_field, 0)
                continue
            try:
                per_path[path_field] = per_path.get(path_field, 0) + int(added_field)
            except ValueError:
                continue

        untracked = subprocess.run(
            [git_bin, "ls-files", "--others", "--exclude-standard"],
            cwd=str(worktree),
            env=env,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
        if untracked.returncode == 0:
            for path in untracked.stdout.splitlines():
                rel = path.strip()
                if not rel:
                    continue
                full = worktree / rel
                try:
                    if full.is_file():
                        with full.open("rb") as fh:
                            per_path[rel] = per_path.get(rel, 0) + sum(1 for _ in fh)
                except OSError:
                    continue
        return per_path
    except (subprocess.TimeoutExpired, OSError):
        return None


def _diff_size_added_lines(worktree: Path) -> Optional[int]:
    """Return total added lines across uncommitted + untracked files.

    Uses ``git diff --numstat`` to count added lines in tracked changes,
    then adds the line counts of untracked files (numstat ignores them).
    Binary files report ``-`` in numstat output and contribute zero.

    Returns ``None`` when the git probe fails, so callers fail-degrade
    rather than blocking pushes on a flaky git invocation.
    """
    per_path = _diff_size_added_lines_by_path(worktree)
    if per_path is None:
        return None
    return sum(per_path.values())


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


def _scrub_secrets(text: str) -> str:
    """Lazy wrapper around the review-loop regex secret scrubber.

    `_refresh_pr_base_ref` previously redacted
    only the env-derived GitHub token before publishing fetch stderr to the
    console and `pr_metadata`. Tokens that travel via git credential helper,
    a GitHub App installation token minted at runtime, or an embedded
    `x-access-token:...@github.com` in a remote URL would all slip through.
    Pipe the stderr through this regex catch-all (covers `ghp_`/`ghs_`/`gho_`,
    `sk-...`, `Bearer`/`Authorization` headers, AWS access keys, Slack
    tokens, and the common `https://<user>:<token>@host` URL shape) before
    any console.print or `pr_metadata` storage.
    """
    from .checkup_review_loop import (  # pylint: disable=import-outside-toplevel
        _scrub_secrets as fn,
    )

    return fn(text)


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


_STEP5_SKIPPED_STATUSES = frozenset({"skipped", "skip", "no_tests", "n/a", "n_a"})


def _step5_failure_signal_status(step_output_value: str) -> str:
    """Return the lowercase ``failure_signal.status`` from a Step 5 output.

    Strips a leading ``"FAILED: "`` prefix that ``_handle_step_result``
    prepends for failed steps, then delegates to
    :func:`_parse_failure_signal_block`. Returns ``""`` when no status
    is present.

    Codex round-10 Finding 3: the orchestrator must be able to derive
    Step 5's logical outcome at any point in the run — including on
    resume — from the persisted ``step_outputs["5"]`` value alone,
    without depending on the in-memory ``context`` cache that is not
    part of the saved workflow state.
    """
    if not step_output_value:
        return ""
    body = step_output_value
    if body.startswith("FAILED: "):
        body = body[len("FAILED: "):]
    fields, _ = _parse_failure_signal_block(body)
    return str(fields.get("status", "")).strip().lower()


def _step5_was_skipped(step_output_value: str) -> bool:
    """Return True when Step 5 reported a ``skipped``-family status.

    Independent of provider success (round-10 Finding 1) — an agent
    that emitted a coherent ``status: skipped`` block even on a failed
    provider call still means "tests did not run", and the pre-push
    gate must refuse the push regardless.
    """
    return _step5_failure_signal_status(step_output_value) in _STEP5_SKIPPED_STATUSES


_EXPANSION_CAUSAL_KEYWORDS = (
    "because",
    "broken by",
    "caused by",
    "depends on",
    "required by",
    "needed for",
    "needed because",
    "blocked by",
    "fails because",
    "breaks because",
    "due to",
    "triggered by",
    "imports",
    "uses",
    "regression in",
)


def _parse_expansion_items(step6_output: str) -> Tuple[set, set]:
    """Parse the ``EXPANSION_ITEMS:`` allowlist from Step 6 output.

    Returns ``(paths, justified_paths)``:
      - ``paths``: the set of all file paths explicitly listed on
        ``EXPANSION_ITEMS:`` lines.
      - ``justified_paths``: the subset of ``paths`` whose own marker
        carried a causal justification — either inline on the marker
        line (``: <paths> — <reason>``) or as trailing prose lines
        beneath the marker block.

    Codex round-5 Finding 3: justification must be tracked per marker
    entry, not globally. A fixer can otherwise list an unrelated path on
    one ``EXPANSION_ITEMS:`` line and then satisfy the justification
    check with a *different* justified marker entry, bypassing the
    out-of-scope guard for the unrelated path.
    """
    paths: set = set()
    justified_paths: set = set()
    if "EXPANSION_ITEMS:" not in step6_output:
        return paths, justified_paths

    lines = step6_output.splitlines()
    for idx, line in enumerate(lines):
        stripped = line.strip()
        if not stripped.startswith("EXPANSION_ITEMS:"):
            continue
        payload = stripped.split(":", 1)[1].strip()
        # Allow an inline justification after an em-dash, hyphen, or
        # "because"/"reason"-style suffix on the same line:
        #   EXPANSION_ITEMS: tests/test_x.py — broken by core.py change
        inline_paths = payload
        inline_reason = ""
        for sep in (" — ", " -- ", " - ", " because ", " reason: "):
            if sep in payload:
                inline_paths, _, inline_reason = payload.partition(sep)
                break
        # Per-marker justification segments accumulate ONLY for this
        # marker so a sibling marker's reason cannot whitelist the paths
        # listed here.
        marker_segments: List[str] = []
        if inline_reason.strip():
            marker_segments.append(inline_reason.strip())
        # Treat ``none`` / ``n/a`` / empty payload as no expansion.
        marker_paths: set = set()
        if inline_paths and inline_paths.lower() not in ("none", "n/a", "-"):
            for token in inline_paths.replace(";", ",").split(","):
                cleaned = token.strip().strip("`'\"")
                # Skip obvious non-path fragments (sentences, parentheticals).
                if not cleaned:
                    continue
                if " " in cleaned and "/" not in cleaned and "\\" not in cleaned:
                    # Reads like prose, not a path — drop it.
                    marker_segments.append(cleaned)
                    continue
                marker_paths.add(cleaned)
        # Pull a few trailing non-empty lines as potential justification
        # text so a multi-line block of reasoning still satisfies the
        # justification requirement. Codex round-6 Finding 1 / round-7
        # Finding 1: arbitrary trailing prose (e.g. a closing "All done."
        # sentence) used to qualify as justification on length alone,
        # letting the fixer bypass scope by emitting any marker plus any
        # padding text. Round-6 tried to fix this by treating indented
        # or bulleted continuations as inherently per-marker — but that
        # is still bypassable with "  All done." or "- All done.". The
        # tightened rule requires SEMANTIC content: a line counts as a
        # per-marker justification only when it carries a JUSTIFICATION:
        # /REASON:/BECAUSE: prefix, mentions one of the marker's own
        # paths (full path or basename), or contains a causal keyword.
        # Bare indentation/bullets without those signals no longer
        # qualifies.
        marker_path_tokens: set = set()
        for path in marker_paths:
            marker_path_tokens.add(path)
            tail = path.rsplit("/", 1)[-1]
            if tail:
                marker_path_tokens.add(tail)
        for follow in lines[idx + 1: idx + 6]:
            follow_stripped = follow.strip()
            if not follow_stripped:
                continue
            if follow_stripped.startswith("EXPANSION_ITEMS:"):
                break
            if follow_stripped.startswith(("FILES_", "PATTERN_", "FIX_")):
                break
            # Strip a leading bullet/blockquote marker so the semantic
            # checks below see the actual content (mentions/keyword) of
            # a "- because foo broke" continuation.
            content = follow_stripped
            for bullet in ("- ", "* ", "+ ", "> "):
                if content.startswith(bullet):
                    content = content[len(bullet):].strip()
                    break
            lowered = content.lower()
            has_prefix = lowered.startswith(
                ("justification:", "reason:", "because:", "rationale:", "why:")
            )
            mentions_path = any(tok in content for tok in marker_path_tokens)
            has_causal_keyword = any(
                kw in lowered for kw in _EXPANSION_CAUSAL_KEYWORDS
            )
            if not (has_prefix or mentions_path or has_causal_keyword):
                # Trailing prose without semantic per-marker content
                # (even when indented or bulleted) — not a justification.
                continue
            marker_segments.append(content)

        paths.update(marker_paths)
        marker_has_justification = any(
            len(seg) >= 8 for seg in marker_segments
        )
        if marker_has_justification:
            justified_paths.update(marker_paths)

    return paths, justified_paths


_FAILURE_SIGNAL_REQUIRED_KEYS = (
    "command",
    "exit_code",
    "status",
    "failing_ids",
    "artifact_path",
    "output",
)


def _extract_failure_signal_block(step5_output: str) -> Optional[str]:
    """Return the raw text inside a `````failure_signal`` fenced block.

    Returns the body (without the fences) when found, otherwise ``None``.
    Only the LAST such block is returned — the Step 5 prompt requires the
    block to be the final fenced block of the response.
    """
    if not step5_output or "failure_signal" not in step5_output:
        return None
    matches = list(
        re.finditer(
            r"```failure_signal\s*\n(.*?)```",
            step5_output,
            flags=re.DOTALL,
        )
    )
    if not matches:
        return None
    return matches[-1].group(1)


def _parse_failure_signal_block(step5_output: str) -> Tuple[Dict[str, str], List[str]]:
    """Parse the structured failure_signal block from Step 5 output.

    Returns ``(fields, missing)``:
      - ``fields``: dict of recognised keys. Missing keys are absent. The
        ``output:`` value collects the indented block under the key (each
        leading two-space indent is stripped) per the prompt's YAML-ish
        shape.
      - ``missing``: ordered list of REQUIRED keys not present in the block
        (or with empty values for required-non-empty keys like ``status``
        and ``command``). When the block itself is missing,
        ``missing == ["__block__"]``.

    Round-2 Finding 5: the prompt says Step 5 MUST emit this block and
    that Step 6 rejects failures without it, but no parsing/validation
    existed. This helper lets the orchestrator detect missing/malformed
    blocks and synthesise a normalised structured block for Step 6.
    """
    body = _extract_failure_signal_block(step5_output)
    if body is None:
        return {}, ["__block__"]

    fields: Dict[str, str] = {}
    current_key: Optional[str] = None
    indented_lines: List[str] = []

    def _commit_block_value() -> None:
        if current_key is None:
            return
        fields[current_key] = "\n".join(indented_lines).rstrip()

    for raw_line in body.splitlines():
        line = raw_line.rstrip()
        if not line:
            if current_key is not None and indented_lines:
                indented_lines.append("")
            continue
        # Recognise ``key: value`` at column 0 (or with ``  key:`` indent
        # styling tolerated). A continuation of a block scalar is any
        # line that starts with whitespace.
        match = re.match(r"^([A-Za-z_]+)\s*:\s*(.*)$", line)
        if match and not raw_line.startswith((" ", "\t")):
            _commit_block_value()
            current_key = match.group(1).strip().lower()
            value = match.group(2).rstrip()
            if value == "|":
                # Block-scalar follows on subsequent indented lines.
                fields[current_key] = ""
                indented_lines = []
            else:
                fields[current_key] = value
                current_key = None
                indented_lines = []
        else:
            if current_key is not None:
                stripped = raw_line[2:] if raw_line.startswith("  ") else raw_line
                indented_lines.append(stripped)
    _commit_block_value()

    missing: List[str] = []
    status_value = str(fields.get("status", "")).strip().lower()
    # Codex round-3 Finding 4: when the status indicates a real failure
    # (``fail``/``error``) Step 6 needs concrete debugging context — exit
    # code, failing IDs, an artifact pointer, and at least some output to
    # reason from. A block that lists those keys with empty values is just
    # as useless as one that omits them, so promote them to ``missing``.
    failure_statuses = {"fail", "error", "failed", "failure"}
    failure_required_non_empty = {
        "exit_code",
        "failing_ids",
        "artifact_path",
        "output",
    }
    for key in _FAILURE_SIGNAL_REQUIRED_KEYS:
        if key not in fields:
            missing.append(key)
            continue
        value = str(fields[key]).strip()
        if key in ("command", "status") and not value:
            missing.append(key)
            continue
        if status_value in failure_statuses and key in failure_required_non_empty and not value:
            # ``failing_ids`` may legitimately be empty when the runner
            # cannot enumerate the IDs; the prompt instructs Step 5 to
            # write ``none`` or a synthetic identifier in that case, so an
            # empty value here is still treated as missing context.
            missing.append(key)
    return fields, missing


_ARTIFACT_OUTPUT_MAX_LINES = 400
_ARTIFACT_OUTPUT_MAX_BYTES = 256 * 1024
# Codex round-6 performance: cap raw bytes pulled off disk before scrubbing.
# Tokens are short (~40 chars) so 16x headroom is more than enough to keep any
# secret intact across the read boundary, while preventing a pathological pytest
# log (hundreds of MB) from spiking orchestrator memory.
_ARTIFACT_READ_MAX_BYTES = _ARTIFACT_OUTPUT_MAX_BYTES * 16


def _read_failure_signal_artifact(
    artifact_path_value: str,
    worktree_path: Optional[Path],
) -> Optional[str]:
    """Read the Step 5 failure log when it lives in ``artifact_path``.

    Codex round-4 Finding 3: Step 5 is allowed to leave ``output:`` empty
    when ``artifact_path:`` points at a file on disk that holds the full
    pytest log. The previous orchestrator never read that file, so Step 6
    received an empty ``output:`` payload and the entire failure detail
    was lost. Resolves the path under the PR worktree, refuses to escape
    it, caps the content to keep the prompt bounded, and scrubs secrets.

    Returns ``None`` when the value is empty, sentinel ("inline"/"none"),
    not a regular file under the worktree, or unreadable.
    """
    value = (artifact_path_value or "").strip()
    if not value or value.lower() in {"inline", "none", "n/a", "-", "missing"}:
        return None
    if worktree_path is None:
        return None
    try:
        worktree_resolved = worktree_path.resolve()
        candidate = Path(value)
        if not candidate.is_absolute():
            candidate = worktree_resolved / candidate
        candidate_resolved = candidate.resolve()
    except (OSError, RuntimeError):
        return None
    # Refuse paths that escape the worktree — Step 5 controls this value
    # and a hostile or buggy run could otherwise hand Step 6 secrets from
    # outside the PR scope (e.g. ``/etc/passwd``, ``~/.netrc``).
    try:
        candidate_resolved.relative_to(worktree_resolved)
    except ValueError:
        return None
    if not candidate_resolved.is_file():
        return None
    try:
        # Read at most _ARTIFACT_READ_MAX_BYTES + 1 so callers can detect
        # raw-side truncation without materialising arbitrarily large logs.
        with candidate_resolved.open("rb") as fh:
            raw_bytes = fh.read(_ARTIFACT_READ_MAX_BYTES + 1)
    except OSError:
        return None
    raw_truncated = len(raw_bytes) > _ARTIFACT_READ_MAX_BYTES
    if raw_truncated:
        raw_bytes = raw_bytes[:_ARTIFACT_READ_MAX_BYTES]
    # Codex round-5 Finding 4: decode AND scrub the full artifact body
    # before any truncation. Slicing raw bytes first leaves a
    # recognisable ``ghp_AB...`` fragment when a token straddles the
    # byte cutoff — the scrub regex never sees the full token, so it
    # cannot redact the fragment. Scrub everything, then truncate the
    # already-safe text.
    full_text = raw_bytes.decode("utf-8", errors="replace")
    token = _github_token_from_env()

    def _scrub(value: str) -> str:
        scrubbed_value = _scrub_secrets(value)
        if token:
            scrubbed_value = _redact_secret(scrubbed_value, token)
        return scrubbed_value

    scrubbed_full = _scrub(full_text)
    scrubbed_lines = scrubbed_full.splitlines()
    truncated_lines = scrubbed_lines[:_ARTIFACT_OUTPUT_MAX_LINES]
    body = "\n".join(truncated_lines)
    if len(body.encode("utf-8", errors="replace")) > _ARTIFACT_OUTPUT_MAX_BYTES:
        body_bytes = body.encode("utf-8", errors="replace")[:_ARTIFACT_OUTPUT_MAX_BYTES]
        body = body_bytes.decode("utf-8", errors="replace")
    needs_truncation_note = (
        raw_truncated
        or len(raw_bytes) > _ARTIFACT_OUTPUT_MAX_BYTES
        or len(scrubbed_lines) > _ARTIFACT_OUTPUT_MAX_LINES
    )
    truncation_note = ""
    if needs_truncation_note:
        # Scrub the artifact path before echoing it back — a hostile or
        # buggy run could embed a token in the directory name.
        safe_path = _scrub(value)
        truncation_note = (
            "\n# orchestrator-note: artifact truncated for prompt "
            f"budget (cap: {_ARTIFACT_OUTPUT_MAX_LINES} lines / "
            f"{_ARTIFACT_OUTPUT_MAX_BYTES} bytes; full log at "
            f"{safe_path})."
        )
    return body + truncation_note


def _normalised_failure_signal_text(
    raw_output: str,
    fields: Dict[str, str],
    missing: List[str],
) -> str:
    """Return a normalised structured block for downstream prompts.

    When the Step 5 agent omits or paraphrases the ``failure_signal``
    block we still want to hand Step 6 a structured representation
    instead of letting it invent context (which is what caused the
    original hallucinated-fix mode). Falls back to a synthesised block
    that captures the raw output verbatim and flags the missing keys.
    """
    if not missing:
        rendered = "\n".join(
            f"{key}: {fields.get(key, '')}"
            for key in _FAILURE_SIGNAL_REQUIRED_KEYS
            if key != "output"
        )
        rendered += "\noutput: |\n"
        body = fields.get("output", "")
        for body_line in body.splitlines() or [""]:
            rendered += f"  {body_line}\n"
        return f"```failure_signal\n{rendered.rstrip()}\n```"

    # Synthesise: pull any fields we did parse; mark the rest as MISSING.
    parts = []
    for key in _FAILURE_SIGNAL_REQUIRED_KEYS:
        if key == "output":
            continue
        value = fields.get(key)
        if value is None or (key in ("command", "status") and not str(value).strip()):
            value = "MISSING"
        parts.append(f"{key}: {value}")
    rendered = "\n".join(parts)
    raw_body = fields.get("output") or raw_output or ""
    rendered += "\noutput: |\n"
    for body_line in (raw_body.splitlines() or [""])[:200]:
        rendered += f"  {body_line}\n"
    rendered += (
        "\n# orchestrator-note: Step 5 emitted a non-compliant "
        f"failure_signal block (missing/empty keys: {sorted(missing)}). "
        "Raw step output is preserved above for Step 6."
    )
    return f"```failure_signal\n{rendered.rstrip()}\n```"


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
    git_cmd, git_env = _trusted_gate_git(worktree)
    if not git_cmd or git_env is None:
        return api_fallback or (
            "PR changed files unavailable: trusted git binary was not found "
            "on the sanitized PATH. Run targeted tests conservatively."
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
                [git_cmd, "rev-parse", "--verify", base],
                cwd=worktree,
                capture_output=True,
                env=git_env,
                text=True,
            )
        except (OSError, subprocess.SubprocessError):
            continue
        if verify.returncode != 0:
            continue

        try:
            diff = subprocess.run(
                [
                    git_cmd,
                    "diff",
                    "--name-status",
                    "--find-renames",
                    f"{base}...HEAD",
                ],
                cwd=worktree,
                capture_output=True,
                env=git_env,
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
        # Codex round-4 Finding 2: ``pr_changed_files`` is a test-selection
        # signal (only populated when ``pr_test_scope == 'targeted'`` so
        # Step 5 runs a focused subset). ``pr_scope_changed_files`` is the
        # FIXER scope signal — Step 6 uses it to constrain edits to the
        # PR's existing changed-file set regardless of test scope. We
        # populate it unconditionally in PR mode so the prompt scope guard
        # holds even when the operator runs the default ``--scope full``.
        "pr_scope_changed_files": "",
        "pr_test_scope": pr_test_scope,
        "manual_start_step": str(start_step_override or ""),
        "worktree_path": "",
        "files_to_stage": "",
        "fix_verify_iteration": "1",
        "max_fix_verify_iterations": str(MAX_FIX_VERIFY_ITERATIONS),
        "previous_fixes": "",
        # Codex round-3 Finding 3: initialise the normalised Step 5
        # failure_signal slots so the Step 6 prompt (which now references
        # ``{step5_failure_signal}``) always renders, even when Step 5
        # succeeded or has not run yet.
        "step5_failure_signal": "",
        "step5_failure_signal_missing": "",
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

    # Issue #1116 round-5 Finding 2: fix mode (no_fix=False) requires a
    # known entry head SHA. All four fix-mode freshness checkpoints
    # (A, A2, B, D) gate on a non-empty ``current_pr_head_sha`` — with an
    # empty baseline they all skip, leaving a stale-verdict hole if the
    # remote advances mid-run. Fail-closed at entry instead, mirroring
    # the --no-fix round-3 precedent (the --no-fix path detects the same
    # condition after Step 7). The user retries once gh recovers.
    #
    # ``_force_skip_state_load`` (set by the outer wrapper on restart
    # iterations) means we already discarded prior state — so an empty
    # SHA here is a fresh transient failure, not a resumed run. Either
    # way, the outer wrapper does not retry on a plain return; it returns
    # the message to the caller (pdd-issue / pdd_cloud).
    if pr_mode and not no_fix and not current_pr_head_sha:
        if not quiet:
            console.print(
                f"[red]PR #{pr_number}: could not determine entry head "
                f"SHA via _fetch_pr_metadata (transient gh / network "
                f"failure). Fix-mode checkup needs a known baseline to "
                f"validate freshness before pushing. Rerun pdd checkup "
                f"--pr once gh recovers.[/red]"
            )
        return (
            False,
            (
                f"Could not determine entry PR head SHA for PR "
                f"#{pr_number}; fix-mode freshness lease requires a "
                f"baseline. Rerun pdd checkup --pr."
            ),
            total_cost,
            last_model_used,
        )

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
                # Codex round-4 Finding 2: always populate the fixer scope
                # placeholder so Step 6's scope guard holds in full mode
                # too. ``pr_changed_files`` stays gated on ``targeted`` so
                # Step 5's test-selection contract is unchanged.
                pr_scope_files_text = _format_pr_changed_files_for_prompt(
                    worktree_path,
                    metadata_for_guard,
                )
                context["pr_scope_changed_files"] = pr_scope_files_text
                if pr_test_scope == "targeted":
                    context["pr_changed_files"] = pr_scope_files_text

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

        # Round-2 Finding 4 + codex round-5 Finding 2: scrub Step 5
        # output BEFORE every persistence surface, on ALL result paths.
        # The provider-success/tests-failing path is the common case in
        # CI — failure_signal blocks frequently embed redacted-looking
        # but actually-live tokens (curl headers, env exports, CI logs).
        # Scrubbing only when ``not success`` leaked credentials into
        # ``context['step5_output']``, ``step_outputs['5']``, and any
        # per-step GitHub comment whenever the provider call itself
        # completed normally.
        persistable_output = output
        if step_num == 5 and output:
            persistable_output = _scrub_secrets(output)
            token = _github_token_from_env()
            if token:
                persistable_output = _redact_secret(persistable_output, token)

        context[f"step{step_key}_output"] = persistable_output

        # Steps 6.1/6.2/6.3: parse changed files.
        if step_num in (6.1, 6.2, 6.3) and success:
            extracted_files = _parse_changed_files(output)
            changed_files.extend(extracted_files)
            # Deduplicate preserving order
            changed_files[:] = list(dict.fromkeys(changed_files))
            context["files_to_stage"] = ", ".join(changed_files)

        if not success:
            if not quiet:
                console.print(
                    f"[yellow]Warning: Step {step_num} reported failure, "
                    f"but proceeding as no hard stop condition met.[/yellow]"
                )
            # Always surface Step 5 failure detail — visible even in quiet mode.
            # ``persistable_output`` is already scrubbed when step_num == 5.
            if step_num == 5 and persistable_output:
                console.print(
                    f"[yellow]Step 5 failure detail:\n{persistable_output}[/yellow]"
                )
        elif not quiet:
            console.print(f"  -> Step {step_num} complete.")

        if success:
            step_outputs[step_key] = persistable_output
            last_completed_step_to_save = step_num
            consecutive_provider_failures = 0
            if description:
                _maybe_post_step_comment(step_num, description, persistable_output, iteration)
        else:
            step_outputs[step_key] = f"FAILED: {persistable_output}"
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
        # Codex round-4 Finding 2: always populate the fixer scope
        # placeholder so Step 6's scope guard holds in the default full
        # mode. The targeted test-selection placeholder
        # (``pr_changed_files``) remains opt-in.
        pr_scope_files_text = _format_pr_changed_files_for_prompt(
            worktree_path,
            metadata_for_guard,
        )
        context["pr_scope_changed_files"] = pr_scope_files_text
        if pr_test_scope == "targeted":
            context["pr_changed_files"] = pr_scope_files_text

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

        # --no-fix --pr Step 5 status gate (issue #1212 round-14):
        # Runs AFTER the 3/4/5 loop so it covers both fresh runs (Step 5
        # just executed) and resumed runs (Step 5 skipped via start_step
        # but output is already in step_outputs from loaded state).
        # Non-PR no-fix runs are unaffected (pr_mode is False).
        if pr_mode:
            _s5_raw = step_outputs.get("5", "") or context.get("step5_output", "") or ""
            if _s5_raw:
                _s5f, _s5m = _parse_failure_signal_block(_s5_raw)
                _s5v = str(_s5f.get("status", "")).strip().lower()
                _s5_block_missing = "__block__" in _s5m
                _s5_skipped = _s5v in _STEP5_SKIPPED_STATUSES
                _s5_pass = _s5v in {"pass", "ok", "success", "passed", "clean"}
                _s5_fail = (
                    _s5v in {"fail", "error", "failed", "failure"}
                    or _s5_block_missing
                    or (not _s5_pass and not _s5_skipped)
                )
                if _s5_skipped or _s5_fail:
                    _art = cwd / ".pdd" / f"checkup-pr-{pr_number}"
                    _art.mkdir(parents=True, exist_ok=True)
                    if _s5_skipped:
                        _nofix_refusal = (
                            "Step 5 reported status: skipped — tests did not "
                            "run against the PR head. Refusing to report a "
                            "verified result. Rerun pdd checkup --pr --no-fix "
                            "once the test environment is healthy."
                        )
                        (_art / "nofix-step5-skipped-refusal.txt").write_text(
                            _nofix_refusal + "\n"
                        )
                    else:
                        _s5_sfx = (
                            " (failure_signal block missing or malformed)"
                            if _s5_block_missing
                            else f" (status: {_s5v!r})"
                        )
                        _nofix_refusal = (
                            f"Step 5 reported a test failure{_s5_sfx}. "
                            "Rerun pdd checkup --pr --no-fix after addressing "
                            "the failures."
                        )
                        (_art / "nofix-step5-failure-refusal.txt").write_text(
                            _nofix_refusal + "\n"
                        )
                    return (False, _nofix_refusal, total_cost, last_model_used)

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
        # head before publishing the canonical verification report.
        # Fail-closed on THREE conditions (no rerun budget consumed — the
        # lease is fix-mode only by design):
        #   • advance confirmed     (fresh_sha != entry_sha, both non-empty)
        #   • post-run unknown      (refetch failed / returned empty sha)
        #   • pre-run unknown       (entry sha was empty — we never had a
        #                            baseline to compare against, so we
        #                            cannot certify the Step 7 verdict ran
        #                            against the head we're about to post)
        # Issue #1116 round-4 (entry-SHA gap): a transient entry-side
        # _fetch_pr_metadata failure must NOT later be hidden by a working
        # post-run fetch. If we never had an entry SHA, freshness is
        # unverifiable in either direction.
        if pr_mode and worktree_path is not None and no_fix and nofix_gate_passed:
            assert pr_owner is not None and pr_repo is not None
            assert pr_number is not None
            try:
                nofix_fresh_metadata = _fetch_pr_metadata(pr_owner, pr_repo, pr_number)
            except Exception:  # noqa: BLE001
                nofix_fresh_metadata = {}
            nofix_fresh_sha = str(
                (nofix_fresh_metadata or {}).get("head_sha", "") or ""
            )
            if not nofix_fresh_sha:
                stale_msg = (
                    f"--no-fix verification on PR #{pr_number} completed a "
                    f"clean Step 7 but the post-run freshness check failed "
                    f"(could not retrieve the current PR head SHA). "
                    f"Verdict treated as unverified; rerun pdd checkup --pr "
                    f"--no-fix."
                )
            elif not current_pr_head_sha:
                stale_msg = (
                    f"--no-fix verification on PR #{pr_number} produced a "
                    f"clean Step 7 verdict but the entry PR head SHA was "
                    f"unavailable (the initial _fetch_pr_metadata returned "
                    f"empty), so freshness against the post-run head "
                    f"({nofix_fresh_sha[:8]}) cannot be confirmed. Verdict "
                    f"treated as unverified; rerun pdd checkup --pr --no-fix."
                )
            elif nofix_fresh_sha != current_pr_head_sha:
                stale_msg = (
                    f"--no-fix verification on PR #{pr_number} produced a "
                    f"clean Step 7 verdict but the PR head advanced during "
                    f"the run ({current_pr_head_sha[:8]}->{nofix_fresh_sha[:8]}). "
                    f"Verdict treated as unverified; rerun pdd checkup --pr "
                    f"--no-fix."
                )
            else:
                stale_msg = None
            if stale_msg is not None:
                if not quiet:
                    console.print(f"[red]{stale_msg}[/red]")
                # Include the downgrade reason in the posted report body so
                # the PR/issue thread shows WHY the verdict was invalidated,
                # not just the clean Step 7 output that no longer applies.
                stale_report_body = (
                    f"**Verdict downgraded — unverified:**\n\n{stale_msg}"
                    f"\n\n---\n\n{nofix_step7_output}"
                )
                stale_post_suffix = _post_pr_mode_final_report(stale_report_body)
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

        # Codex round-3 Finding 2: track whether the fixer (Steps 6.1/6.2/6.3)
        # ever actually ran. Defaults to False so that a clean-run PR (Steps
        # 3/4/5 all clean) cannot push side-effect edits left in the worktree
        # by other steps or tooling. Non-PR mode skips the side-effect refusal
        # path entirely (regular checkup commits its fixes the usual way).
        #
        # Codex round-6 Finding 3 / round-7 Finding 2: a resume that skips
        # ahead bypasses the assignment that would otherwise flip the
        # flag — without honouring persisted fixer state the side-effect
        # guard would refuse the dirty changes the previous run's fixer
        # produced. Seed ONLY from persisted ``step_outputs`` so a manual
        # ``--start-step 7`` (no prior fixer execution, no persisted 6_x
        # outputs) does NOT bypass the side-effect guard for dirty files
        # left by tooling. The earlier ``or start_step > 6`` clause made
        # that bypass possible.
        fixer_invoked = any(
            k in step_outputs for k in ("6_1", "6_2", "6_3")
        )

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
            # Bug 5a: track per-step success of the discovery/build/interface/
            # test signals. The fixer (6.1/6.2/6.3) is skipped in PR mode only
            # when ALL of them are clean — Steps 3 and 4 can fail before Step
            # 5 succeeds and Step 6 is the right place to fix those failures.
            #
            # Round-2 Finding 3: when resuming mid-loop (start_step > 3),
            # initialise the clean flags from the persisted ``step_outputs``
            # so a clean Step 3/4/5 cached before the interruption is not
            # forgotten. Without this, a resume after a clean Step 5 reentered
            # the fixer with all three flags False and hallucinated changes,
            # recreating the non-convergent clean-run bug. ``step_outputs[K]``
            # stores raw success output for clean steps and ``FAILED: …`` for
            # failures (see ``_handle_step_result``).
            def _cached_clean(key: str) -> bool:
                cached = step_outputs.get(key)
                if not cached:
                    return False
                return not cached.startswith("FAILED:")

            step3_clean = (
                is_first_loop_pass
                and start_step > 3
                and _cached_clean("3")
            )
            step4_clean = (
                is_first_loop_pass
                and start_step > 4
                and _cached_clean("4")
            )
            step5_clean = (
                is_first_loop_pass
                and start_step > 5
                and _cached_clean("5")
            )

            for step_num, name, description in loop_steps:
                # On first pass through the loop, honour resume (skip
                # already-done steps). Subsequent iterations run all steps.
                if is_first_loop_pass and step_num < start_step:
                    continue

                # Bug 5a: Skip fixer steps only when Steps 3, 4, AND 5 are all
                # clean (PR mode only). In regular mode, the fixer always
                # runs regardless of the upstream signals.
                if (
                    pr_mode
                    and step3_clean
                    and step4_clean
                    and step5_clean
                    and step_num in (6.1, 6.2, 6.3)
                ):
                    continue

                # Codex round-3 Finding 2: a fixer step is about to execute,
                # so any subsequent worktree changes can plausibly be
                # attributed to the fixer. Without this flag, edits left by
                # other tools/steps in an otherwise-clean PR run would be
                # committed and pushed as "checkup fixes".
                if step_num in (6.1, 6.2, 6.3):
                    fixer_invoked = True

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

                if step_num == 3:
                    step3_clean = success
                if step_num == 4:
                    step4_clean = success
                if step_num == 5:
                    # Codex round-5 Finding 1: a provider-success result
                    # whose embedded ``failure_signal`` block declares
                    # ``status: fail`` still means tests failed. Treating
                    # provider success as cleanliness lets PR mode skip
                    # the fixer (Steps 6.1/6.2/6.3) and report a passing
                    # verdict with broken code on the PR head. Always
                    # parse the block and derive the logical outcome from
                    # ``status``, then combine it with provider success
                    # for ``step5_clean``.
                    step5_persisted = context.get("step5_output", "") or ""
                    signal_fields, signal_missing = (
                        _parse_failure_signal_block(step5_persisted)
                    )
                    failure_statuses = {"fail", "error", "failed", "failure"}
                    pass_statuses = {"pass", "ok", "success", "passed", "clean"}
                    # Codex round-9 Finding 1: ``skipped``/``skip``/empty-
                    # results statuses mean tests did not run, so we have
                    # NO verification signal. Round-8 mapped any non-pass
                    # status to ``logical_failure``, which ran the fixer
                    # against a non-failure and then allowed a push of
                    # speculative changes that no test ever validated.
                    # Treat skipped as a third state: don't run the fixer
                    # (no failure to act on) but record an "unverified"
                    # flag that the pre-push gate consumes to refuse the
                    # push regardless of other guards.
                    skipped_statuses = _STEP5_SKIPPED_STATUSES
                    status_value = (
                        str(signal_fields.get("status", "")).strip().lower()
                    )
                    # Codex round-8 Finding 1: when the agent omits or
                    # mangles the required ``failure_signal`` block, the
                    # logical outcome is unknown — treating an unknown
                    # outcome as "pass" let a provider-success Step 5
                    # that reported failing tests only in prose flow
                    # through as ``step5_clean=True`` and skipped the
                    # fixer. Fail closed: a missing block (signal_missing
                    # contains "__block__"), an empty status, or any
                    # status word that is neither a known pass nor a
                    # known skipped value counts as a logical failure.
                    block_missing = "__block__" in signal_missing
                    status_recognised_pass = status_value in pass_statuses
                    status_skipped = status_value in skipped_statuses
                    logical_failure = (
                        status_value in failure_statuses
                        or block_missing
                        or (not status_recognised_pass and not status_skipped)
                    )
                    # For loop-control purposes treat a "skipped" result
                    # like a clean Step 5 so the fixer is NOT triggered.
                    # The unverified flag below blocks the eventual push.
                    # Round-10 Finding 1: a "skipped" status from the
                    # agent means tests did not run REGARDLESS of the
                    # provider success flag — an agent can emit a
                    # coherent block even when its provider call timed
                    # out or otherwise reported failure. Set the
                    # in-memory hint based on the status alone; the
                    # pre-push gate also re-derives the truth from the
                    # persisted ``step_outputs["5"]`` so the hint is a
                    # cache, not the source of truth.
                    step5_clean = success and not logical_failure
                    if status_skipped:
                        context["step5_verification_skipped"] = "1"
                        # When provider returned failure but status is
                        # skipped, treat the loop like a clean Step 5
                        # too so the fixer doesn't run against a
                        # non-failure.
                        if not success:
                            step5_clean = True
                    else:
                        context.pop("step5_verification_skipped", None)

                    # Codex round-6 Finding 2: a provider-success result whose
                    # embedded failure_signal block declares status: fail used
                    # to skip the failure-detail console.print (which only
                    # fires in the not-success branch) AND left step_outputs
                    # ["5"] without the "FAILED:" prefix. That blanked out
                    # the user-visible failure detail and silently disabled
                    # the downstream causal-connection check (which keys off
                    # step_outputs["5"].startswith("FAILED:")). Surface the
                    # detail and normalise the persisted step output so both
                    # paths behave the same.
                    if success and logical_failure:
                        persisted_for_surface = step5_persisted
                        if not quiet:
                            console.print(
                                "[yellow]Step 5 reported provider success but the "
                                "failure_signal block declares status="
                                f"{status_value!r}; treating as a test failure."
                                "[/yellow]"
                            )
                            if persisted_for_surface:
                                console.print(
                                    "[yellow]Step 5 failure detail:\n"
                                    f"{persisted_for_surface}[/yellow]"
                                )
                        if not step_outputs.get("5", "").startswith("FAILED:"):
                            step_outputs["5"] = f"FAILED: {persisted_for_surface}"
                            _save_state()

                    if not step5_clean:
                        # Codex round-4 Finding 3: when Step 5 leaves
                        # ``output:`` empty and points to a file via
                        # ``artifact_path:``, the orchestrator must read
                        # the file so Step 6 still sees the failure
                        # detail. Without this, long pytest logs were
                        # silently dropped before Step 6, recreating the
                        # original no-signal fixer problem.
                        if (
                            "output" in signal_missing
                            and signal_fields.get("artifact_path")
                        ):
                            artifact_content = _read_failure_signal_artifact(
                                signal_fields.get("artifact_path", ""),
                                worktree_path,
                            )
                            if artifact_content:
                                signal_fields["output"] = artifact_content
                                signal_missing = [
                                    k for k in signal_missing if k != "output"
                                ]
                        if signal_missing and not quiet:
                            console.print(
                                "[yellow]Step 5 failure_signal block "
                                f"missing/malformed (keys: {sorted(signal_missing)}); "
                                "synthesising normalised block for Step 6."
                                "[/yellow]"
                            )
                        normalised_signal = _normalised_failure_signal_text(
                            step5_persisted, signal_fields, signal_missing
                        )
                        context["step5_failure_signal"] = normalised_signal
                        context["step5_failure_signal_missing"] = ",".join(
                            signal_missing
                        )

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

                # ----------------------------------------------------------
                # Issue #1116 — Checkpoint A2: registry/prompt-source guard
                # refusal paths post the canonical Step 7 verdict via
                # _post_pr_mode_final_report and then return. If the remote
                # head advanced between Checkpoint A's refetch and now, that
                # verdict belongs to the OLD head — publishing it as the
                # canonical report would leak a stale clean verdict. Reuse
                # the pr_metadata fetch just above (no extra GitHub I/O); if
                # the head moved, raise restart so the outer wrapper reruns
                # against the new head.
                #
                # Only fires in fix mode (no_fix=False already implied by
                # being in the fix-mode push block here). Empty current SHA
                # or empty fresh SHA fail-degrades to current behavior to
                # avoid false-positive restarts.
                # ----------------------------------------------------------
                fresh_head_sha_a2 = str(
                    (pr_metadata or {}).get("head_sha", "") or ""
                )
                if (
                    fresh_head_sha_a2
                    and current_pr_head_sha
                    and fresh_head_sha_a2 != current_pr_head_sha
                ):
                    raise _PRHeadAdvancedRestart(
                        old_sha=current_pr_head_sha,
                        new_sha=fresh_head_sha_a2,
                        reason=(
                            "PR head advanced between Step 7 gate and "
                            "guards-and-push block"
                        ),
                        cost_so_far=total_cost,
                        model=last_model_used,
                        step_comments=step_comments_set,
                    )

                # Codex round-1 blocker #3: prompt-source + architecture-
                # registry guards. The review-loop runs these BEFORE its
                # push (checkup_review_loop.py:1183/:1194); bare PR-mode
                # used to skip them, opening a #1063/#1081 bypass. Run
                # 10b first (registry-edit) and 10a second (prompt-
                # source) to mirror the review-loop ordering.
                #
                # Codex round-2 Finding 1: filter the orchestrator's own
                # PDD scratch artifacts (e.g. ``.pdd/checkup-context/
                # pr-changed-files-api.txt`` written by
                # ``_format_pr_changed_files_for_prompt`` and the
                # ``.pdd/checkup-pr-<n>/`` working dir) before any scope
                # or causal guard runs. These files are non-committable
                # (gitignore covers ``.pdd/*``) but can leak into
                # ``--untracked-files=all`` output and falsely poison the
                # scope/causal checks, breaking the clean-run convergence
                # contract.
                _raw_guard_changed_files = _git_changed_files(worktree_path)
                guard_changed_files = [
                    f for f in _raw_guard_changed_files
                    if not f.startswith(".pdd/")
                ]
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

                # Bug 5b: Clean run — when there are no fixer-produced
                # changes there is nothing to commit and nothing to scope-
                # or causal-check. We still flow through the regular push
                # block so Checkpoint D (PR-head freshness) runs and the
                # outer finalization (clear_workflow_state) gets called.
                no_changes_clean_run = not guard_changed_files

                # Codex round-9 Finding 1 / round-10 Findings 2+3: when
                # Step 5 reported ``status: skipped`` the test suite
                # never executed, so we have no verification of whatever
                # the fixer (or tooling) produced AND no evidence that
                # the PR itself is healthy. Refuse the push regardless
                # of scope/causal/diff-size — and regardless of whether
                # the worktree happens to be clean. Returning success on
                # a clean worktree would tell the user "checkup
                # complete" even though no tests ran (round-10 #2).
                #
                # Derive the skipped state from the PERSISTED
                # ``step_outputs["5"]`` value rather than relying on the
                # in-memory ``context['step5_verification_skipped']``
                # cache — context isn't part of the saved state, so a
                # mid-loop interruption could resume with the
                # ``step_outputs["5"]`` skipped block but an empty
                # context cache (round-10 #3). The helper handles a
                # leading ``"FAILED: "`` prefix that ``_handle_step_result``
                # may have prepended.
                verification_skipped = (
                    context.get("step5_verification_skipped") == "1"
                    or _step5_was_skipped(step_outputs.get("5", ""))
                )
                if verification_skipped:
                    # Keep the context cache in sync so downstream code
                    # / state save reflects the gate decision.
                    context["step5_verification_skipped"] = "1"
                    if no_changes_clean_run:
                        unverified_refusal = (
                            "Step 5 verification skipped: the failure_signal "
                            "block reported a 'skipped' status, so the test "
                            "suite did not execute against the PR head. The "
                            "worktree is clean (no fixer changes to push) "
                            "but the checkup did NOT verify that the PR's "
                            "tests pass — refusing to report success. Rerun "
                            "pdd checkup --pr once the test environment is "
                            "healthy."
                        )
                    else:
                        unverified_refusal = (
                            "Step 5 verification skipped: the failure_signal "
                            "block reported a 'skipped' status, so the test "
                            "suite did not execute against the PR head. "
                            "Refusing to push fixer/tooling changes "
                            f"({sorted(guard_changed_files)}) because there "
                            "is no test evidence that they don't break the "
                            "PR. Rerun pdd checkup --pr once the test "
                            "environment is healthy."
                        )
                    pr_artifacts_dir.mkdir(parents=True, exist_ok=True)
                    (
                        pr_artifacts_dir / "verification-skipped-refusal.txt"
                    ).write_text(unverified_refusal + "\n")
                    step_outputs["pr_push"] = unverified_refusal
                    context["pr_push_output"] = unverified_refusal
                    _save_state()
                    post_suffix = _post_pr_mode_final_report(
                        step_outputs.get("7", step7_output)
                    )
                    return (
                        False,
                        f"{unverified_refusal}{post_suffix}",
                        total_cost,
                        last_model_used,
                    )

                # Codex round-3 Finding 2: when Steps 3/4/5 were all clean
                # the fixer (6.1/6.2/6.3) was skipped, so any dirty files in
                # the worktree are side effects from non-fixer steps (Step 7
                # tooling, ad-hoc agent edits, etc.). Pushing them would
                # recreate the non-convergent clean-run failure where each
                # rerun publishes a new "checkup fix" commit that nobody
                # asked for. Refuse the push, record the artifact, and post
                # the canonical Step 7 verdict instead.
                if (
                    not fixer_invoked
                    and not no_changes_clean_run
                ):
                    side_effect_refusal = (
                        "Clean-run side-effect guard: fixer steps "
                        "(6.1/6.2/6.3) were skipped because Steps 3/4/5 all "
                        "reported clean, but the worktree contains "
                        f"non-fixer edits: {sorted(guard_changed_files)}. "
                        "Refusing to commit or push these — they were not "
                        "produced by the fixer and have no causal link to a "
                        "PR failure."
                    )
                    pr_artifacts_dir.mkdir(parents=True, exist_ok=True)
                    (
                        pr_artifacts_dir / "clean-run-side-effect-refusal.txt"
                    ).write_text(side_effect_refusal + "\n")
                    step_outputs["pr_push"] = side_effect_refusal
                    context["pr_push_output"] = side_effect_refusal
                    _save_state()
                    post_suffix = _post_pr_mode_final_report(
                        step_outputs.get("7", step7_output)
                    )
                    return (
                        False,
                        f"{side_effect_refusal}{post_suffix}",
                        total_cost,
                        last_model_used,
                    )

                # Bug 2: Scope guard — reject fixer files outside the PR's
                # changed-file set. Parse the actual GitHub API status rows
                # emitted by ``_format_pr_api_changed_files`` ("- MODIFIED:
                # path", "- ADDED: path", "- RENAMED: old -> new", etc.).
                # RENAMED rows contribute both the old and new paths so a
                # fixer that touches either side is in scope. The
                # truncation footer ("NOTE: GitHub PR files API list
                # truncated…") is filtered out because its colon would
                # otherwise pollute the file set.
                pr_file_set: set = set()
                if not no_changes_clean_run:
                    import re as _re
                    # Codex round-2 Finding 1: prefer the unbounded
                    # ``api_changed_files_full`` list when present —
                    # ``api_changed_files`` is a truncated preview (with a
                    # ``- NOTE: GitHub PR files API list truncated…``
                    # footer) so on large PRs valid in-scope files beyond
                    # the preview were being rejected. Fall back to the
                    # preview when the full list is unavailable.
                    api_files_text = (
                        pr_metadata.get("api_changed_files_full")
                        or pr_metadata.get("api_changed_files")
                        or ""
                    )
                    # Codex round-8 Finding 2: when the GitHub PR files
                    # API is down/rate-limited, ``api_files_text`` is
                    # empty even though the local merge-base diff
                    # (formatted by ``_format_pr_changed_files_for_prompt``
                    # into ``context['pr_scope_changed_files']``) still
                    # lists the PR's changed files. Parsing only the API
                    # rows left ``pr_file_set`` empty and refused valid
                    # edits to PR-touched files. Union both sources so
                    # the scope guard tolerates an API outage when the
                    # local base ref is healthy. The same regex matches
                    # both formats — uppercase word statuses (MODIFIED/
                    # ADDED/RENAMED/DELETED) from the API formatter, and
                    # short git statuses (M, A, D, R100) from the local
                    # merge-base formatter — because ``[A-Z][A-Z0-9]*``
                    # spans both.
                    local_scope_text = str(
                        context.get("pr_scope_changed_files") or ""
                    )
                    pr_scope_sources = "\n".join(
                        text for text in (api_files_text, local_scope_text)
                        if text
                    )

                    def _ingest_row(status_label: str, value: str) -> None:
                        if status_label == "NOTE":
                            return
                        if " -> " in value and status_label.startswith("R"):
                            old_path, _, new_path = value.partition(" -> ")
                            if old_path:
                                pr_file_set.add(old_path)
                            if new_path:
                                pr_file_set.add(new_path)
                        else:
                            pr_file_set.add(value)

                    for match in _re.finditer(
                        r"^-\s+([A-Z][A-Z0-9]*):\s*(.+?)\s*$",
                        pr_scope_sources,
                        flags=_re.MULTILINE,
                    ):
                        _ingest_row(match.group(1), match.group(2))
                    # Codex round-5 Finding 3: parse EXPANSION_ITEMS into
                    # (paths, justified_paths). Only paths whose OWN marker
                    # entry carried a causal justification bypass the
                    # out-of-scope refusal — a fixer cannot list an
                    # unrelated path on one marker line and let a sibling
                    # marker's justification cover for it.
                    step6_out = step_outputs.get("6_1", "")
                    _, justified_paths_set = (
                        _parse_expansion_items(step6_out)
                    )
                    # Codex round-8 Finding 3: the Step 6 prompt
                    # explicitly permits the fixer to edit failing test
                    # files and files whose failures are causally related
                    # to PR-changed files, without requiring an explicit
                    # EXPANSION_ITEMS marker. The old scope guard refused
                    # those before the causal guard could allow them.
                    # Extract Step 5 failure paths and treat them as a
                    # third scope-allowed source. The causal guard below
                    # still applies (it requires at least one overlap
                    # between fixer files and the OK-set), so genuinely
                    # unrelated edits remain blocked.
                    step5_for_scope = step_outputs.get("5", "")
                    scope_failure_paths: set = set()
                    if step5_for_scope.startswith("FAILED:"):
                        scope_failure_paths = set(_re.findall(
                            r"(?:tests?/|pdd/|src/)[\w/._-]+\.py",
                            step5_for_scope,
                        ))
                    scope_allowed: set = (
                        pr_file_set | scope_failure_paths | justified_paths_set
                    )
                    out_of_scope = [
                        f for f in guard_changed_files
                        if f not in scope_allowed
                    ]
                    if out_of_scope:
                        if justified_paths_set:
                            scope_refusal = (
                                "Scope guard: fixer touched files outside PR's "
                                "changed-file set; EXPANSION_ITEMS marker was "
                                "present but did not cover these paths: "
                                f"{out_of_scope}. Justified expansion paths: "
                                f"{sorted(justified_paths_set)}."
                            )
                        elif "EXPANSION_ITEMS:" in step6_out:
                            scope_refusal = (
                                "Scope guard: fixer emitted an EXPANSION_ITEMS "
                                "marker but no listed path carried its own "
                                "causal justification. Out-of-scope files: "
                                f"{out_of_scope}."
                            )
                        else:
                            scope_refusal = (
                                "Scope guard: fixer touched files outside PR's "
                                "changed-file set without EXPANSION_ITEMS "
                                f"justification: {out_of_scope}"
                            )
                        pr_artifacts_dir.mkdir(parents=True, exist_ok=True)
                        (pr_artifacts_dir / "scope-guard-refusal.txt").write_text(
                            scope_refusal + "\n"
                        )
                        step_outputs["pr_push"] = scope_refusal
                        context["pr_push_output"] = scope_refusal
                        _save_state()
                        post_suffix = _post_pr_mode_final_report(
                            step_outputs.get("7", step7_output)
                        )
                        return (False, f"{scope_refusal}{post_suffix}", total_cost, last_model_used)

                    # Bug 3: Causal-connection check — fixer diff must
                    # plausibly relate to the work in this PR. The "OK
                    # set" is the UNION of:
                    #   1. PR changed files (parsed above) — a test-file
                    #      failure pointing at a source file that is part
                    #      of the PR is the normal causal pattern.
                    #   2. File paths mentioned in the Step 5 failure
                    #      output (test files, pdd/src files, etc.).
                    #   3. EXPANSION_ITEMS paths explicitly justified by
                    #      the fixer (parsed from step 6 output).
                    # Only refuse when fixer_files has zero overlap with
                    # the union. This avoids the previous false-positive
                    # where a failing ``tests/test_main.py`` could not be
                    # fixed by editing ``pdd/main.py``.
                    step5_out = step_outputs.get("5", "")
                    if step5_out.startswith("FAILED:"):
                        failure_paths = set(_re.findall(
                            r"(?:tests?/|pdd/|src/)[\w/._-]+\.py",
                            step5_out,
                        ))
                        # Codex round-5 Finding 3: reuse the per-path
                        # justified expansion set from the scope check;
                        # only paths whose OWN marker carried a causal
                        # justification contribute to the causal OK-set.
                        expansion_paths = justified_paths_set
                        ok_set = pr_file_set | failure_paths | expansion_paths
                        if failure_paths and ok_set:
                            fixer_files_set = set(guard_changed_files)
                            overlap = fixer_files_set & ok_set
                            if not overlap:
                                causal_refusal = (
                                    f"Causal-connection check: fixer changed files "
                                    f"{sorted(fixer_files_set)} have zero overlap with "
                                    f"the union of PR changed files {sorted(pr_file_set)}, "
                                    f"Step 5 failure paths {sorted(failure_paths)}, and "
                                    f"justified EXPANSION_ITEMS paths {sorted(expansion_paths)}. "
                                    f"Refusing push to prevent unrelated changes reaching the PR."
                                )
                                pr_artifacts_dir.mkdir(parents=True, exist_ok=True)
                                (
                                    pr_artifacts_dir / "causal-connection-refusal.txt"
                                ).write_text(causal_refusal + "\n")
                                step_outputs["pr_push"] = causal_refusal
                                context["pr_push_output"] = causal_refusal
                                _save_state()
                                post_suffix = _post_pr_mode_final_report(
                                    step_outputs.get("7", step7_output)
                                )
                                return (
                                    False,
                                    f"{causal_refusal}{post_suffix}",
                                    total_cost,
                                    last_model_used,
                                )

                # Codex round-3 Finding 5: diff size sanity gate. A push
                # that adds more than ``DIFF_SIZE_ADDED_LOC_LIMIT`` lines
                # without an explicit, justified EXPANSION_ITEMS marker
                # signals a runaway fixer (whole-module rewrites, large
                # generated files, etc.). Refuse it so the operator can
                # inspect — a fix genuinely needing that much code should
                # declare itself via EXPANSION_ITEMS.
                if not no_changes_clean_run:
                    try:
                        size_limit = int(
                            os.environ.get(
                                "PDD_CHECKUP_DIFF_LOC_LIMIT",
                                str(DIFF_SIZE_ADDED_LOC_LIMIT),
                            )
                        )
                    except ValueError:
                        size_limit = DIFF_SIZE_ADDED_LOC_LIMIT
                    if size_limit > 0:
                        per_path_added = _diff_size_added_lines_by_path(worktree_path)
                        added_lines = (
                            sum(per_path_added.values())
                            if per_path_added is not None
                            else None
                        )
                        if added_lines is not None and added_lines > size_limit:
                            # Codex round-5 Finding 3 / round-9 Finding 2:
                            # every OVERSIZED dirty path must be covered
                            # by its OWN justified EXPANSION_ITEMS entry —
                            # small companion files (a 5-line test update
                            # alongside a 600-line refactor) are exempt
                            # so the gate matches the documented
                            # "every oversized dirty path" promise. A
                            # sibling marker's justification still does
                            # NOT wave the size gate through for an
                            # oversized path that lacks its own causal
                            # reason.
                            #
                            # NOTE: this is intentionally stricter than
                            # the scope guard above — the scope guard
                            # accepts ``pr_file_set`` membership alone
                            # because PR-listed files are presumed
                            # in-scope by the PR itself. The size guard
                            # cares about the SIZE of the change, so
                            # in-scope membership does not implicitly
                            # justify a large diff; only an explicit,
                            # path-level justified EXPANSION_ITEMS entry
                            # does.
                            oversized_paths = {
                                path
                                for path, count in (per_path_added or {}).items()
                                if count >= OVERSIZED_PATH_ADDED_LOC_FLOOR
                            }
                            uncovered_oversized = sorted(
                                oversized_paths - justified_paths_set
                            )
                            # If the total is over but no single file is
                            # oversized (death-by-a-thousand-cuts), fall
                            # back to the original strict rule so the
                            # gate still catches diffuse runaway diffs.
                            if not oversized_paths:
                                uncovered_oversized = sorted(
                                    set(guard_changed_files) - justified_paths_set
                                )
                            covers_oversized_paths = (
                                bool(justified_paths_set)
                                and not uncovered_oversized
                            )
                            if not covers_oversized_paths:
                                if not justified_paths_set:
                                    bypass_reason = (
                                        "no justified EXPANSION_ITEMS marker"
                                    )
                                else:
                                    bypass_reason = (
                                        "EXPANSION_ITEMS marker did not cover "
                                        "every oversized changed path "
                                        f"(>= {OVERSIZED_PATH_ADDED_LOC_FLOOR} "
                                        "added lines) with its own causal "
                                        "justification; uncovered oversized "
                                        f"files: {uncovered_oversized}. Justified "
                                        f"expansion paths: {sorted(justified_paths_set)}"
                                    )
                                size_refusal = (
                                    "Diff size guard: fixer push would add "
                                    f"{added_lines} lines (limit {size_limit}) "
                                    f"and the bypass is invalid: {bypass_reason}. "
                                    "Refusing push — every oversized changed "
                                    f"path (>= {OVERSIZED_PATH_ADDED_LOC_FLOOR} "
                                    "added lines) must be declared under "
                                    "EXPANSION_ITEMS with a causal justification, "
                                    "or the limit must be raised via "
                                    "PDD_CHECKUP_DIFF_LOC_LIMIT."
                                )
                                pr_artifacts_dir.mkdir(parents=True, exist_ok=True)
                                (
                                    pr_artifacts_dir / "diff-size-guard-refusal.txt"
                                ).write_text(size_refusal + "\n")
                                step_outputs["pr_push"] = size_refusal
                                context["pr_push_output"] = size_refusal
                                _save_state()
                                post_suffix = _post_pr_mode_final_report(
                                    step_outputs.get("7", step7_output)
                                )
                                return (
                                    False,
                                    f"{size_refusal}{post_suffix}",
                                    total_cost,
                                    last_model_used,
                                )

                if no_changes_clean_run:
                    push_ok, push_message = True, "No changes to push."
                else:
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
                # Issue #1116 round-5 Finding 1 — Checkpoint D: between
                # the successful-push paths and the canonical Step 7
                # report there is a final stale-verdict window where a
                # third party can push more commits on top of ours. The
                # narrow round-1 Checkpoint C only fired on
                # "No changes to push." / "No eligible changes to push.";
                # plain success and post-rebase reverify-passed paths
                # skipped the boundary. Broaden the check to fire on
                # every successful push outcome (the failure paths are
                # already covered by Checkpoint B above).
                #
                # The baseline must NOT be ``current_pr_head_sha`` here
                # — that's the entry SHA, and after a real push the
                # remote head moved BECAUSE of us; comparing fresh
                # against entry would false-positive every push into a
                # restart. The correct baseline is the local worktree
                # HEAD: after a normal push it equals our pushed commit,
                # after a rebase-then-push it equals the rebased commit,
                # and after a no-change push it equals the entry SHA
                # (which subsumes round-1 Checkpoint C). A divergence
                # between local HEAD and the refetched remote head
                # means *additional* commits landed after ours — the
                # stale-verdict case.
                # ------------------------------------------------------
                local_head_sha_d = _git_rev_parse_head(worktree_path)
                try:
                    fresh_meta_d = _fetch_pr_metadata(
                        pr_owner, pr_repo, pr_number
                    )
                except Exception:  # noqa: BLE001
                    fresh_meta_d = {}
                fresh_head_sha_d = str(
                    (fresh_meta_d or {}).get("head_sha", "") or ""
                )
                if (
                    fresh_head_sha_d
                    and local_head_sha_d
                    and fresh_head_sha_d != local_head_sha_d
                ):
                    raise _PRHeadAdvancedRestart(
                        old_sha=local_head_sha_d,
                        new_sha=fresh_head_sha_d,
                        reason=(
                            "Push completed but PR head advanced "
                            "beyond pushed commit before final report"
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
    test_scope: str = "full",
    start_step_override: Optional[Union[int, float]] = None,
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
            test_scope=test_scope,
            start_step_override=start_step_override,
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
                test_scope=test_scope,
                start_step_override=start_step_override,
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
