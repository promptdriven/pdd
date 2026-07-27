"""``create_branch_and_pr`` — fallback PR creation when the PDD CLI doesn't make one.

When the PDD CLI exits without producing a PR (e.g. ``pdd generate``, or when
``pdd bug``/``fix`` make changes but don't push), the executor falls back to
this function to commit any uncommitted changes, push to a branch named after
the issue's label, and open a PR via ``gh pr create``.

Responsibilities:
- Clean up PDD artifacts before checking for real code changes
- Detect existing PRs (exact branch match + CLI prefix fallback) to avoid dual-PR
- Stash + checkout + pop dance when local changes conflict with target branch
- Commit with label-appropriate prefix (fix/feat/test/chore)
- Refresh git remote URL with current GH token before push
- Force-with-lease push with auth-failure retry (token might have expired)
- Update PR title on existing PRs

This module owns one function but it is the largest single function in the
executor (426 lines as of 2026-04 and it has historically been the most
churned area — issues #609, #689, #742, #744, #825, #951).
"""

from __future__ import annotations

import logging
import subprocess

from src.workers.runtime.artifacts import (
    _is_pdd_artifact,  # noqa: F401  # used by docstring example
)
from src.workers.runtime.output import extract_pr_url

logger = logging.getLogger(__name__)

__all__ = ["create_branch_and_pr"]


async def _run_git_command(args: list[str], workdir: str, env: dict[str, str]) -> tuple[int, str]:
    """Local wrapper that defers to ``orchestrator._run_git_command`` at call time.

    Why not just ``from .git_helpers import _run_git_command``?

    Because when tests patch ``pdd_executor.orchestrator._run_git_command``
    they expect the patch to intercept calls inside ``create_branch_and_pr``
    too — that's how the test suite has worked since before this refactor.
    A direct import from ``git_helpers`` would bind a local reference that
    those patches can't reach.

    With the deferred lookup pattern below, the binding is fetched from
    ``orchestrator`` (not ``git_helpers``) at every call.  Tests can patch
    *either*:

    - ``pdd_executor.orchestrator._run_git_command`` — the original convention
      (intercepted because we look it up from orchestrator at call time)
    - ``pdd_executor.pr_creation._run_git_command`` — the white-box convention
      for tests that exercise create_branch_and_pr in isolation
      (intercepted because the call site finds this wrapper in the local namespace)
    """
    from . import orchestrator

    return await orchestrator._run_git_command(args, workdir, env)


async def create_branch_and_pr(
    owner: str,
    repo: str,
    issue_number: int,
    workdir: str,
    env: dict[str, str],
    label: str | None = None,
    base_branch: str | None = None,
) -> str | None:
    """
    Creates a branch, commits all changes, pushes, and opens a PR.

    Used when PDD CLI doesn't create a PR (generate label, or when bug/fix/change/test
    commands make changes but don't create a PR).

    Args:
        owner: Repository owner.
        repo: Repository name.
        issue_number: The GitHub issue number.
        workdir: The directory where the repo is cloned.
        env: Environment variables including GitHub token.
        label: The label type (bug, fix, enhancement, test, generate). Defaults to "pdd".
        base_branch: Optional base branch for the PR. Defaults to "main".

    Returns the PR URL if successful, None if no changes detected.
    Raises RuntimeError on git/gh failures.
    """
    # Use label for branch naming, fall back to "pdd" if not provided
    label_str = (
        str(label.value)
        if label is not None and hasattr(label, "value")
        else str(label)
        if label
        else "pdd"
    )
    branch_name = f"{label_str}/issue-{issue_number}"

    # If already on an issue branch (e.g. change/issue-N from a prior command),
    # push to that branch instead of creating a new one (e.g. sync/issue-N).
    # This matches upstream behavior where pdd change → pdd sync both commit
    # to the same branch/PR.  CRITICAL: this guard prevents the dual-PR bug
    # where sync creates a second PR on sync/issue-N while change/issue-N
    # already exists.
    try:
        result = subprocess.run(
            ["git", "branch", "--show-current"],
            cwd=workdir,
            capture_output=True,
            text=True,
            timeout=5,
        )
        if result.returncode == 0 and result.stdout.strip():
            current = result.stdout.strip()
            if current.endswith(f"/issue-{issue_number}") and current != branch_name:
                logger.info(
                    f"Already on issue branch '{current}' (differs from default '{branch_name}'), "
                    f"using it to avoid creating a duplicate PR"
                )
                branch_name = current
    except Exception as e:
        logger.warning(
            "Dual-PR guard failed (git branch --show-current): %s — "
            "using default branch_name '%s'. This may cause duplicate PRs.",
            str(e)[:200],
            branch_name,
        )

    # 1. Clean up PDD artifacts before checking for real code changes.
    #    First: remove known non-test artifacts unconditionally.
    await _run_git_command(
        [
            "bash",
            "-c",
            "rm -f pdd_cost.csv .pdd_gh_token .agentic_prompt_* verify_*.sh; "
            "find . -name '*_fixed.py' -delete; "
            "find . -name 'step*_output.md' -delete; "
            "find . -name '*_errors.txt' -delete; "
            "rm -rf .local_pkgs .pdd/backups/ .pdd/bug-state/ .pdd/core_dumps/ .gh-wrapper; "
            "for d in .tmp-build-venv .tmp-test-venv; do "
            '  if [ -e "$d" ] && [ -z "$(git ls-files -- "$d")" ]; then rm -rf -- "$d"; fi; '
            "done",
        ],
        workdir,
        env,
    )
    #    Second: remove test reproduction artifacts ONLY if they are untracked.
    #    Previous approach used `find -delete` which also removed legitimate
    #    tracked test files (root cause of 19-file deletion in PRs #950-#998).
    await _run_git_command(
        [
            "bash",
            "-c",
            "for pattern in 'test_issue_*' 'test_*_reproduce*' 'test_reproduce_*' "
            "'test_*_reproduction*' 'test_*_repro.py' 'test_e2e_*_issue_*'; do "
            "  find . -name \"$pattern\" -print0 | while IFS= read -r -d '' f; do "
            '    git ls-files --error-unmatch -- "$f" >/dev/null 2>&1 || rm -f -- "$f"; '
            "  done; "
            "done",
        ],
        workdir,
        env,
    )

    # 2. Check for changes (after artifact cleanup so only real code changes remain)
    exit_code, status_output = await _run_git_command(
        ["git", "status", "--porcelain"], workdir, env
    )
    if exit_code != 0:
        raise RuntimeError(f"git status failed: {status_output}")

    has_local_changes = bool(status_output.strip())
    if has_local_changes:
        real_changes = []
        for line in status_output.splitlines():
            if not line.strip():
                continue
            # porcelain format: "XY filename" — filename starts at offset 3
            filename = line[3:] if len(line) > 3 else line.strip()
            # Handle renames: "R  old -> new" — check both paths
            if " -> " in filename:
                _, new_path = filename.rsplit(" -> ", 1)
                filename = new_path
            if not _is_pdd_artifact(filename):
                real_changes.append(line)
        has_local_changes = bool(real_changes)

    # 2b. Check for existing open PR for this issue (exact branch match).
    # Uses exact match to prevent cross-label hijacking (issue #616).
    existing_pr_url = None
    exit_code, pr_list_output = await _run_git_command(
        [
            "gh",
            "pr",
            "list",
            "--state",
            "open",
            "--json",
            "url,headRefName",
            "--jq",
            f'.[] | select(.headRefName == "{branch_name}") | "\\(.url)\\t\\(.headRefName)"',
        ],
        workdir,
        env,
    )
    if exit_code == 0 and pr_list_output.strip():
        first_line = pr_list_output.strip().split("\n")[0]
        existing_pr_url, existing_branch = first_line.split("\t", 1)
        branch_name = existing_branch
        logger.info(f"Found existing PR {existing_pr_url} on branch {branch_name}, pushing to it")
    else:
        # Fallback: the PDD CLI uses different branch prefixes than the executor.
        # CLI uses "change/issue-N" but executor computes "enhancement/issue-N".
        # CLI uses "bug/issue-N" which matches executor's "bug/issue-N".
        # Check the CLI's branch prefix if the executor's didn't match.
        cli_prefix_map = {
            "enhancement": "change",
            "bug": "fix",
        }  # label_str → CLI prefix
        cli_prefix = cli_prefix_map.get(label_str)
        if cli_prefix:
            cli_branch = f"{cli_prefix}/issue-{issue_number}"
            exit_code2, pr_list_output2 = await _run_git_command(
                [
                    "gh",
                    "pr",
                    "list",
                    "--state",
                    "open",
                    "--json",
                    "url,headRefName",
                    "--jq",
                    f'.[] | select(.headRefName == "{cli_branch}") | "\\(.url)\\t\\(.headRefName)"',
                ],
                workdir,
                env,
            )
            if exit_code2 == 0 and pr_list_output2.strip():
                first_line = pr_list_output2.strip().split("\n")[0]
                existing_pr_url, existing_branch = first_line.split("\t", 1)
                branch_name = existing_branch
                logger.info(
                    f"Found CLI's PR {existing_pr_url} on branch {branch_name} "
                    f"(CLI uses '{cli_prefix}/' instead of '{label_str}/'), pushing to it"
                )

    if not has_local_changes:
        if existing_pr_url:
            logger.info(
                f"No local changes but found existing PR for {label_str} job on {owner}/{repo}#{issue_number}"
            )
            return existing_pr_url
        logger.info(
            f"No file changes detected for {label_str} job on {owner}/{repo}#{issue_number}"
        )
        return None

    logger.info(f"Detected changes for {label_str} job, creating branch {branch_name}")

    # Skip worktree cleanup when the workdir IS a worktree (e.g. pdd change's
    # .pdd/worktrees/change-issue-N/). Removing it would destroy our working
    # directory and all the files we want to commit.
    is_inside_worktree = "/.pdd/worktrees/" in workdir
    if not is_inside_worktree:
        # Clean up worktrees holding the target branch (PDD CLI may leave active worktrees
        # that block checkout; `git worktree prune` only removes orphaned metadata, not
        # worktrees whose directories still exist on disk)
        wt_exit, wt_output = await _run_git_command(
            ["git", "worktree", "list", "--porcelain"], workdir, env
        )
        if wt_exit == 0:
            target_ref = f"refs/heads/{branch_name}"
            current_wt_path = None
            for line in wt_output.splitlines():
                if line.startswith("worktree "):
                    current_wt_path = line[len("worktree ") :]
                elif line.startswith("branch ") and current_wt_path:
                    if line.strip() == f"branch {target_ref}":
                        await _run_git_command(
                            ["git", "worktree", "remove", "--force", current_wt_path],
                            workdir,
                            env,
                        )
                    current_wt_path = None
                elif line == "":
                    current_wt_path = None
        await _run_git_command(["git", "worktree", "prune"], workdir, env)
    else:
        logger.info(f"Skipping worktree cleanup — workdir is itself a worktree: {workdir}")

    # 3. Create and checkout branch (skip if already on it)
    exit_code, current_branch = await _run_git_command(
        ["git", "branch", "--show-current"], workdir, env
    )
    if current_branch.strip() != branch_name:
        exit_code, output = await _run_git_command(
            ["git", "checkout", "-b", branch_name], workdir, env
        )
        if exit_code != 0:
            # Branch may already exist locally (e.g. CLI created it via worktree)
            exit_code, output = await _run_git_command(
                ["git", "checkout", branch_name], workdir, env
            )
            if exit_code != 0:
                if "local changes" in output.lower() or "would be overwritten" in output.lower():
                    # Local changes conflict with target branch content.
                    # Stash → checkout → pop to preserve our changes.
                    await _run_git_command(
                        ["git", "stash", "push", "--include-untracked"],
                        workdir,
                        env,
                    )
                    exit_code, output = await _run_git_command(
                        ["git", "checkout", branch_name], workdir, env
                    )
                    if exit_code != 0:
                        raise RuntimeError(f"git checkout failed after stash: {output}")
                    exit_code, output = await _run_git_command(
                        ["git", "stash", "pop"], workdir, env
                    )
                    if exit_code != 0:
                        # Conflicts during pop — keep stashed (our) changes
                        await _run_git_command(["git", "checkout", "--theirs", "."], workdir, env)
                        await _run_git_command(["git", "add", "."], workdir, env)
                        await _run_git_command(["git", "stash", "drop"], workdir, env)
                else:
                    raise RuntimeError(f"git checkout failed: {output}")

    # 4. Stage all changes
    exit_code, output = await _run_git_command(["git", "add", "-A"], workdir, env)
    if exit_code != 0:
        raise RuntimeError(f"git add failed: {output}")

    # 4. Commit - use label-appropriate commit message
    commit_prefixes = {
        "bug": "fix",
        "fix": "fix",
        "enhancement": "feat",
        "test": "test",
        "generate": "feat",
        "sync": "chore",
    }
    commit_prefix = commit_prefixes.get(label_str, "chore")
    commit_msg = f"{commit_prefix}: PDD {label_str} changes for #{issue_number}"
    exit_code, output = await _run_git_command(["git", "commit", "-m", commit_msg], workdir, env)
    if exit_code != 0:
        raise RuntimeError(f"git commit failed: {output}")

    # 4b. Refresh remote URL with current token — the token embedded in the
    # origin URL during clone may have expired (GitHub App tokens last 1 hour,
    # PDD CLI jobs can run up to 4 hours).
    fresh_token = env.get("GH_TOKEN", "")
    if fresh_token:
        await _run_git_command(
            [
                "git",
                "remote",
                "set-url",
                "origin",
                f"https://x-access-token:{fresh_token}@github.com/{owner}/{repo}.git",
            ],
            workdir,
            env,
        )

    # 5. Fetch remote branch ref if it exists (needed for --force-with-lease
    # with shallow clones where remote tracking refs aren't available).
    # Shallow clones configure a single-branch refspec (e.g. +refs/heads/main:...).
    # --force-with-lease resolves tracking refs via the configured refspec, so we
    # must add a wildcard refspec first, otherwise push fails with (stale info).
    await _run_git_command(
        ["git", "config", "remote.origin.fetch", "+refs/heads/*:refs/remotes/origin/*"],
        workdir,
        env,
    )
    await _run_git_command(
        [
            "git",
            "fetch",
            "origin",
            f"+refs/heads/{branch_name}:refs/remotes/origin/{branch_name}",
        ],
        workdir,
        env,
    )

    # Push (use --force-with-lease to handle re-runs where remote branch
    # already exists from a prior attempt with divergent commits).
    # Retry up to 3 times on authentication failures — the token may have
    # expired between the remote URL refresh and the push attempt.
    max_push_attempts = 3
    for push_attempt in range(1, max_push_attempts + 1):
        exit_code, output = await _run_git_command(
            ["git", "push", "--force-with-lease", "-u", "origin", branch_name],
            workdir,
            env,
        )
        if exit_code == 0:
            break
        output_lower = output.lower()
        is_auth_failure = (
            "authentication failed" in output_lower or "invalid username or token" in output_lower
        )
        if not is_auth_failure or push_attempt == max_push_attempts:
            raise RuntimeError(f"git push failed: {output}")
        logger.warning(
            f"Push attempt {push_attempt}/{max_push_attempts} failed with auth error, "
            f"refreshing token and retrying: {output}"
        )
        # Re-read fresh token from the background-refreshed token file,
        # falling back to env["GH_TOKEN"] if the file isn't available.
        retry_token = ""
        token_file = env.get("PDD_GH_TOKEN_FILE", "")
        if token_file:
            try:
                with open(token_file) as f:
                    retry_token = f.read().strip()
                if retry_token:
                    env["GH_TOKEN"] = retry_token
                    env["GITHUB_TOKEN"] = retry_token
            except OSError:
                pass
        if not retry_token:
            retry_token = env.get("GH_TOKEN", "")
        if retry_token:
            await _run_git_command(
                [
                    "git",
                    "remote",
                    "set-url",
                    "origin",
                    f"https://x-access-token:{retry_token}@github.com/{owner}/{repo}.git",
                ],
                workdir,
                env,
            )

    # 5b. If we found an existing PR, update title and skip PR creation
    if existing_pr_url:
        pr_title = f"{commit_prefix}: PDD {label_str} for #{issue_number}"
        await _run_git_command(
            ["gh", "pr", "edit", existing_pr_url, "--title", pr_title],
            workdir,
            env,
        )
        logger.info(f"Pushed to existing PR: {existing_pr_url}")
        return existing_pr_url

    # 6. Create PR via gh CLI - use label-appropriate title and body
    pr_title = f"{commit_prefix}: PDD {label_str} for #{issue_number}"
    pr_body = (
        f"## Summary\n"
        f"Changes from PDD `{label_str}` command for issue #{issue_number}.\n\n"
        f"Closes #{issue_number}"
    )
    # Create PR - use specified base or default to "main"
    target_base = base_branch or "main"
    exit_code, pr_output = await _run_git_command(
        [
            "gh",
            "pr",
            "create",
            "--title",
            pr_title,
            "--body",
            pr_body,
            "--base",
            target_base,
            "--head",
            branch_name,
        ],
        workdir,
        env,
    )
    if exit_code != 0:
        if "already exists" in pr_output:
            existing_url = extract_pr_url(pr_output)
            if existing_url:
                logger.info(f"PR already exists, reusing: {existing_url}")
                return existing_url
        raise RuntimeError(f"gh pr create failed: {pr_output}")

    # 7. Extract PR URL from gh output (gh prints the URL on stdout)
    pr_url = extract_pr_url(pr_output)
    if not pr_url:
        # gh pr create prints the URL as its output; try the raw stripped output
        pr_url = pr_output.strip() if pr_output.strip().startswith("https://") else None

    logger.info(f"PR created successfully: {pr_url}")
    return pr_url
