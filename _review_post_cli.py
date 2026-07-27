"""Post-CLI processing extracted from execute_pdd_job.

This module owns Phases 5-9 of the executor pipeline:

- **Phase 5** — find or create the PR.  Tries (in order): the PR URL printed
  by the PDD CLI, then ``gh pr list`` with retries (Issue #689 eventual
  consistency), then ``create_branch_and_pr`` as a fallback.  Also handles
  the unpushed-changes-on-existing-PR path (Issue #609).
- **Phase 6** — calculate total cost (infrastructure + LLM) and store in
  ``result_summary``.
- **Phase 7** — determine the actual outcome via ``_classify_pdd_outcome``
  (Issue #609 had us add a "found unpushed changes but failed to push" path
  here).
- **Phase 8** — finalize the credit reservation with the actual cost.
- **Phase 9** — update Firestore status and, for normal user-facing jobs,
  post the issue comment summarizing the run plus best-effort project-board
  completion.  Internal verification jobs skip generic comments/project
  updates because the solving orchestrator owns verifier UX.

This is a single async function that takes ~17 inputs.  It mutates
``result_summary`` in place and returns ``(reservation_id, stop_handled)``.
``reservation_id`` is set to ``None`` after finalization so the orchestrator's
finally block doesn't double-release.

All patchable dependencies are looked up from orchestrator at call time
(see the same deferred-capture pattern in env_setup.py and waterfall_runner.py).
"""

from __future__ import annotations

import logging
import re
from pathlib import PurePosixPath
from typing import Any

from src.models import Job
from src.workers.pdd_executor.result_handlers import _is_internal_verification_job

logger = logging.getLogger(__name__)

__all__ = ["_build_research_replay_hint", "_process_pdd_results"]


def _prompt_source_candidates(prompt_path: str) -> list[str]:
    path = PurePosixPath(prompt_path)
    name = path.name
    if not name.endswith(".prompt") or "_" not in name:
        return []
    stem = name[: -len(".prompt")]
    base, language = stem.rsplit("_", 1)
    if language.lower() != "python":
        return []
    if prompt_path.startswith("prompts/backend/"):
        return [f"backend/functions/{base}.py"]
    prefix = "extensions/github_pdd_app/prompts/src/"
    if prompt_path.startswith(prefix):
        rel = PurePosixPath(prompt_path[len(prefix) :])
        parent = rel.parent.as_posix()
        if parent == ".":
            return [f"extensions/github_pdd_app/src/{base}.py"]
        return [f"extensions/github_pdd_app/src/{parent}/{base}.py"]
    return [f"{base}.py", f"src/{base}.py", f"app/{base}.py"]


def _paths_from_name_status(output: str) -> list[str]:
    paths: list[str] = []
    for line in output.splitlines():
        parts = line.split("\t")
        if not parts:
            continue
        status = parts[0]
        path = parts[-1]
        if status and status[0] in {"A", "M", "R", "C"} and path:
            paths.append(path)
    return sorted(set(paths))


def _classify_replay_files(paths: list[str]) -> dict[str, Any]:
    prompts = sorted(
        path for path in paths if path.endswith(".prompt") and _prompt_source_candidates(path)
    )
    tests = sorted(
        path
        for path in paths
        if path.endswith(".py")
        and (
            path.startswith("backend/tests/")
            or path.startswith("extensions/github_pdd_app/tests/")
            or path.startswith("tests/")
            or "/tests/" in path
            or PurePosixPath(path).name.startswith("test_")
        )
    )
    sources = sorted(
        path
        for path in paths
        if path.endswith(".py") and path not in tests and not path.startswith(".pdd/")
    )
    prompt_source_pairs = []
    for prompt in prompts:
        candidates = set(_prompt_source_candidates(prompt))
        candidate_names = {PurePosixPath(candidate).name for candidate in candidates}
        for source in sources:
            if source in candidates or PurePosixPath(source).name in candidate_names:
                prompt_source_pairs.append({"prompt": prompt, "source": source})
    return {
        "changed_prompt_files": prompts,
        "changed_source_files": sources,
        "changed_test_files": tests,
        "prompt_source_pairs": prompt_source_pairs,
    }


async def _build_research_replay_hint(
    *,
    job: Job,
    workdir: str,
    effective_workdir: str,
    pdd_command: str,
    pr_url: str | None,
    base_branch: str | None,
    run_git_command: Any,
    env_vars: dict[str, str],
) -> dict[str, Any]:
    """Capture replay metadata for future RQ5 corpus construction.

    This is intentionally best-effort and non-authoritative. Exporters still
    validate public-base and hidden-target tests before admitting a task.
    """

    async def git_output(args: list[str]) -> str | None:
        try:
            rc, output = await run_git_command(["git", *args], effective_workdir, env_vars)
        except Exception as exc:  # noqa: BLE001
            logger.debug("research replay hint git command failed: %s", exc)
            return None
        if rc != 0:
            return None
        return output.strip() or None

    head_commit = await git_output(["rev-parse", "HEAD"])
    base_ref = (
        f"origin/{base_branch}" if isinstance(base_branch, str) and base_branch else "origin/HEAD"
    )
    base_commit = await git_output(["rev-parse", "--verify", base_ref])
    changed_files: list[str] = []
    if base_commit and head_commit and base_commit != head_commit:
        diff_output = await git_output(["diff", "--name-status", base_commit, head_commit, "--"])
        if diff_output:
            changed_files = _paths_from_name_status(diff_output)

    replay_files = _classify_replay_files(changed_files)
    blockers = []
    if not base_commit:
        blockers.append("missing_base_commit")
    if not head_commit:
        blockers.append("missing_head_commit")
    if not replay_files["prompt_source_pairs"]:
        blockers.append("no_prompt_source_pair")
    if not replay_files["changed_test_files"]:
        blockers.append("no_changed_tests")

    return {
        "schema_version": "pdd-research-replay-hint-v1",
        "owner": job.owner,
        "repo": job.repo,
        "issue_number": job.issue_number,
        "issue_url": job.issue_url,
        "label": str(job.label),
        "command": pdd_command,
        "base_branch": base_branch,
        "pr_url": pr_url,
        "worktree_used": effective_workdir != workdir,
        "base_commit": base_commit,
        "head_commit": head_commit,
        "changed_files": changed_files,
        **replay_files,
        "replay_contract_ready": not blockers,
        "replay_blockers": blockers,
    }


async def _process_pdd_results(
    *,
    job: Job,
    secrets: dict[str, str],
    workdir: str,
    pdd_command: str,
    output: str,
    exit_code: int,
    exec_minutes: float,
    llm_cost_usd: float,
    total_incrementally_deducted_usd: float,
    env_vars: dict[str, str],
    token: str,
    reservation_id: str | None,
    job_metadata: dict[str, Any],
    result_summary: dict[str, Any],
    has_platform_llm_keys: bool,
) -> tuple[str | None, bool]:
    """Run Phases 5-9 of the executor pipeline.

    Returns ``(reservation_id, stop_condition_handled)``:

    - ``reservation_id`` is the updated value (``None`` after finalization).
    - ``stop_condition_handled`` is ``True`` when the helper exited early
      because a PDD CLI stop condition was detected (Issue #659).  In that
      case the caller should immediately ``return result_summary`` without
      running the rest of execute_pdd_job's body — Phases 6-9 have already
      been completed by ``_handle_stop_condition_result``.

    Mutates ``result_summary`` and ``job_metadata`` in place.
    """
    # Capture patchable dependencies from orchestrator at call time so test
    # mocks on ``pdd_executor.orchestrator.X`` continue to intercept calls
    # inside this helper.
    from . import orchestrator as _orch

    os = _orch.os
    subprocess = _orch.subprocess
    asyncio = _orch.asyncio
    get_settings = _orch.get_settings
    update_job_status = _orch.update_job_status
    update_issue_status = _orch.update_issue_status
    _lookup_pat_for_user_install = _orch._lookup_pat_for_user_install
    post_issue_comment = _orch.post_issue_comment
    finalize_credit_reservation = _orch.finalize_credit_reservation
    extract_pr_url = _orch.extract_pr_url
    create_branch_and_pr = _orch.create_branch_and_pr
    _has_uncommitted_changes = _orch._has_uncommitted_changes
    _all_workflow_steps_failed = _orch._all_workflow_steps_failed
    _safe_update_progress = _orch._safe_update_progress
    _classify_pdd_outcome = _orch._classify_pdd_outcome
    _handle_stop_condition_result = _orch._handle_stop_condition_result
    _redact_secrets = _orch._redact_secrets
    JobStatus = _orch.JobStatus
    COMMAND_WORKTREE_PREFIX = _orch.COMMAND_WORKTREE_PREFIX
    COMMANDS_REQUIRING_CHANGES = _orch.COMMANDS_REQUIRING_CHANGES
    logger = _orch.logger
    _run_git_command = _orch._run_git_command
    is_internal_verification = _is_internal_verification_job(job)

    # 5. Extract Results - try PDD CLI output first, then check gh pr list, then create PR as fallback
    _safe_update_progress(job.id, "analyzing_changes", "Checking for changes...", 70)
    pr_url = extract_pr_url(output)
    fallback_pr_error: str | None = None
    requires_changes = pdd_command in COMMANDS_REQUIRING_CHANGES

    # PDD CLI commands work in git worktrees under .pdd/worktrees/.
    # Each command uses a different prefix (see COMMAND_WORKTREE_PREFIX).
    # Use the worktree as the effective workdir for fallback PR creation
    # so we capture ALL files the CLI created — not just main workdir
    # artifacts (architecture.json, sync_order.sh) which are incomplete.
    effective_workdir = workdir
    wt_prefix = COMMAND_WORKTREE_PREFIX.get(pdd_command)
    if wt_prefix:
        worktree_path = os.path.join(
            workdir, ".pdd", "worktrees", f"{wt_prefix}-issue-{job.issue_number}"
        )
        if os.path.isdir(worktree_path):
            logger.info(
                f"Found pdd {pdd_command} worktree at {worktree_path}, "
                f"using it for fallback PR creation"
            )
            effective_workdir = worktree_path
            # Debug: log worktree contents so we can diagnose missing files
            try:
                wt_git_status = subprocess.run(
                    ["git", "status", "--porcelain"],
                    cwd=worktree_path,
                    capture_output=True,
                    text=True,
                    timeout=10,
                )
                wt_files = subprocess.run(
                    ["find", "prompts", "-type", "f"],
                    cwd=worktree_path,
                    capture_output=True,
                    text=True,
                    timeout=10,
                )
                logger.info(
                    f"Worktree git status: {wt_git_status.stdout.strip()[:500] or '(clean)'}"
                )
                logger.info(
                    f"Worktree prompts/: {wt_files.stdout.strip()[:200] or '(empty/missing)'}"
                )
            except Exception as e:
                logger.warning(f"Worktree debug logging failed: {e}")
    # Track whether we detected uncommitted changes that the CLI didn't push.
    # Used in result determination to prevent false success (issue #609).
    had_unpushed_changes = False
    fallback_pr_url: str | None = None

    # Issue #659: Check for stop conditions in PDD CLI output.
    # If a stop condition is present, skip PR creation entirely — post a
    # clarification comment and remove trigger labels so the job doesn't
    # re-run automatically.  See _handle_stop_condition_result for the
    # full orchestrated-vs-standalone branching logic.
    handled, reservation_id = await _handle_stop_condition_result(
        job=job,
        secrets=secrets,
        pdd_command=pdd_command,
        output=output,
        pr_url=pr_url,
        token=token,
        exec_minutes=exec_minutes,
        llm_cost_usd=llm_cost_usd,
        total_incrementally_deducted_usd=total_incrementally_deducted_usd,
        reservation_id=reservation_id,
        job_metadata=job_metadata,
        result_summary=result_summary,
    )
    if handled:
        return reservation_id, True

    if not pr_url and not is_internal_verification:
        # PDD CLI output didn't contain a PR URL - check if CLI already created a PR via gh.
        # Retry up to 3 times with 2s delay to handle GitHub API eventual consistency:
        # a PR created by the CLI (e.g. Step 12 of pdd bug) may not be immediately
        # visible in gh pr list (issue #689).
        for _pr_check_attempt in range(3):
            try:
                exit_code, pr_check_output = await _run_git_command(
                    [
                        "gh",
                        "pr",
                        "list",
                        "--state",
                        "open",
                        "--json",
                        "url,headRefName",
                        "--jq",
                        f'.[] | select(.headRefName | endswith("/issue-{job.issue_number}")) | .url',
                    ],
                    workdir,
                    env_vars,
                )
                if exit_code == 0 and pr_check_output.strip():
                    pr_url = pr_check_output.strip().split("\n")[0]
                    logger.info(f"Found existing PR via gh pr list: {pr_url}")
                    break
            except Exception as e:
                logger.debug(f"Pre-fallback PR check failed: {e}")
            if _pr_check_attempt < 2:
                logger.debug(f"PR not found on attempt {_pr_check_attempt + 1}, retrying in 2s...")
                await asyncio.sleep(2)

    if not pr_url and not is_internal_verification:
        # No PR found via output or gh pr list - create one ourselves if there are changes
        # This ensures all commands end with a PR for the user to review
        _safe_update_progress(job.id, "creating_pr", "Creating pull request...", 85)
        logger.info("No PR URL in PDD output. Creating PR for any uncommitted changes.")
        try:
            pr_url = await create_branch_and_pr(
                job.owner,
                job.repo,
                job.issue_number,
                effective_workdir,
                env_vars,
                job.label,
                getattr(job, "base_branch", None),
            )
        except RuntimeError as e:
            fallback_pr_error = _redact_secrets(str(e), secrets)
            logger.warning(f"PR creation failed: {fallback_pr_error}")
    elif (
        not is_internal_verification
        and requires_changes
        and _has_uncommitted_changes(effective_workdir)
    ):
        # Issue #609: PDD CLI output contains a PR URL (possibly from a prior
        # step like `pdd bug`), but there are uncommitted local changes that
        # need to be committed and pushed. Without this, the fix would be
        # silently discarded when the temp directory is cleaned up.
        #
        # effective_workdir points to the CLI's worktree
        # (.pdd/worktrees/{prefix}-issue-N/) so we commit from there —
        # capturing all files the CLI created rather than the main
        # workdir's incomplete artifacts.
        had_unpushed_changes = True
        _safe_update_progress(job.id, "creating_pr", "Pushing uncommitted changes...", 85)
        logger.info(
            f"PR URL found in CLI output ({pr_url}) but effective_workdir has uncommitted "
            f"changes. Calling create_branch_and_pr to commit/push them. "
            f"(effective_workdir={effective_workdir})"
        )
        try:
            fallback_pr_url = await create_branch_and_pr(
                job.owner,
                job.repo,
                job.issue_number,
                effective_workdir,
                env_vars,
                job.label,
                getattr(job, "base_branch", None),
            )
            if fallback_pr_url:
                pr_url = fallback_pr_url
        except RuntimeError as e:
            fallback_pr_error = _redact_secrets(str(e), secrets)
            logger.warning(f"PR creation failed: {fallback_pr_error}")

    # 5b. Retarget CLI-created PRs to the correct base branch.
    # The CLI's prompt templates hardcode --base main, but when the executor
    # specifies a non-main base_branch (e.g. a feature branch for decomposed
    # sub-issues), we retarget the PR so it merges into the correct branch.
    # isinstance(str) check is important: tests may pass MagicMock jobs where
    # job.base_branch is a truthy MagicMock, not a real branch name.
    base_branch = getattr(job, "base_branch", None)
    if (
        pr_url
        and not is_internal_verification
        and isinstance(base_branch, str)
        and base_branch
        and base_branch != "main"
    ):
        pr_number_match = re.search(r"/pull/(\d+)", pr_url)
        if pr_number_match:
            pr_number = pr_number_match.group(1)
            try:
                # Verify the target branch exists before retargeting.
                # The orchestrator's create_branch may have failed silently,
                # leaving base_branch set but no actual branch on the remote.
                branch_check_rc, _ = await _run_git_command(
                    [
                        "gh",
                        "api",
                        f"repos/{job.owner}/{job.repo}/branches/{base_branch}",
                        "--silent",
                    ],
                    workdir,
                    env_vars,
                )
                if branch_check_rc != 0:
                    logger.warning(
                        "Skipping retarget: branch '%s' does not exist on %s/%s",
                        base_branch,
                        job.owner,
                        job.repo,
                    )
                else:
                    retarget_rc, retarget_output = await _run_git_command(
                        ["gh", "pr", "edit", pr_number, "--base", base_branch],
                        workdir,
                        env_vars,
                    )
                    if retarget_rc == 0:
                        logger.info("Retargeted PR #%s from main to %s", pr_number, base_branch)
                    else:
                        logger.warning(
                            "Failed to retarget PR #%s to %s: %s",
                            pr_number,
                            base_branch,
                            retarget_output[:200],
                        )
            except Exception as e:
                # Non-blocking: if retarget fails, log and continue.
                # PR will still be mergeable to main (just not optimal target).
                logger.warning(
                    "Exception retargeting PR #%s to %s (non-fatal): %s",
                    pr_number,
                    base_branch,
                    str(e)[:200],
                )

    # 6. Calculate total cost: infrastructure (always) + LLM (already parsed above)
    settings = get_settings()
    infra_cost_usd = exec_minutes * settings.CONNECT_INFRASTRUCTURE_RATE_PER_MINUTE
    cost_usd = infra_cost_usd + llm_cost_usd

    logger.info(
        f"Job {job.id} cost breakdown: "
        f"infra=${infra_cost_usd:.4f} ({exec_minutes:.1f} min) + "
        f"LLM=${llm_cost_usd:.4f} (platform_keys={has_platform_llm_keys}) = "
        f"total=${cost_usd:.4f}"
    )

    result_summary["pr_url"] = pr_url
    result_summary["cost_usd"] = cost_usd
    result_summary["infra_cost_usd"] = infra_cost_usd
    result_summary["llm_cost_usd"] = llm_cost_usd
    result_summary["exec_minutes"] = round(exec_minutes, 1)
    result_summary["model"] = job.model_override or "default"
    job_metadata["pr_url"] = pr_url
    if is_internal_verification:
        result_summary["research_replay_hint"] = {
            "schema_version": "pdd-research-replay-hint-v1",
            "replay_contract_ready": False,
            "replay_blockers": ["internal_verification_job"],
        }
    else:
        try:
            result_summary["research_replay_hint"] = await _build_research_replay_hint(
                job=job,
                workdir=workdir,
                effective_workdir=effective_workdir,
                pdd_command=pdd_command,
                pr_url=pr_url,
                base_branch=base_branch,
                run_git_command=_run_git_command,
                env_vars=env_vars,
            )
        except Exception as exc:  # noqa: BLE001
            logger.warning("Failed to build research replay hint for job %s: %s", job.id, exc)
            result_summary["research_replay_hint"] = {
                "schema_version": "pdd-research-replay-hint-v1",
                "replay_contract_ready": False,
                "replay_blockers": ["hint_generation_failed"],
                "error": str(exc)[:500],
            }

    # 7. Determine actual outcome
    all_steps_failed = _all_workflow_steps_failed(workdir, job.issue_number)
    comment_header, result_line = _classify_pdd_outcome(
        result_summary,
        all_steps_failed=all_steps_failed,
        pr_url=pr_url,
        had_unpushed_changes=had_unpushed_changes,
        fallback_pr_url=fallback_pr_url,
        fallback_pr_error=fallback_pr_error,
        requires_changes=requires_changes,
    )

    # 8. Finalize Credit Reservation with actual cost
    #    All users pay infra; platform-key users also pay LLM.
    #    Account for costs already deducted incrementally during execution.
    remaining_cost = max(0.0, cost_usd - total_incrementally_deducted_usd)
    # ``reservation_id`` was set successfully back in step 1; if we ever
    # reach this finalize call with it still unset that's a control-flow
    # bug, so assert (also narrows the type for mypy).
    assert reservation_id is not None, (
        "execute_pdd_job reached finalize without an active reservation"
    )
    await finalize_credit_reservation(reservation_id, job.user_uid, remaining_cost, job_metadata)
    reservation_id = None  # Mark as finalized so the finally block doesn't release it
    logger.info(
        f"Job {job.id}: Total cost ${cost_usd:.4f} "
        f"(incremental: ${total_incrementally_deducted_usd:.4f}, "
        f"finalized: ${remaining_cost:.4f})."
    )

    # 9. Post comment and update status. Internal verification jobs are
    # machine-only checkup executions; the solving orchestrator owns their
    # user-visible comments and project-board transitions after parsing the
    # verifier report.
    if not is_internal_verification:
        comment_body = (
            f"{comment_header}\n\n"
            f"**Command:** `{pdd_command}`\n"
            f"**Duration:** {exec_minutes:.1f} min\n"
        )
        if has_platform_llm_keys:
            comment_body += (
                f"**Cost:** ${cost_usd:.4f} "
                f"(infra: ${infra_cost_usd:.4f} + LLM: ${llm_cost_usd:.4f})\n"
            )
        else:
            comment_body += f"**Cost:** ${infra_cost_usd:.4f} infra (LLM billed to your API keys)\n"
        comment_body += result_line

        await post_issue_comment(job.owner, job.repo, job.issue_number, comment_body, token)
    else:
        logger.info(
            "Skipping generic issue comment/project-board update for internal verification job %s",
            job.id,
        )

    if result_summary["success"]:
        progress_message = (
            "Verification job completed successfully!"
            if is_internal_verification
            else "Job completed successfully!"
        )
        _safe_update_progress(job.id, "completed", progress_message, 100)
        await update_job_status(job.id, JobStatus.COMPLETED, result=result_summary)
    else:
        _safe_update_progress(
            job.id,
            "failed",
            str(result_summary.get("error", "Job failed"))[:2000],
            -1,
        )
        await update_job_status(job.id, JobStatus.FAILED, result=result_summary)

    if result_summary["success"] and not is_internal_verification:
        pat_token = await _lookup_pat_for_user_install(job)
        await update_issue_status(
            job.owner,
            job.repo,
            job.issue_number,
            "complete",
            job.installation_id,
            token,
            pat_token=pat_token,
        )

    return reservation_id, False
