from __future__ import annotations

import sys
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from rich.console import Console

project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

from pdd.agentic_e2e_fix_orchestrator import run_agentic_e2e_fix_orchestrator

console = Console()


def mock_load_prompt_template(template_name: str) -> str:
    """Return a minimal prompt template for the requested step."""
    return (
        f"Template: {template_name}\n"
        "Issue #{issue_number}\n"
        "Cycle {cycle_number}/{max_cycles}\n"
        "Protect tests: {protect_tests_flag}"
    )


def mock_run_agentic_task(
    instruction: str,
    cwd: Path,
    *,
    label: str,
    **_: object,
) -> tuple[bool, str, float, str]:
    """Simulate a successful single-cycle E2E fix workflow."""
    if "step1" in label:
        return True, "Unit tests reproduced the failure.", 0.04, "gpt-4.1"
    if "step2" in label:
        return True, "E2E tests failed in the login flow.", 0.04, "gpt-4.1"
    if "step3" in label:
        return True, "CODE_BUG: stale retry logic.", 0.05, "gpt-4.1"
    if "step4" in label:
        return True, "Applied targeted E2E fix.\nFILES_MODIFIED: src/login.py", 0.06, "gpt-4.1"
    if "step5" in label:
        return True, "DEV_UNITS_IDENTIFIED: src/login.py", 0.05, "gpt-4.1"
    if "step6" in label:
        return True, "FILES_CREATED: tests/test_login.py", 0.05, "gpt-4.1"
    if "step7" in label:
        return True, "The new unit test fails before the fix and passes after it.", 0.05, "gpt-4.1"
    if "step8" in label:
        return True, "src/login.py: FIXED\nFILES_MODIFIED: src/login.py, tests/test_login.py", 0.08, "gpt-4.1"
    if "step9" in label:
        return True, "Verification complete.\nALL_TESTS_PASS", 0.05, "gpt-4.1"
    return False, f"Unexpected label: {label}", 0.0, "gpt-4.1"


def _fetch_pr_head_sha(repo_owner: str, repo_name: str, pr_number: int) -> str:
    """Best-effort fetch of the PR's remote head SHA. Empty string on failure."""
    try:
        from pdd.checkup_review_loop import _fetch_pr_metadata
        metadata = _fetch_pr_metadata(repo_owner, repo_name, pr_number)
    except Exception:  # best-effort; empty means "can't compare"
        return ""
    return str(metadata.get("head_sha", "") or "")


def _read_checkup_worktree_head_sha(cwd: Path, pr_number: int) -> str:
    """Read HEAD SHA of the PR-mode checkup worktree.

    The checkup orchestrator creates .pdd/worktrees/checkup-pr-{N}/ under
    the repo's git root. After run_agentic_checkup returns, that worktree's
    HEAD is the *exact* SHA the checkup's verdict and push apply to.
    Comparing it to the live PR remote SHA distinguishes a checkup
    self-push from an external party advancing the PR during the checkup.
    """
    import subprocess
    try:
        toplevel = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return ""
    if toplevel.returncode != 0:
        return ""
    worktree = Path(toplevel.stdout.strip()) / ".pdd" / "worktrees" / f"checkup-pr-{pr_number}"
    if not worktree.exists():
        return ""
    try:
        rev = subprocess.run(
            ["git", "-C", str(worktree), "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return ""
    if rev.returncode != 0:
        return ""
    return rev.stdout.strip()


def _run_final_checkup_on_pr(
    *,
    issue_url: str,
    issue_number: int,
    repo_owner: str,
    repo_name: str,
    cwd: Path,
    verbose: bool,
    quiet: bool,
    timeout_adder: float,
    use_github_state: bool,
    reasoning_time: float | None,
    ci_step_template: str,
    ci_validation_timeout: float,
) -> tuple[bool, str, float, str]:
    """Run full PR-mode checkup against the current branch's open PR.

    Closes the post-CI mutation hole: the checkup runs with no_fix=False
    and may push fixes that advance the PR head past the CI-validated SHA.
    Snapshot before/after; if the head advanced, re-run CI on the new SHA
    with max_retries=0 (verify-only). Fail closed when either SHA is empty.
    """
    from pdd.agentic_checkup import run_agentic_checkup
    from pdd.agentic_common import run_agentic_task
    from pdd.ci_validation import _find_open_pr_number, run_ci_validation_loop

    pr_number = _find_open_pr_number(repo_owner, repo_name, cwd)
    if pr_number is None:
        return (
            True,
            "No open PR found for current branch; skipping final checkup",
            0.0,
            "",
        )

    pre_checkup_head_sha = _fetch_pr_head_sha(repo_owner, repo_name, pr_number)

    pr_url = f"https://github.com/{repo_owner}/{repo_name}/pull/{pr_number}"
    checkup_success, checkup_message, checkup_cost, checkup_model = run_agentic_checkup(
        issue_url=issue_url,
        verbose=verbose,
        quiet=quiet,
        no_fix=False,
        timeout_adder=timeout_adder,
        use_github_state=use_github_state,
        reasoning_time=reasoning_time,
        pr_url=pr_url,
        cwd=cwd,
    )

    if not checkup_success:
        return checkup_success, checkup_message, checkup_cost, checkup_model

    if not pre_checkup_head_sha:
        return (
            False,
            (
                "Final checkup completed but the pre-checkup PR head SHA was "
                "unavailable; cannot verify whether checkup pushed new commits "
                "that bypass CI."
            ),
            checkup_cost,
            checkup_model,
        )

    post_checkup_head_sha = _fetch_pr_head_sha(repo_owner, repo_name, pr_number)
    if not post_checkup_head_sha:
        return (
            False,
            (
                "Final checkup completed but the post-checkup PR head SHA was "
                "unavailable; cannot verify whether checkup pushed new commits "
                "that bypass CI."
            ),
            checkup_cost,
            checkup_model,
        )

    if post_checkup_head_sha == pre_checkup_head_sha:
        return checkup_success, checkup_message, checkup_cost, checkup_model

    # The PR head moved during the checkup, but we cannot assume the
    # checkup itself moved it. The worktree HEAD is the authoritative
    # "last verified/pushed" SHA; if it does not equal the remote PR head,
    # an external party advanced the PR during the checkup and Step 7
    # never saw the new code.
    checkup_worktree_head_sha = _read_checkup_worktree_head_sha(cwd, pr_number)
    if not checkup_worktree_head_sha:
        return (
            False,
            (
                "Final checkup completed but the checkup worktree HEAD SHA "
                "was unavailable; cannot prove the PR remote head matches "
                "what was verified. Failing closed to avoid green-lighting "
                "an unverified head."
            ),
            checkup_cost,
            checkup_model,
        )
    if checkup_worktree_head_sha != post_checkup_head_sha:
        return (
            False,
            (
                f"PR head advanced to {post_checkup_head_sha[:8]} during "
                f"final checkup but the checkup worktree last verified "
                f"{checkup_worktree_head_sha[:8]}. External push during "
                f"checkup detected — re-run pdd-issue so the new head is "
                f"verified by Step 7 before CI re-validation."
            ),
            checkup_cost,
            checkup_model,
        )

    # Pass post_checkup_head_sha as the override — the checkup pushed from
    # its own worktree, so cwd's local HEAD is stale.
    revalidate_success, revalidate_message, revalidate_cost = run_ci_validation_loop(
        cwd=cwd,
        repo_owner=repo_owner,
        repo_name=repo_name,
        issue_number=issue_number,
        max_retries=0,
        step_template=ci_step_template,
        run_agentic_task_fn=run_agentic_task,
        timeout=ci_validation_timeout,
        quiet=quiet,
        expected_head_sha_override=post_checkup_head_sha,
    )

    total_cost = checkup_cost + revalidate_cost
    if not revalidate_success:
        return (
            False,
            (
                f"Final checkup pushed fixes ({pre_checkup_head_sha[:8]}->"
                f"{post_checkup_head_sha[:8]}) but post-push CI re-validation "
                f"failed: {revalidate_message}"
            ),
            total_cost,
            checkup_model,
        )
    return True, checkup_message, total_cost, checkup_model


def main() -> None:
    """Run a local demonstration of the orchestrator with mocked dependencies."""
    with TemporaryDirectory() as temp_dir:
        cwd = Path(temp_dir)
        console.print(f"[blue]Running mocked E2E fix workflow in {cwd}[/blue]")

        with patch("pdd.agentic_e2e_fix_orchestrator.load_prompt_template", side_effect=mock_load_prompt_template), \
            patch("pdd.agentic_e2e_fix_orchestrator.run_agentic_task", side_effect=mock_run_agentic_task), \
            patch("pdd.agentic_e2e_fix_orchestrator.load_workflow_state", return_value=(None, None)), \
            patch("pdd.agentic_e2e_fix_orchestrator.save_workflow_state", return_value=None), \
            patch("pdd.agentic_e2e_fix_orchestrator.clear_workflow_state"), \
            patch("pdd.agentic_e2e_fix_orchestrator._check_e2e_environment", return_value=(True, "")), \
            patch("pdd.agentic_e2e_fix_orchestrator._extract_test_files", return_value=["tests/test_login.py"]), \
            patch("pdd.agentic_e2e_fix_orchestrator._verify_tests_independently", return_value=(True, "1 passed")), \
            patch("pdd.agentic_e2e_fix_orchestrator._get_file_hashes", return_value={}), \
            patch(
                "pdd.agentic_e2e_fix_orchestrator._detect_changed_files",
                return_value=["src/login.py", "tests/test_login.py"],
            ), \
            patch(
                "pdd.agentic_e2e_fix_orchestrator._commit_and_push",
                return_value=(True, "Committed and pushed 2 file(s)"),
            ), \
            patch(
                "pdd.agentic_e2e_fix_orchestrator.run_ci_validation_loop",
                return_value=(True, "CI validation passed after push.", 0.02),
            ):
            success, final_message, total_cost, model_used, changed_files = run_agentic_e2e_fix_orchestrator(
                issue_url="https://github.com/example-owner/example-repo/issues/123",
                issue_content="Login E2E test fails after a retry timeout.",
                repo_owner="example-owner",
                repo_name="example-repo",
                issue_number=123,
                issue_author="example-author",
                issue_title="Fix login E2E retry failure",
                cwd=cwd,
                timeout_adder=0.0,
                max_cycles=1,
                resume=False,
                verbose=False,
                quiet=False,
                use_github_state=False,
                protect_tests=True,
                ci_retries=3,
                skip_ci=False,
            )

        console.print("\n[bold]Results[/bold]")
        console.print(f"Success: {success}")
        console.print(f"Final message: {final_message}")
        console.print(f"Total cost: ${total_cost:.2f}")
        console.print(f"Model used: {model_used}")
        console.print(f"Changed files: {changed_files}")


if __name__ == "__main__":
    main()
