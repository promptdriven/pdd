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

import re
import shutil
import subprocess
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Union

from rich.console import Console

from .agentic_common import (
    DEFAULT_MAX_RETRIES,
    clear_workflow_state,
    load_workflow_state,
    run_agentic_task,
    save_workflow_state,
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

    # Safe substitution (Issue #549): un-double template literal braces from preprocess()
    # first, then substitute context keys. This preserves JSON braces in context values.
    prompt_template = prompt_template.replace("{{", "{").replace("}}", "}")
    formatted_prompt = prompt_template
    for key, value in context.items():
        formatted_prompt = formatted_prompt.replace(f'{{{key}}}', str(value))

    success, output, cost, model = run_agentic_task(
        instruction=formatted_prompt,
        cwd=step_cwd,
        verbose=verbose,
        quiet=quiet,
        label=label,
        timeout=CHECKUP_STEP_TIMEOUTS.get(step_num, 600.0) + timeout_adder,
        max_retries=DEFAULT_MAX_RETRIES,
    )
    return (success, output, cost, model)


# ---------------------------------------------------------------------------
# Orchestrator
# ---------------------------------------------------------------------------


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
) -> Tuple[bool, str, float, str]:
    """Orchestrate the 8-step agentic checkup workflow.

    Returns:
        (success, final_message, total_cost, model_used)
    """
    if not quiet:
        console.print(f"[bold]Running checkup for issue #{issue_number}: \"{issue_title}\"[/bold]")

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
    }

    total_cost = 0.0
    last_model_used = "unknown"
    changed_files: List[str] = []
    current_cwd = cwd
    worktree_path: Optional[Path] = None
    github_comment_id: Optional[int] = None

    # Resume: load existing state if available.
    state_dir = _get_state_dir(cwd)
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
                # Recreate worktree with existing branch
                wt_path, err = _setup_worktree(cwd, issue_number, quiet, resume_existing=True)
                if err:
                    return False, f"Failed to recreate worktree on resume: {err}", total_cost, last_model_used
                worktree_path = wt_path
                current_cwd = worktree_path
            context["worktree_path"] = str(worktree_path)

        # Restore context from cached step outputs.
        # State keys use underscores (e.g. "6_1"); context keys follow suit.
        # No brace escaping needed: safe str.replace() substitution preserves JSON braces (Issue #549).
        for step_key, output in step_outputs.items():
            context[f"step{step_key}_output"] = output

        # Restore files_to_stage if available
        if changed_files:
            context["files_to_stage"] = ", ".join(changed_files)

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
        )
        github_comment_id = save_workflow_state(
            cwd=cwd, issue_number=issue_number, workflow_type="checkup",
            state=new_state, state_dir=state_dir,
            repo_owner=repo_owner, repo_name=repo_name,
            use_github_state=use_github_state,
            github_comment_id=github_comment_id,
        )

    def _handle_step_result(
        step_num: Union[int, float],
        success: bool,
        output: str,
        cost: float,
        model: str,
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
        # No brace escaping needed: safe str.replace() substitution preserves JSON braces (Issue #549).
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
        else:
            step_outputs[step_key] = f"FAILED: {output}"
            if "All agent providers failed" in output:
                consecutive_provider_failures += 1
                if consecutive_provider_failures >= 3:
                    _save_state()
                    return (
                        False,
                        f"Aborting: {consecutive_provider_failures} consecutive "
                        f"steps failed - agent providers unavailable",
                        total_cost,
                        last_model_used,
                    )
            else:
                consecutive_provider_failures = 0

        _save_state()
        return None

    # ==================================================================
    # Section 1: Steps 1-2 (linear, run once)
    # ==================================================================

    for step_num in (1, 2):
        if step_num < start_step:
            continue

        name, description = step_map[step_num]
        if not quiet:
            console.print(f"[bold][Step {step_num}/{TOTAL_STEPS}][/bold] {description}...")

        result = _run_single_step(
            step_num, name, context,
            cwd=cwd, step_cwd=cwd,
            verbose=verbose, quiet=quiet,
            label=f"step{step_num}",
            timeout_adder=timeout_adder,
        )

        if result is None:
            template_name = f"agentic_checkup_step{step_num}_{name}_LLM"
            return (False, f"Missing prompt template: {template_name}", total_cost, last_model_used)

        success, output, cost, model = result

        abort = _handle_step_result(step_num, success, output, cost, model)
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
        for step_num in (3, 4, 5):
            if step_num < start_step:
                continue
            name, description = step_map[step_num]
            if not quiet:
                console.print(f"[bold][Step {step_num}/{TOTAL_STEPS}][/bold] {description}...")

            result = _run_single_step(
                step_num, name, context,
                cwd=cwd, step_cwd=cwd,
                verbose=verbose, quiet=quiet,
                label=f"step{step_num}",
                timeout_adder=timeout_adder,
            )

            if result is None:
                template_name = f"agentic_checkup_step{step_num}_{name}_LLM"
                return (False, f"Missing prompt template: {template_name}", total_cost, last_model_used)

            success, output, cost, model = result
            abort = _handle_step_result(step_num, success, output, cost, model)
            if abort is not None:
                return abort

        # Skip step 6 sub-steps.
        for sub_step in (6.1, 6.2, 6.3):
            if sub_step >= start_step:
                sub_key = str(sub_step).replace(".", "_")
                disp = _display_step.get(sub_step, str(sub_step))
                if not quiet:
                    console.print(
                        f"[bold][Step {disp}/{TOTAL_STEPS}][/bold] Skipped (--no-fix mode)"
                    )
                escaped = "Skipped: --no-fix mode"
                step_outputs[sub_key] = escaped
                context[f"step{sub_key}_output"] = escaped
                last_completed_step_to_save = sub_step
        if any(s >= start_step for s in (6.1, 6.2, 6.3)):
            _save_state()

        # Run step 7.
        if 7 >= start_step:
            name7, desc7 = step_map[7]
            if not quiet:
                console.print(f"[bold][Step 7/{TOTAL_STEPS}][/bold] {desc7}...")

            result = _run_single_step(
                7, name7, context,
                cwd=cwd, step_cwd=cwd,
                verbose=verbose, quiet=quiet,
                label="step7",
                timeout_adder=timeout_adder,
            )

            if result is None:
                template_name = f"agentic_checkup_step7_{name7}_LLM"
                return (False, f"Missing prompt template: {template_name}", total_cost, last_model_used)

            success, output, cost, model = result
            abort = _handle_step_result(7, success, output, cost, model)
            if abort is not None:
                return abort

        # Skip step 8.
        if 8 >= start_step:
            if not quiet:
                console.print(f"[bold][Step 8/{TOTAL_STEPS}][/bold] Skipped (--no-fix mode)")
            escaped = "Skipped: --no-fix mode"
            step_outputs["8"] = escaped
            context["step8_output"] = escaped
            last_completed_step_to_save = 8
            _save_state()

    else:
        # --- Fix mode: iterative loop over steps 3-7 ---

        # Create worktree before first loop iteration.
        if worktree_path is None and start_step <= 7:
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
                )

                if result is None:
                    tmpl_name = f"agentic_checkup_step{step_str}_{name}_LLM"
                    return (False, f"Missing prompt template: {tmpl_name}", total_cost, last_model_used)

                success, output, cost, model = result
                abort = _handle_step_result(step_num, success, output, cost, model)
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
            if not quiet:
                console.print(
                    f"[yellow]Warning: Max fix-verify iterations "
                    f"({MAX_FIX_VERIFY_ITERATIONS}) reached. "
                    f"Proceeding to PR creation.[/yellow]"
                )

        # ==============================================================
        # Section 3: Step 8 (create PR) — after the loop
        # ==============================================================

        if 8 >= start_step or fix_verify_iteration > 0:
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
            )

            if result is None:
                template_name = f"agentic_checkup_step8_{name8}_LLM"
                return (False, f"Missing prompt template: {template_name}", total_cost, last_model_used)

            success, output, cost, model = result
            abort = _handle_step_result(8, success, output, cost, model)
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

    return True, final_msg, total_cost, last_model_used


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
) -> Dict:
    """Build a serialisable state dict for persistence."""
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
    }
