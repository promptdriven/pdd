"""
Orchestrator for the 9-step agentic test generation workflow.
Runs each step as a separate agentic task, accumulates context between steps,
tracks overall progress and cost, and supports resuming from saved state.
"""

from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any

from rich.console import Console
from rich.markup import escape

from pdd.agentic_common import (
    run_agentic_task,
    load_workflow_state,
    save_workflow_state,
    clear_workflow_state,
    DEFAULT_MAX_RETRIES,
)
from pdd.load_prompt_template import load_prompt_template

# Initialize console for rich output
console = Console()

# Per-Step Timeouts (Workflow specific)
TEST_STEP_TIMEOUTS: Dict[int, float] = {
    1: 240.0,   # Duplicate Check
    2: 400.0,   # Docs Check
    3: 400.0,   # Analyze & Clarify
    4: 340.0,   # Detect Frontend
    5: 600.0,   # Create Test Plan
    6: 1000.0,  # Generate Tests (Most Complex)
    7: 600.0,   # Run Tests
    8: 800.0,   # Fix & Iterate
    9: 240.0,   # Submit PR
}


def _get_git_root(cwd: Path) -> Optional[Path]:
    """Get repo root via git rev-parse."""
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=cwd,
            capture_output=True,
            text=True,
            check=True
        )
        return Path(result.stdout.strip())
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None


def _worktree_exists(cwd: Path, worktree_path: Path) -> bool:
    """Check if path is in git worktree list --porcelain output."""
    git_root = _get_git_root(cwd)
    if not git_root:
        return False
    try:
        wt_list = subprocess.run(
            ["git", "worktree", "list", "--porcelain"],
            cwd=git_root,
            capture_output=True,
            text=True
        ).stdout
        return str(worktree_path) in wt_list
    except Exception:
        return False


def _branch_exists(cwd: Path, branch: str) -> bool:
    """Check via git show-ref --verify refs/heads/{branch}."""
    git_root = _get_git_root(cwd)
    if not git_root:
        return False
    try:
        subprocess.run(
            ["git", "show-ref", "--verify", f"refs/heads/{branch}"],
            cwd=git_root,
            check=True,
            capture_output=True
        )
        return True
    except subprocess.CalledProcessError:
        return False


def _remove_worktree(cwd: Path, worktree_path: Path) -> Tuple[bool, str]:
    """Remove via git worktree remove --force."""
    git_root = _get_git_root(cwd)
    if not git_root:
        return False, "Not a git repository"
    try:
        subprocess.run(
            ["git", "worktree", "remove", "--force", str(worktree_path)],
            cwd=git_root,
            capture_output=True,
            check=True
        )
        return True, ""
    except subprocess.CalledProcessError as e:
        return False, str(e)


def _delete_branch(cwd: Path, branch: str) -> Tuple[bool, str]:
    """Delete via git branch -D."""
    git_root = _get_git_root(cwd)
    if not git_root:
        return False, "Not a git repository"
    try:
        subprocess.run(
            ["git", "branch", "-D", branch],
            cwd=git_root,
            capture_output=True,
            check=True
        )
        return True, ""
    except subprocess.CalledProcessError as e:
        return False, str(e)


def _setup_worktree(cwd: Path, issue_number: int, quiet: bool) -> Tuple[Optional[Path], Optional[str]]:
    """
    Create an isolated git worktree for the issue.
    Returns (worktree_path, error_message).
    """
    git_root = _get_git_root(cwd)
    if not git_root:
        return None, "Not a git repository"

    branch_name = f"test/issue-{issue_number}"
    worktree_rel_path = Path(".pdd") / "worktrees" / f"test-issue-{issue_number}"
    worktree_path = git_root / worktree_rel_path

    # Clean up existing directory if it exists
    if worktree_path.exists():
        if _worktree_exists(cwd, worktree_path):
            success, err = _remove_worktree(cwd, worktree_path)
            if not success:
                # Fallback to rmtree if git command fails but dir exists
                try:
                    shutil.rmtree(worktree_path)
                except Exception:
                    pass
        else:
            # Just a directory
            shutil.rmtree(worktree_path)

    # Clean up branch if it exists
    if _branch_exists(cwd, branch_name):
        _delete_branch(cwd, branch_name)

    # Create worktree
    try:
        worktree_path.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["git", "worktree", "add", "-b", branch_name, str(worktree_path), "HEAD"],
            cwd=git_root,
            capture_output=True,
            check=True
        )
        if not quiet:
            console.print(f"[blue]Working in worktree: {worktree_path}[/blue]")
        return worktree_path, None
    except subprocess.CalledProcessError as e:
        return None, f"Git worktree creation failed: {e}"


def _parse_changed_files(output: str) -> List[str]:
    """Extract file paths from FILES_CREATED or FILES_MODIFIED lines."""
    files = []
    # Look for FILES_CREATED: path, path
    created_match = re.search(r"FILES_CREATED:\s*(.*)", output)
    if created_match:
        files.extend([f.strip().strip("*").strip() for f in created_match.group(1).split(",") if f.strip()])
    
    # Look for FILES_MODIFIED: path, path
    modified_match = re.search(r"FILES_MODIFIED:\s*(.*)", output)
    if modified_match:
        files.extend([f.strip().strip("*").strip() for f in modified_match.group(1).split(",") if f.strip()])
        
    return list(set(files))  # Deduplicate


def _check_hard_stop(step_num: int, output: str) -> Optional[str]:
    """Check output for hard stop conditions."""
    if step_num == 1 and "Duplicate of #" in output:
        return "Issue is a duplicate"
    if step_num == 3 and "Needs More Info" in output:
        return "Needs more info from author"
    if step_num == 5 and "PLAN_BLOCKED" in output:
        return "Test plan not achievable"
    if step_num == 6:
        # Check if files were generated
        files = _parse_changed_files(output)
        if not files:
            return "No test file generated"
    return None


def _get_state_dir(cwd: Path) -> Path:
    """Get the state directory relative to git root."""
    root = _get_git_root(cwd) or cwd
    return root / ".pdd" / "test-state"


def run_agentic_test_orchestrator(
    issue_url: str,
    issue_content: str,
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    issue_author: str,
    issue_title: str,
    *,
    cwd: Path,
    verbose: bool = False,
    quiet: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Orchestrates the 9-step agentic test generation workflow.
    
    Returns:
        (success, final_message, total_cost, model_used, changed_files)
    """
    
    if not quiet:
        console.print(f"Generating tests for issue #{issue_number}: \"{issue_title}\"")

    state_dir = _get_state_dir(cwd)

    # Load state
    state, loaded_gh_id = load_workflow_state(
        cwd, issue_number, "test", state_dir, repo_owner, repo_name, use_github_state
    )

    # Initialize variables from state or defaults
    if state is not None:
        last_completed_step = state.get("last_completed_step", 0)
        step_outputs = state.get("step_outputs", {})
        total_cost = state.get("total_cost", 0.0)
        model_used = state.get("model_used", "unknown")
        github_comment_id = loaded_gh_id
        worktree_path_str = state.get("worktree_path")
        worktree_path = Path(worktree_path_str) if worktree_path_str else None
    else:
        state = {"step_outputs": {}}
        last_completed_step = 0
        step_outputs = state["step_outputs"]
        total_cost = 0.0
        model_used = "unknown"
        github_comment_id = None
        worktree_path = None

    context = {
        "issue_url": issue_url,
        "issue_content": issue_content,
        "repo_owner": repo_owner,
        "repo_name": repo_name,
        "issue_number": issue_number,
        "issue_author": issue_author,
        "issue_title": issue_title,
    }
    
    # Populate context with previous step outputs
    for s_num, s_out in step_outputs.items():
        context[f"step{s_num}_output"] = s_out

    # Re-extract files from step 6/8 outputs if available
    changed_files = []
    if "step6_output" in context:
        s6_out = context["step6_output"]
        changed_files.extend(_parse_changed_files(s6_out))
    
    if "step8_output" in context:
        s8_out = context["step8_output"]
        new_files = _parse_changed_files(s8_out)
        for f in new_files:
            if f not in changed_files:
                changed_files.append(f)

    if changed_files:
        context["files_to_stage"] = ", ".join(changed_files)
        context["test_files"] = "\n".join(f"- {f}" for f in changed_files)

    if "step7_output" in context:
        context["test_results"] = context["step7_output"]

    start_step = last_completed_step + 1
    
    if last_completed_step > 0 and not quiet:
        console.print(f"Resuming test generation for issue #{issue_number}")
        console.print(f"   Steps 1-{last_completed_step} already complete (cached)")
        console.print(f"   Starting from Step {start_step}")

    steps_config = [
        (1, "duplicate", "Search for duplicate test requests"),
        (2, "docs", "Review codebase"),
        (3, "clarify", "Determine if enough info"),
        (4, "detect_frontend", "Identify test type"),
        (5, "test_plan", "Create test plan"),
        (6, "generate_tests", "Generate tests"),
        (7, "run_tests", "Execute generated tests"),
        (8, "fix_iterate", "Fix failing tests"),
        (9, "submit_pr", "Create draft PR"),
    ]

    current_work_dir = cwd

    # If resuming at step 6 or later, ensure worktree is set up
    if start_step >= 6:
        if worktree_path and worktree_path.exists():
             if not quiet:
                console.print(f"[blue]Reusing existing worktree: {worktree_path}[/blue]")
             current_work_dir = worktree_path
             context["worktree_path"] = str(worktree_path)
        else:
            # If state says we have a worktree but it's gone, or we need one now
            wt_path, err = _setup_worktree(cwd, issue_number, quiet)
            if not wt_path:
                return False, f"Failed to restore worktree: {err}", total_cost, model_used, []
            worktree_path = wt_path
            current_work_dir = worktree_path
            state["worktree_path"] = str(worktree_path)
            context["worktree_path"] = str(worktree_path)

    for step_num, name, description in steps_config:
        if step_num < start_step:
            continue

        # Worktree setup before Step 6
        if step_num == 6:
            if worktree_path and worktree_path.exists():
                 current_work_dir = worktree_path
                 if not quiet:
                     console.print(f"[blue]Using existing worktree: {worktree_path}[/blue]")
            else:
                try:
                    current_branch = subprocess.run(
                        ["git", "rev-parse", "--abbrev-ref", "HEAD"],
                        cwd=cwd,
                        capture_output=True,
                        text=True,
                        check=True
                    ).stdout.strip()
                    if current_branch not in ["main", "master"] and not quiet:
                        console.print(f"[yellow]Note: Creating branch from HEAD ({current_branch}), not origin/main. PR will include commits from this branch. Run from main for independent changes.[/yellow]")
                except (subprocess.CalledProcessError, FileNotFoundError):
                    pass

                wt_path, err = _setup_worktree(cwd, issue_number, quiet)
                if not wt_path:
                    return False, f"Failed to create worktree: {err}", total_cost, model_used, []
                worktree_path = wt_path
                current_work_dir = worktree_path
                state["worktree_path"] = str(worktree_path)
                context["worktree_path"] = str(worktree_path)

        if not quiet:
            console.print(f"[bold][Step {step_num}/9][/bold] {description}...")

        template_name = f"agentic_test_step{step_num}_{name}_LLM"
        prompt_template = load_prompt_template(template_name)
        if not prompt_template:
            return False, f"Missing prompt template: {template_name}", total_cost, model_used, []

        try:
            formatted_prompt = prompt_template.format(**context)
        except KeyError as e:
            return False, f"Context missing key for step {step_num}: {e}", total_cost, model_used, []

        timeout = TEST_STEP_TIMEOUTS.get(step_num, 340.0) + timeout_adder
        step_success, step_output, step_cost, step_model = run_agentic_task(
            instruction=formatted_prompt,
            cwd=current_work_dir,
            verbose=verbose,
            quiet=quiet,
            timeout=timeout,
            label=f"step{step_num}",
            max_retries=DEFAULT_MAX_RETRIES,
        )

        total_cost += step_cost
        model_used = step_model
        state["total_cost"] = total_cost
        state["model_used"] = model_used

        # Check for hard stops even if success is True (agent might report success but found a blocker)
        stop_reason = _check_hard_stop(step_num, step_output)
        if stop_reason:
            if not quiet:
                console.print(f"[yellow]Investigation stopped at Step {step_num}: {stop_reason}[/yellow]")
            state["last_completed_step"] = step_num
            state["step_outputs"][str(step_num)] = step_output
            save_workflow_state(cwd, issue_number, "test", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
            return False, f"Stopped at step {step_num}: {stop_reason}", total_cost, model_used, changed_files

        if not step_success:
            # Soft failure logic: log warning but continue unless it was a hard stop above
            console.print(f"[yellow]Warning: Step {step_num} reported failure but continuing...[/yellow]")

        # File extraction logic
        if step_num == 6:
            extracted_files = _parse_changed_files(step_output)
            changed_files = extracted_files
            context["files_to_stage"] = ", ".join(changed_files)
            context["test_files"] = "\n".join(f"- {f}" for f in changed_files) if changed_files else "No test files detected"

        if step_num == 7:
            context["test_results"] = step_output

        if step_num == 8:
            # Update files if fixes created new ones
            new_files = _parse_changed_files(step_output)
            for f in new_files:
                if f not in changed_files:
                    changed_files.append(f)
            context["files_to_stage"] = ", ".join(changed_files)

        context[f"step{step_num}_output"] = step_output
        
        if step_success:
            state["step_outputs"][str(step_num)] = step_output
            state["last_completed_step"] = step_num
        else:
            state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"

        save_result = save_workflow_state(cwd, issue_number, "test", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
        if save_result:
            github_comment_id = save_result
            state["github_comment_id"] = github_comment_id

        if not quiet:
            lines = step_output.strip().split('\n')
            brief = lines[-1] if lines else "Done"
            if len(brief) > 80: brief = brief[:77] + "..."
            console.print(f"   -> {escape(brief)}")

    # Final Summary
    pr_url = "Unknown"
    if "step9_output" in context:
        s9_out = context["step9_output"]
        url_match = re.search(r"https://github.com/\S+/pull/\d+", s9_out)
        if url_match:
            pr_url = url_match.group(0)

    if not quiet:
        console.print("\n[green]Test generation complete[/green]")
        console.print(f"   Total cost: ${total_cost:.4f}")
        console.print(f"   Files created: {', '.join(changed_files)}")
        if worktree_path:
            console.print(f"   Worktree: {worktree_path}")
        console.print(f"   PR created: {pr_url}")

    clear_workflow_state(cwd, issue_number, "test", state_dir, repo_owner, repo_name, use_github_state)
    
    final_msg = f"PR Created: {pr_url}" if pr_url != "Unknown" else "Workflow completed"
    return True, final_msg, total_cost, model_used, changed_files