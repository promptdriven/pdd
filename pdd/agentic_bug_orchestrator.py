"""
Orchestrator for the 11-step agentic bug investigation workflow.
Runs each step as a separate agentic task, accumulates context, tracks progress/cost,
and supports resuming from saved state.
"""

from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Union, Any

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
BUG_STEP_TIMEOUTS: Dict[Union[int, float], float] = {
    1: 240.0,    # Duplicate Check
    2: 400.0,    # Docs Check
    3: 400.0,    # Triage
    4: 600.0,    # Reproduce (Complex)
    5: 600.0,    # Root Cause (Complex)
    5.5: 600.0,  # Prompt Classification (may auto-fix prompts)
    6: 340.0,    # Test Plan
    7: 1000.0,   # Generate Unit Test (Most Complex)
    8: 600.0,    # Verify Unit Test
    9: 2000.0,   # E2E Test (Complex - needs to discover env & run tests)
    10: 240.0,   # Create PR
}


def _get_git_root(cwd: Path) -> Optional[Path]:
    """Get repo root via git rev-parse."""
    if not cwd.exists():
        return None
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=cwd,
            capture_output=True,
            text=True,
            check=True
        )
        return Path(result.stdout.strip())
    except subprocess.CalledProcessError:
        return None


def _setup_worktree(cwd: Path, issue_number: int, quiet: bool) -> Tuple[Optional[Path], Optional[str]]:
    """
    Create an isolated git worktree for the issue.
    Returns (worktree_path, error_message).
    """
    git_root = _get_git_root(cwd)
    if not git_root:
        return None, "Not a git repository"

    branch_name = f"fix/issue-{issue_number}"
    worktree_rel_path = Path(".pdd") / "worktrees" / f"fix-issue-{issue_number}"
    worktree_path = git_root / worktree_rel_path

    # Clean up existing directory if it exists but isn't a valid worktree
    if worktree_path.exists():
        # Check if it's a valid worktree
        is_worktree = False
        try:
            wt_list = subprocess.run(
                ["git", "worktree", "list", "--porcelain"],
                cwd=git_root,
                capture_output=True,
                text=True
            ).stdout
            if str(worktree_path) in wt_list:
                is_worktree = True
        except Exception:
            pass

        if is_worktree:
            # Remove existing worktree to start fresh or ensure clean state
            subprocess.run(
                ["git", "worktree", "remove", "--force", str(worktree_path)],
                cwd=git_root,
                capture_output=True
            )
        else:
            # Just a directory
            shutil.rmtree(worktree_path)

    # Clean up branch if it exists
    try:
        subprocess.run(
            ["git", "branch", "-D", branch_name],
            cwd=git_root,
            capture_output=True
        )
    except Exception:
        pass

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


def _parse_e2e_files(output: str) -> List[str]:
    """Extract file paths from E2E_FILES_CREATED lines."""
    files = []
    match = re.search(r"E2E_FILES_CREATED:\s*(.*)", output)
    if match:
        files.extend([f.strip().strip("*").strip() for f in match.group(1).split(",") if f.strip()])
    return list(set(files))


def _check_hard_stop(step_num: Union[int, float], output: str) -> Optional[str]:
    """Check output for hard stop conditions."""
    if step_num == 1 and "Duplicate of #" in output:
        return "Issue is a duplicate"
    if step_num == 2:
        if "Feature Request (Not a Bug)" in output:
            return "Feature Request (Not a Bug)"
        if "User Error (Not a Bug)" in output:
            return "User Error (Not a Bug)"
    if step_num == 3 and "Needs More Info" in output:
        return "Needs more info from author"
    if step_num == 5.5 and "PROMPT_REVIEW:" in output:
        # Extract reason if possible
        match = re.search(r"PROMPT_REVIEW:\s*(.*)", output)
        reason = match.group(1).strip() if match else "Prompt defect needs human review"
        return reason
    if step_num == 7:
        # Note: Missing FILES_... check is handled in logic, not just string match
        pass
    if step_num == 8 and "FAIL: Test does not work as expected" in output:
        return "Test doesn't fail correctly"
    if step_num == 9 and "E2E_FAIL: Test does not catch bug correctly" in output:
        return "E2E test doesn't catch bug"
    return None


def _get_state_dir(cwd: Path) -> Path:
    """Get the state directory relative to git root."""
    root = _get_git_root(cwd) or cwd
    return root / ".pdd" / "bug-state"


def run_agentic_bug_orchestrator(
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
    Orchestrates the 11-step agentic bug investigation workflow.
    
    Returns:
        (success, final_message, total_cost, model_used, changed_files)
    """
    
    if not quiet:
        console.print(f"🔍 Investigating issue #{issue_number}: \"{issue_title}\"")

    state_dir = _get_state_dir(cwd)

    # Load state
    state, loaded_gh_id = load_workflow_state(
        cwd, issue_number, "bug", state_dir, repo_owner, repo_name, use_github_state
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
        # Initialize fresh state dict for new workflow
        state = {"step_outputs": {}}
        last_completed_step = 0
        step_outputs = state["step_outputs"]
        total_cost = 0.0
        model_used = "unknown"
        github_comment_id = None
        worktree_path = None
    
    # Context accumulation dictionary
    context = {
        "issue_url": issue_url,
        "issue_content": issue_content,
        "repo_owner": repo_owner,
        "repo_name": repo_name,
        "issue_number": issue_number,
        "issue_author": issue_author,
        "issue_title": issue_title,
    }
    
    # Populate context with cached outputs
    for s_num, s_out in step_outputs.items():
        context[f"step{s_num}_output"] = s_out
        # Also handle float keys in string format (e.g. "5.5")
        if "." in str(s_num):
            context[f"step{str(s_num).replace('.', '_')}_output"] = s_out

    # Determine start step
    # Logic: if last_completed_step is 5, next is 5.5. If 5.5, next is 6.
    if last_completed_step == 5:
        start_step = 5.5
    elif last_completed_step == 5.5:
        start_step = 6
    else:
        start_step = last_completed_step + 1
    
    if last_completed_step > 0 and not quiet:
        console.print(f"Resuming bug investigation for issue #{issue_number}")
        console.print(f"   Steps 1-{last_completed_step} already complete (cached)")
        console.print(f"   Starting from Step {start_step}")

    # Step definitions
    # (step_num, name_suffix, description)
    steps_config: List[Tuple[Union[int, float], str, str]] = [
        (1, "duplicate", "Search for duplicate issues"),
        (2, "docs", "Check documentation for user error"),
        (3, "triage", "Assess if enough info to proceed"),
        (4, "reproduce", "Attempt to reproduce the bug"),
        (5, "root_cause", "Analyze root cause"),
        (5.5, "prompt_classification", "Classify defect: code bug vs prompt defect"),
        (6, "test_plan", "Design test strategy"),
        (7, "generate", "Generate failing unit test"),
        (8, "verify", "Verify test catches the bug"),
        (9, "e2e_test", "Generate and run E2E tests"),
        (10, "pr", "Create draft PR and link to issue"),
    ]

    current_work_dir = cwd
    changed_files: List[str] = []

    # Re-hydrate changed_files from previous steps if resuming late
    # Specifically check step 5.5 (prompt fixes) and step 7 (unit tests)
    # Note: step_outputs keys are strings of the step number (e.g. "5.5", "7")
    if "5.5" in step_outputs:
        # Check for prompt fixes
        p_match = re.search(r"PROMPT_FIXED:\s*(.*)", step_outputs["5.5"])
        if p_match:
            changed_files.append(p_match.group(1).strip())
    
    if "7" in step_outputs:
        changed_files.extend(_parse_changed_files(step_outputs["7"]))
    
    if "9" in step_outputs:
        changed_files.extend(_parse_e2e_files(step_outputs["9"]))
    
    # Deduplicate
    changed_files = list(set(changed_files))
    context["files_to_stage"] = ", ".join(changed_files)

    # If we are resuming at step 7 or later, we need to ensure the worktree exists/is active
    if start_step >= 7:
        if worktree_path and worktree_path.exists():
             if not quiet:
                console.print(f"[blue]Reusing existing worktree: {worktree_path}[/blue]")
             current_work_dir = worktree_path
             context["worktree_path"] = str(worktree_path)
        else:
            # Re-create worktree if missing
            wt_path, err = _setup_worktree(cwd, issue_number, quiet)
            if not wt_path:
                return False, f"Failed to restore worktree: {err}", total_cost, model_used, []
            worktree_path = wt_path
            current_work_dir = worktree_path
            state["worktree_path"] = str(worktree_path)
            context["worktree_path"] = str(worktree_path)

    for step_num, name, description in steps_config:
        # Skip if already done
        if step_num < start_step:
            continue

        # Special handling before Step 7: Create Worktree
        if step_num == 7:
            # Check current branch before creating worktree
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
            except subprocess.CalledProcessError:
                pass 

            wt_path, err = _setup_worktree(cwd, issue_number, quiet)
            if not wt_path:
                return False, f"Failed to create worktree: {err}", total_cost, model_used, []
            worktree_path = wt_path
            current_work_dir = worktree_path
            state["worktree_path"] = str(worktree_path)
            context["worktree_path"] = str(worktree_path)

        if not quiet:
            if step_num == 5.5:
                console.print(f"[bold][Step 5.5/11][/bold] {description}...")
            else:
                console.print(f"[bold][Step {step_num}/11][/bold] {description}...")

        # Load Prompt
        # Construct template name: agentic_bug_step{n}_{name}_LLM
        # For 5.5, we want agentic_bug_step5_5_prompt_classification_LLM
        if step_num == 5.5:
            template_name = f"agentic_bug_step5_5_{name}_LLM"
        else:
            template_name = f"agentic_bug_step{step_num}_{name}_LLM"
            
        prompt_template = load_prompt_template(template_name)
        if not prompt_template:
            return False, f"Missing prompt template: {template_name}", total_cost, model_used, []

        # Format Prompt
        try:
            formatted_prompt = prompt_template.format(**context)
        except KeyError as e:
            return False, f"Context missing key for step {step_num}: {e}", total_cost, model_used, []

        # Run Task
        timeout = BUG_STEP_TIMEOUTS.get(step_num, 340.0) + timeout_adder
        
        # Label for logging and context keys
        # 1 -> step1, 5.5 -> step5_5
        step_label_suffix = str(step_num).replace(".", "_")
        step_label = f"step{step_label_suffix}"
        
        step_success, step_output, step_cost, step_model = run_agentic_task(
            instruction=formatted_prompt,
            cwd=current_work_dir,
            verbose=verbose,
            quiet=quiet,
            timeout=timeout,
            label=step_label,
            max_retries=DEFAULT_MAX_RETRIES,
        )

        # Update tracking
        total_cost += step_cost
        model_used = step_model
        state["total_cost"] = total_cost
        state["model_used"] = model_used

        # Check hard stops (on failure OR success)
        stop_reason = _check_hard_stop(step_num, step_output)
        if stop_reason:
            if not quiet:
                console.print(f"⏹️  Investigation stopped at Step {step_num}: {stop_reason}")
            
            # Save state
            state["last_completed_step"] = step_num
            state["step_outputs"][str(step_num)] = step_output
            save_workflow_state(cwd, issue_number, "bug", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
            
            return False, f"Stopped at Step {step_num}: {stop_reason}", total_cost, model_used, changed_files

        if not step_success:
            # Soft failure
            console.print(f"[yellow]Warning: Step {step_num} reported failure but continuing...[/yellow]")

        # Step 5.5 Specific: Parse prompt fixes
        if step_num == 5.5:
            p_match = re.search(r"PROMPT_FIXED:\s*(.*)", step_output)
            if p_match:
                fixed_prompt = p_match.group(1).strip()
                changed_files.append(fixed_prompt)
                context["files_to_stage"] = ", ".join(changed_files)

        # Step 7 Specific: Parse created files
        if step_num == 7:
            extracted_files = _parse_changed_files(step_output)
            if not extracted_files:
                # Hard stop if no test file generated
                return False, "Stopped at Step 7: No test file generated", total_cost, model_used, changed_files
            
            changed_files.extend(extracted_files)
            changed_files = list(set(changed_files))
            context["files_to_stage"] = ", ".join(changed_files)

        # Step 9 Specific: Parse E2E files
        if step_num == 9:
            e2e_files = _parse_e2e_files(step_output)
            if e2e_files:
                changed_files.extend(e2e_files)
                changed_files = list(set(changed_files))
                context["files_to_stage"] = ", ".join(changed_files)

        # Update Context & State
        # Fix: Use step_label directly for context key to avoid double 'step' prefix
        # step_label is already 'step1' or 'step5_5'
        context[f"{step_label}_output"] = step_output
        
        if step_success:
            state["step_outputs"][str(step_num)] = step_output
            state["last_completed_step"] = step_num
        else:
            state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"
            # Don't update last_completed_step - keep it at previous value

        # Save State
        save_result = save_workflow_state(cwd, issue_number, "bug", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
        if save_result:
            github_comment_id = save_result
            state["github_comment_id"] = github_comment_id

        if not quiet:
            # Brief result summary
            lines = step_output.strip().split('\n')
            brief = lines[-1] if lines else "Done"
            if len(brief) > 80: brief = brief[:77] + "..."
            console.print(f"   → {escape(brief)}")

    # Final Summary
    pr_number = "Unknown"
    if "step10_output" in context:
        # Try to extract PR number/URL
        match = re.search(r"https://github.com/\S+/pull/(\d+)", context["step10_output"])
        if match:
            pr_number = f"#{match.group(1)}"
        elif "PR created" in context["step10_output"]:
            pr_number = "Created (URL not parsed)"

    if not quiet:
        console.print("\n✅ Investigation complete")
        console.print(f"   Total cost: ${total_cost:.4f}")
        console.print(f"   Files changed: {', '.join(changed_files)}")
        if worktree_path:
            console.print(f"   Worktree: {worktree_path}")
        if pr_number != "Unknown":
            console.print(f"   PR created: {pr_number}")

    # Clear state on success
    clear_workflow_state(cwd, issue_number, "bug", state_dir, repo_owner, repo_name, use_github_state)

    final_msg = f"Investigation complete. PR: {pr_number}"
    return True, final_msg, total_cost, model_used, changed_files