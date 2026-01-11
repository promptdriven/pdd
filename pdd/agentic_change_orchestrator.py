import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Tuple, List, Optional, Dict, Any, Union

from rich.console import Console
from rich.panel import Panel

# Internal imports
try:
    from .agentic_common import run_agentic_task, CHANGE_STEP_TIMEOUTS
    from .load_prompt_template import load_prompt_template
except ImportError:
    # Fallback for development/testing if relative imports fail
    from pdd.agentic_common import run_agentic_task, CHANGE_STEP_TIMEOUTS
    from pdd.load_prompt_template import load_prompt_template

console = Console()

# -----------------------------------------------------------------------------
# Constants & Configuration
# -----------------------------------------------------------------------------

STATE_DIR = Path(".pdd/change-state")
WORKTREE_DIR = Path(".pdd/worktrees")

STEPS_METADATA = {
    1: ("agentic_change_step1_duplicate_LLM", "Searching for duplicate issues"),
    2: ("agentic_change_step2_docs_LLM", "Checking if already implemented"),
    3: ("agentic_change_step3_research_LLM", "Researching specifications"),
    4: ("agentic_change_step4_clarify_LLM", "Verifying requirements"),
    5: ("agentic_change_step5_docs_change_LLM", "Analyzing documentation changes"),
    6: ("agentic_change_step6_devunits_LLM", "Identifying dev units"),
    7: ("agentic_change_step7_architecture_LLM", "Reviewing architecture"),
    8: ("agentic_change_step8_analyze_LLM", "Analyzing prompt changes"),
    9: ("agentic_change_step9_implement_LLM", "Implementing changes"),
    10: ("agentic_change_step10_identify_issues_LLM", "Identifying issues"),
    11: ("agentic_change_step11_fix_issues_LLM", "Fixing issues"),
    12: ("agentic_change_step12_create_pr_LLM", "Creating Pull Request"),
}

# -----------------------------------------------------------------------------
# State Management Helpers
# -----------------------------------------------------------------------------

def _json_serializer(obj):
    """JSON serializer for objects not serializable by default json code"""
    if isinstance(obj, Path):
        return str(obj)
    raise TypeError(f"Type {type(obj)} not serializable")

def _get_state_file_path(cwd: Path, issue_number: int) -> Path:
    return cwd / STATE_DIR / f"issue-{issue_number}.json"

def _load_state(cwd: Path, issue_number: int) -> Optional[Dict[str, Any]]:
    path = _get_state_file_path(cwd, issue_number)
    if path.exists():
        try:
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception as e:
            console.print(f"[yellow]Warning: Failed to load state file: {e}[/yellow]")
    return None

def _save_state(cwd: Path, issue_number: int, state: Dict[str, Any]) -> None:
    path = _get_state_file_path(cwd, issue_number)
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            json.dump(state, f, indent=2, default=_json_serializer)
    except Exception as e:
        console.print(f"[yellow]Warning: Failed to save state file: {e}[/yellow]")

def _clear_state(cwd: Path, issue_number: int) -> None:
    path = _get_state_file_path(cwd, issue_number)
    if path.exists():
        try:
            os.remove(path)
        except Exception as e:
            console.print(f"[yellow]Warning: Failed to clear state file: {e}[/yellow]")

# -----------------------------------------------------------------------------
# Git Worktree Helpers
# -----------------------------------------------------------------------------

def _get_git_root(cwd: Path) -> Optional[Path]:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=cwd, capture_output=True, text=True, check=True
        )
        return Path(result.stdout.strip())
    except (subprocess.CalledProcessError, FileNotFoundError):
        return None

def _branch_exists(cwd: Path, branch: str) -> bool:
    try:
        subprocess.run(
            ["git", "show-ref", "--verify", f"refs/heads/{branch}"],
            cwd=cwd, capture_output=True, check=True
        )
        return True
    except subprocess.CalledProcessError:
        return False

def _setup_worktree(cwd: Path, issue_number: int, quiet: bool, resume_existing: bool = False) -> Tuple[Optional[Path], Optional[str]]:
    """
    Sets up an isolated git worktree for the issue.
    Returns (worktree_path, error_message).
    
    Args:
        cwd: Current working directory
        issue_number: The issue number
        quiet: Suppress output
        resume_existing: If True, attempts to reuse existing branch if worktree is missing.
    """
    git_root = _get_git_root(cwd)
    if not git_root:
        return None, "Not a git repository"

    branch_name = f"change/issue-{issue_number}"
    # Worktree path relative to git root
    worktree_rel_path = WORKTREE_DIR / f"change-issue-{issue_number}"
    worktree_abs_path = git_root / worktree_rel_path

    # 1. Clean up existing worktree at path if it exists
    if worktree_abs_path.exists():
        # Try to remove via git first
        subprocess.run(
            ["git", "worktree", "remove", "--force", str(worktree_abs_path)],
            cwd=git_root, capture_output=True, check=False
        )
        # If directory still exists (e.g. not a valid worktree or git failed), force remove
        if worktree_abs_path.exists():
            try:
                shutil.rmtree(worktree_abs_path)
            except Exception as e:
                return None, f"Failed to clean up existing directory {worktree_abs_path}: {e}"

    # 2. Handle existing branch
    branch_exists = _branch_exists(git_root, branch_name)
    
    if branch_exists:
        if resume_existing:
            # If we are resuming and the branch exists, we want to checkout that branch
            # into the new worktree, NOT delete it.
            if not quiet:
                console.print(f"[blue]Resuming with existing branch: {branch_name}[/blue]")
        else:
            # Standard behavior: delete existing branch to start fresh
            try:
                subprocess.run(
                    ["git", "branch", "-D", branch_name],
                    cwd=git_root, capture_output=True, check=True
                )
                branch_exists = False # It's gone now
            except subprocess.CalledProcessError as e:
                return None, f"Failed to delete existing branch {branch_name}: {e.stderr}"

    # 3. Create new worktree
    try:
        worktree_abs_path.parent.mkdir(parents=True, exist_ok=True)
        
        cmd = ["git", "worktree", "add"]
        if branch_exists and resume_existing:
            # Checkout existing branch
            cmd.extend([str(worktree_abs_path), branch_name])
        else:
            # Create new branch from HEAD
            cmd.extend(["-b", branch_name, str(worktree_abs_path), "HEAD"])
            
        subprocess.run(
            cmd,
            cwd=git_root, capture_output=True, text=True, check=True
        )
    except subprocess.CalledProcessError as e:
        return None, f"Failed to create worktree: {e.stderr}"

    return worktree_abs_path, None

# -----------------------------------------------------------------------------
# Orchestrator Logic
# -----------------------------------------------------------------------------

def run_agentic_change_orchestrator(
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
    quiet: bool = False
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Orchestrates the 12-step agentic change workflow.
    """
    
    # Initial Setup
    if not quiet:
        console.print(Panel(f"Implementing change for issue #{issue_number}: \"{issue_title}\"", style="bold blue"))

    # Load State
    state = _load_state(cwd, issue_number)
    
    # Initialize variables from state or defaults
    if state:
        if not quiet:
            console.print(f"[yellow]Resuming from step {state.get('last_completed_step', 0) + 1} (steps 1-{state.get('last_completed_step', 0)} cached)[/yellow]")
        
        total_cost = state.get("total_cost", 0.0)
        model_used = state.get("model_used", "unknown")
        step_outputs = state.get("step_outputs", {})
        last_completed_step = state.get("last_completed_step", 0)
        worktree_path_str = state.get("worktree_path")
        worktree_path = Path(worktree_path_str) if worktree_path_str else None
        review_iteration = state.get("review_iteration", 0)
        previous_fixes = state.get("previous_fixes", "")
        files_to_stage_str = state.get("files_to_stage", "")

        # Verify worktree existence on resume
        if worktree_path and not worktree_path.exists():
            if not quiet:
                console.print(f"[yellow]Worktree path {worktree_path} not found. Attempting to recreate...[/yellow]")
            # Pass resume_existing=True to avoid deleting the branch if it contains our work
            wt_path, err = _setup_worktree(cwd, issue_number, quiet, resume_existing=True)
            if not wt_path:
                return False, f"Failed to recreate worktree on resume: {err}", total_cost, model_used, []
            worktree_path = wt_path
            # Update state with new worktree path if it changed (though it should be same path)
            if str(worktree_path) != worktree_path_str:
                _save_state(cwd, issue_number, {
                    **state,
                    "worktree_path": str(worktree_path)
                })

    else:
        total_cost = 0.0
        model_used = "unknown"
        step_outputs = {}
        last_completed_step = 0
        worktree_path = None
        review_iteration = 0
        previous_fixes = ""
        files_to_stage_str = ""

    # Context dictionary to pass to templates
    context = {
        "issue_url": issue_url,
        "issue_content": issue_content,
        "repo_owner": repo_owner,
        "repo_name": repo_name,
        "issue_number": str(issue_number),
        "issue_author": issue_author,
        "issue_title": issue_title,
        "files_to_stage": files_to_stage_str,
        "worktree_path": str(worktree_path) if worktree_path else "",
        "review_iteration": str(review_iteration),
        "previous_fixes": previous_fixes
    }
    
    # Populate context with loaded step outputs
    for k, v in step_outputs.items():
        context[f"step{k}_output"] = v

    # Determine current working directory for agents
    # If we resumed after step 9, we should be in the worktree
    current_agent_cwd = worktree_path if (worktree_path and last_completed_step >= 9) else cwd

    # -------------------------------------------------------------------------
    # Main Execution Loop
    # -------------------------------------------------------------------------
    
    # We iterate through steps 1 to 12. 
    # Steps 10 and 11 are handled specially as a loop block when we hit step 10.
    
    step_sequence = list(range(1, 13))
    start_index = last_completed_step

    for i in range(start_index, 12):
        step_num = step_sequence[i]
        template_name, description = STEPS_METADATA[step_num]
        
        # ---------------------------------------------------------------------
        # Special Handling: Step 9 (Worktree Setup)
        # ---------------------------------------------------------------------
        if step_num == 9:
            # Only setup worktree if we haven't already (or if we lost it)
            if not worktree_path or not worktree_path.exists():
                if not quiet:
                    console.print(f"[Step {step_num}/12] Setting up isolated worktree...")
                
                # Standard setup (resume_existing=False) because we are just reaching step 9
                wt_path, err = _setup_worktree(cwd, issue_number, quiet, resume_existing=False)
                if not wt_path:
                    return False, f"Failed to create worktree: {err}", total_cost, model_used, []
                
                worktree_path = wt_path
                current_agent_cwd = worktree_path
                context["worktree_path"] = str(worktree_path)
                
                # Update state with worktree path immediately
                _save_state(cwd, issue_number, {
                    "issue_url": issue_url,
                    "issue_number": issue_number,
                    "last_completed_step": last_completed_step,
                    "step_outputs": step_outputs,
                    "total_cost": total_cost,
                    "model_used": model_used,
                    "worktree_path": str(worktree_path),
                    "files_to_stage": files_to_stage_str
                })
                
                if not quiet:
                    console.print(f"[blue]Working in worktree: {worktree_path}[/blue]")

        # ---------------------------------------------------------------------
        # Special Handling: Steps 10 & 11 (Review Loop)
        # ---------------------------------------------------------------------
        if step_num == 10:
            # Enter the review loop
            MAX_REVIEW_ITERATIONS = 5
            
            # If we are resuming at step 10, review_iteration might be > 0 from state
            # If we are resuming at step 11, we need to jump into the loop but skip step 10 logic for this iteration
            
            while review_iteration < MAX_REVIEW_ITERATIONS:
                # If we are just starting the loop or finished a full iteration (step 11 done), increment
                # If we are resuming at step 11 (last_completed_step=10), we are still in the same iteration
                if last_completed_step != 10:
                    review_iteration += 1
                
                context["review_iteration"] = str(review_iteration)
                context["previous_fixes"] = previous_fixes

                # --- Run Step 10: Identify Issues ---
                # Only run step 10 if we haven't completed it for this iteration yet
                if last_completed_step != 10:
                    if not quiet:
                        console.print(f"[Step 10/12] Identifying issues (iteration {review_iteration}/{MAX_REVIEW_ITERATIONS})...")
                    
                    s10_template = load_prompt_template(STEPS_METADATA[10][0])
                    if not s10_template:
                        return False, f"Missing template for step 10", total_cost, model_used, []
                    
                    s10_prompt = s10_template.format(**context)
                    
                    success, s10_output, cost, model = run_agentic_task(
                        s10_prompt, 
                        cwd=current_agent_cwd, 
                        verbose=verbose, 
                        quiet=quiet,
                        label="step10",
                        timeout=CHANGE_STEP_TIMEOUTS.get(10, 300)
                    )
                    
                    total_cost += cost
                    model_used = model or model_used
                    step_outputs["10"] = s10_output
                    context["step10_output"] = s10_output
                    
                    # Save state inside loop
                    _save_state(cwd, issue_number, {
                        "issue_url": issue_url,
                        "issue_number": issue_number,
                        "last_completed_step": 10, # Mark 10 as done for this iteration
                        "step_outputs": step_outputs,
                        "total_cost": total_cost,
                        "model_used": model_used,
                        "worktree_path": str(worktree_path),
                        "review_iteration": review_iteration,
                        "previous_fixes": previous_fixes,
                        "files_to_stage": files_to_stage_str
                    })

                    if "No Issues Found" in s10_output:
                        if not quiet:
                            console.print("  -> No issues found. Proceeding.")
                        break # Exit review loop, proceed to Step 12
                    
                    if not quiet:
                        console.print("  -> Issues found. Proceeding to fix.")
                else:
                    # If we skipped step 10 because last_completed_step was 10, we need to ensure context has output
                    # The output should be in step_outputs from state load
                    context["step10_output"] = step_outputs.get("10", "")
                    # Reset last_completed_step so next iteration runs step 10 normally
                    last_completed_step = 0 

                # --- Run Step 11: Fix Issues ---
                if not quiet:
                    console.print(f"[Step 11/12] Fixing issues (iteration {review_iteration}/{MAX_REVIEW_ITERATIONS})...")
                
                s11_template = load_prompt_template(STEPS_METADATA[11][0])
                if not s11_template:
                    return False, f"Missing template for step 11", total_cost, model_used, []
                
                s11_prompt = s11_template.format(**context)
                
                success, s11_output, cost, model = run_agentic_task(
                    s11_prompt, 
                    cwd=current_agent_cwd, 
                    verbose=verbose, 
                    quiet=quiet,
                    label="step11",
                    timeout=CHANGE_STEP_TIMEOUTS.get(11, 300)
                )
                
                total_cost += cost
                model_used = model or model_used
                step_outputs["11"] = s11_output
                
                # Accumulate fixes
                previous_fixes += f"\n\nIteration {review_iteration}:\n{s11_output}"
                context["previous_fixes"] = previous_fixes
                
                # Save state after fix
                _save_state(cwd, issue_number, {
                    "issue_url": issue_url,
                    "issue_number": issue_number,
                    "last_completed_step": 11,
                    "step_outputs": step_outputs,
                    "total_cost": total_cost,
                    "model_used": model_used,
                    "worktree_path": str(worktree_path),
                    "review_iteration": review_iteration,
                    "previous_fixes": previous_fixes,
                    "files_to_stage": files_to_stage_str
                })
                
                if not quiet:
                    console.print("  -> Fixes applied.")

            if review_iteration >= MAX_REVIEW_ITERATIONS:
                console.print("[yellow]Warning: Maximum review iterations reached. Proceeding to PR creation.[/yellow]")
            
            # Skip the standard loop iteration for step 11, as we handled it inside step 10 block
            continue 
        
        if step_num == 11:
            # Handled inside step 10 block
            continue

        # ---------------------------------------------------------------------
        # Standard Step Execution (1-9, 12)
        # ---------------------------------------------------------------------
        
        if not quiet:
            console.print(f"[Step {step_num}/12] {description}...")

        # Load Template
        template = load_prompt_template(template_name)
        if not template:
            return False, f"Failed to load template: {template_name}", total_cost, model_used, []

        # Format Prompt
        try:
            prompt = template.format(**context)
        except KeyError as e:
            return False, f"Missing context key for step {step_num}: {e}", total_cost, model_used, []

        # Run Agent
        success, output, cost, model = run_agentic_task(
            prompt,
            cwd=current_agent_cwd,
            verbose=verbose,
            quiet=quiet,
            label=f"step{step_num}",
            timeout=CHANGE_STEP_TIMEOUTS.get(step_num, 300)
        )

        # Update Metrics
        total_cost += cost
        if model:
            model_used = model
        
        # Store Output
        step_outputs[str(step_num)] = output
        context[f"step{step_num}_output"] = output

        # ---------------------------------------------------------------------
        # Post-Step Processing & Stop Conditions
        # ---------------------------------------------------------------------

        # Step 9: Parse Changed Files
        if step_num == 9:
            # Look for FILES_CREATED: a, b or FILES_MODIFIED: a, b
            files_found = []
            # Improved regex: case insensitive, handles spaces better
            for match in re.finditer(r"FILES_(?:CREATED|MODIFIED):\s*(.*)", output, re.IGNORECASE):
                file_list = match.group(1).strip()
                if file_list and file_list.lower() != "none":
                    files_found.extend([f.strip() for f in file_list.split(",")])
            
            # Deduplicate and store
            unique_files = list(set(files_found))
            files_to_stage_str = ", ".join(unique_files)
            context["files_to_stage"] = files_to_stage_str
            
            # Fix: Stop if no files found OR "FAIL:" in output
            if not unique_files or "FAIL:" in output:
                 return False, f"Stopped at step 9: Implementation failed (no files changed or explicit fail)", total_cost, model_used, []

        # Hard Stop Conditions
        stop_reason = None
        if step_num == 1 and "Duplicate of #" in output:
            stop_reason = "Issue is a duplicate"
        elif step_num == 2 and "Already Implemented" in output:
            stop_reason = "Feature already implemented"
        elif step_num == 4 and "Clarification Needed" in output:
            stop_reason = "Clarification needed from user"
        elif step_num == 6 and "No Dev Units Found" in output:
            stop_reason = "No relevant dev units found"
        elif step_num == 7 and "Architectural Decision Needed" in output:
            stop_reason = "Architectural decision needed"
        elif step_num == 8 and "No Changes Required" in output:
            stop_reason = "Analysis determined no changes required"

        if stop_reason:
            if not quiet:
                console.print(f"[bold red]Investigation stopped at Step {step_num}: {stop_reason}[/bold red]")
            
            # Save state so we can resume later if needed (e.g. after clarification)
            _save_state(cwd, issue_number, {
                "issue_url": issue_url,
                "issue_number": issue_number,
                "last_completed_step": step_num,
                "step_outputs": step_outputs,
                "total_cost": total_cost,
                "model_used": model_used,
                "worktree_path": str(worktree_path) if worktree_path else None,
                "files_to_stage": files_to_stage_str
            })
            
            return False, f"Stopped at step {step_num}: {stop_reason}", total_cost, model_used, []

        # Save State after successful step
        _save_state(cwd, issue_number, {
            "issue_url": issue_url,
            "issue_number": issue_number,
            "last_completed_step": step_num,
            "step_outputs": step_outputs,
            "total_cost": total_cost,
            "model_used": model_used,
            "worktree_path": str(worktree_path) if worktree_path else None,
            "files_to_stage": files_to_stage_str
        })

        # Console Feedback
        if not quiet:
            brief = "Completed"
            if step_num == 1: brief = "No duplicates found"
            elif step_num == 6: brief = "Dev units identified"
            elif step_num == 9: brief = f"Changes applied ({len(files_to_stage_str.split(',')) if files_to_stage_str else 0} files)"
            elif step_num == 12: brief = "PR Created"
            console.print(f"  -> {brief}")

    # -------------------------------------------------------------------------
    # Finalization
    # -------------------------------------------------------------------------
    
    # Extract PR URL from Step 12 output if available
    pr_url = "Unknown"
    s12_out = step_outputs.get("12", "")
    pr_match = re.search(r"(https://github\.com/[^\s]+/pull/\d+)", s12_out)
    if pr_match:
        pr_url = pr_match.group(1)

    changed_files_list = [f.strip() for f in files_to_stage_str.split(",")] if files_to_stage_str else []

    if not quiet:
        summary = f"""
Change workflow complete
   Total cost: ${total_cost:.4f}
   Files changed: {files_to_stage_str}
   PR: {pr_url}
   Review iterations: {review_iteration}

Next steps:
   1. Review and merge the PR
   2. Run `pdd sync <module>` after merge
"""
        console.print(Panel(summary, title="Summary", style="green"))

    # Clear state on success
    _clear_state(cwd, issue_number)

    return True, f"Workflow complete. PR: {pr_url}", total_cost, model_used, changed_files_list