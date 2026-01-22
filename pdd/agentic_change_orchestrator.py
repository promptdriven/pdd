"""
Orchestrator for the 13-step agentic change workflow.
Runs each step as a separate agentic task, accumulates context, tracks progress/cost,
and supports resuming from saved state. Includes a review loop (steps 11-12).
"""

import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple, Any

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
from pdd.sync_order import (
    build_dependency_graph,
    topological_sort,
    get_affected_modules,
    generate_sync_order_script,
    extract_module_from_include,
)

# Initialize console for rich output
console = Console()

# Per-Step Timeouts (Workflow specific)
CHANGE_STEP_TIMEOUTS: Dict[int, float] = {
    1: 240.0,   # Duplicate Check
    2: 240.0,   # Docs Comparison
    3: 340.0,   # Research
    4: 340.0,   # Clarify
    5: 340.0,   # Docs Changes
    6: 340.0,   # Identify Dev Units
    7: 340.0,   # Architecture Review
    8: 600.0,   # Analyze Prompt Changes (Complex)
    9: 1000.0,  # Implement Changes (Most Complex)
    10: 340.0,  # Architecture Update
    11: 340.0,  # Identify Issues
    12: 600.0,  # Fix Issues (Complex)
    13: 340.0,  # Create PR
}

MAX_REVIEW_ITERATIONS = 5

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

    branch_name = f"change/issue-{issue_number}"
    worktree_rel_path = Path(".pdd") / "worktrees" / f"change-issue-{issue_number}"
    worktree_path = git_root / worktree_rel_path

    if worktree_path.exists():
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
            subprocess.run(
                ["git", "worktree", "remove", "--force", str(worktree_path)],
                cwd=git_root,
                capture_output=True
            )
        else:
            shutil.rmtree(worktree_path)

    try:
        subprocess.run(
            ["git", "branch", "-D", branch_name],
            cwd=git_root,
            capture_output=True
        )
    except Exception:
        pass

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
    created_match = re.search(r"FILES_CREATED:\s*(.*)", output)
    if created_match:
        files.extend([f.strip().strip("*").strip() for f in created_match.group(1).split(",") if f.strip()])
    
    modified_match = re.search(r"FILES_MODIFIED:\s*(.*)", output)
    if modified_match:
        files.extend([f.strip().strip("*").strip() for f in modified_match.group(1).split(",") if f.strip()])
    
    arch_match = re.search(r"ARCHITECTURE_FILES_MODIFIED:\s*(.*)", output)
    if arch_match:
        files.extend([f.strip().strip("*").strip() for f in arch_match.group(1).split(",") if f.strip()])
        
    return list(set(files))

def _check_hard_stop(step_num: int, output: str) -> Optional[str]:
    """Check output for hard stop conditions."""
    if step_num == 1 and "Duplicate of #" in output:
        return "Issue is a duplicate"
    if step_num == 2 and "Already Implemented" in output:
        return "Already implemented"
    if step_num == 4 and "Clarification Needed" in output:
        return "Clarification needed"
    if step_num == 6 and "No Dev Units Found" in output:
        return "No dev units found"
    if step_num == 7 and "Architectural Decision Needed" in output:
        return "Architectural decision needed"
    if step_num == 8 and "No Changes Required" in output:
        return "No changes needed"
    if step_num == 9:
        if "FAIL:" in output:
            return "Implementation failed"
    return None

def _get_state_dir(cwd: Path) -> Path:
    """Get the state directory relative to git root."""
    root = _get_git_root(cwd) or cwd
    return root / ".pdd" / "change-state"

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
    quiet: bool = False,
    timeout_adder: float = 0.0,
    use_github_state: bool = True
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Orchestrates the 13-step agentic change workflow.

    Returns:
        (success, final_message, total_cost, model_used, changed_files)
    """
    if not quiet:
        console.print(f"Implementing change for issue #{issue_number}: \"{issue_title}\"")

    state_dir = _get_state_dir(cwd)
    state, loaded_gh_id = load_workflow_state(cwd, issue_number, "change", state_dir, repo_owner, repo_name, use_github_state)

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
    
    context = {"issue_url": issue_url, "issue_content": issue_content, "repo_owner": repo_owner, "repo_name": repo_name, "issue_number": issue_number, "issue_author": issue_author, "issue_title": issue_title}
    for s_num, s_out in step_outputs.items():
        context[f"step{s_num}_output"] = s_out

    start_step = last_completed_step + 1
    if last_completed_step > 0 and not quiet:
        console.print(f"Resuming change workflow for issue #{issue_number}")
        console.print(f"   Steps 1-{last_completed_step} already complete (cached)")
        console.print(f"   Starting from Step {start_step}")

    steps_config = [
        (1, "duplicate", "Search for duplicate issues"),
        (2, "docs", "Check if already implemented"),
        (3, "research", "Research to clarify specifications"),
        (4, "clarify", "Verify requirements are clear"),
        (5, "docs_change", "Analyze documentation changes needed"),
        (6, "devunits", "Identify dev units involved"),
        (7, "architecture", "Review architecture"),
        (8, "analyze", "Analyze prompt changes"),
        (9, "implement", "Implement the prompt changes"),
        (10, "architecture_update", "Update architecture metadata"),
    ]

    current_work_dir = cwd
    changed_files = []

    if start_step >= 9:
        if worktree_path and worktree_path.exists():
             if not quiet: console.print(f"[blue]Reusing existing worktree: {worktree_path}[/blue]")
             current_work_dir = worktree_path
             context["worktree_path"] = str(worktree_path)
        else:
            wt_path, err = _setup_worktree(cwd, issue_number, quiet)
            if not wt_path: return False, f"Failed to restore worktree: {err}", total_cost, model_used, []
            worktree_path = wt_path
            current_work_dir = worktree_path
            state["worktree_path"] = str(worktree_path)
            context["worktree_path"] = str(worktree_path)

    for step_num, name, description in steps_config:
        if step_num < start_step: continue
        if step_num == 9:
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
                pass  # Ignore if git command fails, worktree setup will likely catch issues
            wt_path, err = _setup_worktree(cwd, issue_number, quiet)
            if not wt_path: return False, f"Failed to create worktree: {err}", total_cost, model_used, []
            worktree_path = wt_path
            current_work_dir = worktree_path
            state["worktree_path"] = str(worktree_path)
            context["worktree_path"] = str(worktree_path)

        if not quiet: console.print(f"[bold][Step {step_num}/13][/bold] {description}...")
        template_name = f"agentic_change_step{step_num}_{name}_LLM"
        prompt_template = load_prompt_template(template_name)
        if not prompt_template: return False, f"Missing prompt template: {template_name}", total_cost, model_used, []

        try: formatted_prompt = prompt_template.format(**context)
        except KeyError as e: return False, f"Context missing key for step {step_num}: {e}", total_cost, model_used, []

        timeout = CHANGE_STEP_TIMEOUTS.get(step_num, 340.0) + timeout_adder
        step_success, step_output, step_cost, step_model = run_agentic_task(instruction=formatted_prompt, cwd=current_work_dir, verbose=verbose, quiet=quiet, timeout=timeout, label=f"step{step_num}", max_retries=DEFAULT_MAX_RETRIES)

        total_cost += step_cost
        model_used = step_model
        state["total_cost"] = total_cost
        state["model_used"] = model_used

        if not step_success:
            # Check if it's a hard stop condition that caused "failure" or just agent error
            stop_reason = _check_hard_stop(step_num, step_output)
            if stop_reason:
                if not quiet:
                    console.print(f"[yellow]Investigation stopped at Step {step_num}: {stop_reason}[/yellow]")
                # Save state so we don't re-run previous steps
                state["last_completed_step"] = step_num
                state["step_outputs"][str(step_num)] = step_output
                save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
                return False, f"Stopped at step {step_num}: {stop_reason}", total_cost, model_used, []
            # Soft failure - warn but continue
            console.print(f"[yellow]Warning: Step {step_num} reported failure but continuing...[/yellow]")

        # Check hard stops on success too
        stop_reason = _check_hard_stop(step_num, step_output)
        if stop_reason:
            if not quiet: console.print(f"[yellow]Investigation stopped at Step {step_num}: {stop_reason}[/yellow]")
            state["last_completed_step"] = step_num
            state["step_outputs"][str(step_num)] = step_output
            save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
            return False, f"Stopped at step {step_num}: {stop_reason}", total_cost, model_used, []

        if step_num == 9:
            extracted_files = _parse_changed_files(step_output)
            changed_files = extracted_files
            if not changed_files: return False, "Stopped at step 9: Implementation produced no file changes", total_cost, model_used, []
            context["files_to_stage"] = ", ".join(changed_files)
            created_match = re.search(r"FILES_CREATED:\s*(.*)", step_output)
            modified_match = re.search(r"FILES_MODIFIED:\s*(.*)", step_output)
            context["files_created"] = created_match.group(1).strip() if created_match else ""
            context["files_modified"] = modified_match.group(1).strip() if modified_match else ""

        if step_num == 10:
            arch_files = _parse_changed_files(step_output)
            new_files = [f for f in arch_files if f not in changed_files]
            changed_files.extend(new_files)
            context["files_to_stage"] = ", ".join(changed_files)

        context[f"step{step_num}_output"] = step_output
        if step_success:
            state["step_outputs"][str(step_num)] = step_output
            state["last_completed_step"] = step_num
        else:
            state["step_outputs"][str(step_num)] = f"FAILED: {step_output}"

        save_result = save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
        if save_result: github_comment_id = save_result; state["github_comment_id"] = github_comment_id

        if not quiet:
            # Brief result summary
            lines = step_output.strip().split('\n')
            brief = lines[-1] if lines else "Done"
            if len(brief) > 80: brief = brief[:77] + "..."
            console.print(f"   -> {escape(brief)}")

    if "files_to_stage" not in context:
        s9_out = context.get("step9_output", "")
        s10_out = context.get("step10_output", "")
        c_files = _parse_changed_files(s9_out)
        c_files.extend(_parse_changed_files(s10_out))
        changed_files = list(set(c_files))
        context["files_to_stage"] = ", ".join(changed_files)

    review_iteration = state.get("review_iteration", 0)
    previous_fixes = state.get("previous_fixes", "")
    
    if last_completed_step < 13:
        while review_iteration < MAX_REVIEW_ITERATIONS:
            review_iteration += 1
            state["review_iteration"] = review_iteration
            if not quiet: console.print(f"[bold][Step 11/13][/bold] Identifying issues (iteration {review_iteration}/{MAX_REVIEW_ITERATIONS})...")
            s11_template = load_prompt_template("agentic_change_step11_identify_issues_LLM")
            context["review_iteration"] = review_iteration
            context["previous_fixes"] = previous_fixes
            s11_prompt = s11_template.format(**context)
            timeout11 = CHANGE_STEP_TIMEOUTS.get(11, 340.0) + timeout_adder
            s11_success, s11_output, s11_cost, s11_model = run_agentic_task(instruction=s11_prompt, cwd=current_work_dir, verbose=verbose, quiet=quiet, timeout=timeout11, label=f"step11_iter{review_iteration}", max_retries=DEFAULT_MAX_RETRIES)
            total_cost += s11_cost; model_used = s11_model; state["total_cost"] = total_cost
            if "No Issues Found" in s11_output:
                if not quiet: console.print("   -> No issues found. Proceeding to PR.")
                context["step11_output"] = s11_output; break
            if not quiet: console.print("   -> Issues found. Proceeding to fix.")
            if not quiet: console.print(f"[bold][Step 12/13][/bold] Fixing issues (iteration {review_iteration}/{MAX_REVIEW_ITERATIONS})...")
            s12_template = load_prompt_template("agentic_change_step12_fix_issues_LLM")
            context["step11_output"] = s11_output
            s12_prompt = s12_template.format(**context)
            timeout12 = CHANGE_STEP_TIMEOUTS.get(12, 600.0) + timeout_adder
            s12_success, s12_output, s12_cost, s12_model = run_agentic_task(instruction=s12_prompt, cwd=current_work_dir, verbose=verbose, quiet=quiet, timeout=timeout12, label=f"step12_iter{review_iteration}", max_retries=DEFAULT_MAX_RETRIES)
            total_cost += s12_cost; model_used = s12_model; state["total_cost"] = total_cost
            previous_fixes += f"\n\nIteration {review_iteration}:\n{s12_output}"; state["previous_fixes"] = previous_fixes
            save_result = save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
            if save_result: github_comment_id = save_result; state["github_comment_id"] = github_comment_id
        if review_iteration >= MAX_REVIEW_ITERATIONS: console.print("[yellow]Warning: Maximum review iterations reached. Proceeding to PR creation.[/yellow]")

    sync_order_script = ""; sync_order_list = "No modules to sync"
    files_to_stage_str = context.get("files_to_stage", "")
    file_list = [f.strip() for f in files_to_stage_str.split(",") if f.strip()]
    modified_modules: Set[str] = set()
    for file_path in file_list:
        if file_path.startswith("prompts/") and file_path.endswith(".prompt"):
            module = extract_module_from_include(file_path)
            if module: modified_modules.add(module)
    if worktree_path:
        prompts_dir = worktree_path / "prompts"
        if prompts_dir.exists() and modified_modules:
            try:
                graph = build_dependency_graph(prompts_dir)
                sorted_modules, cycles = topological_sort(graph)
                if cycles and not quiet: console.print(f"[yellow]Warning: Circular dependencies detected: {cycles}[/yellow]")
                affected = get_affected_modules(sorted_modules, modified_modules, graph)
                if affected:
                    script_path = worktree_path / "sync_order.sh"
                    sync_order_list = generate_sync_order_script(affected, script_path, worktree_path)
                    sync_order_script = str(script_path)
                    if not quiet:
                        console.print(f"[dim]Generated sync order script: {script_path}[/dim]")
            except Exception as e:
                if not quiet: console.print(f"[yellow]Warning: Could not generate sync order: {e}[/yellow]")
    context["sync_order_script"] = sync_order_script; context["sync_order_list"] = sync_order_list

    if last_completed_step < 13:
        if not quiet: console.print("[bold][Step 13/13][/bold] Create PR and link to issue...")
        s13_template = load_prompt_template("agentic_change_step13_create_pr_LLM")
        s13_prompt = s13_template.format(**context)
        timeout13 = CHANGE_STEP_TIMEOUTS.get(13, 340.0) + timeout_adder
        s13_success, s13_output, s13_cost, s13_model = run_agentic_task(instruction=s13_prompt, cwd=current_work_dir, verbose=verbose, quiet=quiet, timeout=timeout13, label="step13", max_retries=DEFAULT_MAX_RETRIES)
        total_cost += s13_cost; model_used = s13_model; state["total_cost"] = total_cost
        if not s13_success:
             save_workflow_state(cwd, issue_number, "change", state, state_dir, repo_owner, repo_name, use_github_state, github_comment_id)
             return False, "PR Creation failed", total_cost, model_used, changed_files
        pr_url = "Unknown"; url_match = re.search(r"https://github.com/\S+/pull/\d+", s13_output)
        if url_match: pr_url = url_match.group(0)
        if not quiet:
            console.print("\n[green]Change workflow complete[/green]")
            console.print(f"   Total cost: ${total_cost:.4f}")
            console.print(f"   Files changed: {', '.join(changed_files)}")
            console.print(f"   PR: {pr_url}")
            console.print(f"   Review iterations: {review_iteration}")
            console.print("\nNext steps:")
            console.print("   1. Review and merge the PR")
            console.print("   2. Run `./sync_order.sh` after merge (or see PR for manual commands)")
        clear_workflow_state(cwd, issue_number, "change", state_dir, repo_owner, repo_name, use_github_state)
        return True, f"PR Created: {pr_url}", total_cost, model_used, changed_files
    return True, "Workflow already completed", total_cost, model_used, changed_files