from __future__ import annotations

import shutil
import subprocess
from pathlib import Path
from typing import List, Tuple, Optional, Dict, Any

from rich.console import Console

from .agentic_common import run_agentic_task
from .load_prompt_template import load_prompt_template

# Initialize console
console = Console()

def _get_git_root(cwd: Path) -> Optional[Path]:
    """Get the root directory of the git repository."""
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

def _worktree_exists(cwd: Path, worktree_path: Path) -> bool:
    """Check if a path is a registered git worktree."""
    try:
        result = subprocess.run(
            ["git", "worktree", "list", "--porcelain"],
            cwd=cwd,
            capture_output=True,
            text=True,
            check=True
        )
        # The porcelain output lists 'worktree /path/to/worktree'
        # We check if our specific path appears in the output
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
            check=True
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
            check=True
        )
        return True, ""
    except subprocess.CalledProcessError as e:
        return False, e.stderr.decode('utf-8')

def _delete_branch(cwd: Path, branch: str) -> Tuple[bool, str]:
    """Force delete a git branch."""
    try:
        subprocess.run(
            ["git", "branch", "-D", branch],
            cwd=cwd,
            capture_output=True,
            check=True
        )
        return True, ""
    except subprocess.CalledProcessError as e:
        return False, e.stderr.decode('utf-8')

def _setup_worktree(cwd: Path, issue_number: int, quiet: bool) -> Tuple[Optional[Path], Optional[str]]:
    """
    Sets up an isolated git worktree for the issue fix.
    Returns (worktree_path, error_message).
    """
    git_root = _get_git_root(cwd)
    if not git_root:
        return None, "Current directory is not a git repository."

    worktree_rel_path = Path(".pdd") / "worktrees" / f"fix-issue-{issue_number}"
    worktree_path = git_root / worktree_rel_path
    branch_name = f"fix/issue-{issue_number}"

    # 1. Clean up existing worktree at path
    if worktree_path.exists():
        if _worktree_exists(git_root, worktree_path):
            if not quiet:
                console.print(f"[yellow]Removing existing worktree at {worktree_path}[/yellow]")
            success, err = _remove_worktree(git_root, worktree_path)
            if not success:
                return None, f"Failed to remove existing worktree: {err}"
        else:
            # It's just a directory, not a registered worktree
            if not quiet:
                console.print(f"[yellow]Removing stale directory at {worktree_path}[/yellow]")
            shutil.rmtree(worktree_path)

    # 2. Clean up existing branch
    if _branch_exists(git_root, branch_name):
        if not quiet:
            console.print(f"[yellow]Removing existing branch {branch_name}[/yellow]")
        success, err = _delete_branch(git_root, branch_name)
        if not success:
            return None, f"Failed to delete existing branch: {err}"

    # 3. Create new worktree and branch
    try:
        worktree_path.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["git", "worktree", "add", "-b", branch_name, str(worktree_path), "HEAD"],
            cwd=git_root,
            capture_output=True,
            check=True
        )
        return worktree_path, None
    except subprocess.CalledProcessError as e:
        return None, f"Failed to create worktree: {e.stderr.decode('utf-8')}"


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
    quiet: bool = False
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Orchestrates the 9-step agentic bug investigation workflow.
    
    Returns:
        (success, final_message, total_cost, model_used, changed_files)
    """
    
    if not quiet:
        console.print(f"🔍 Investigating issue #{issue_number}: \"{issue_title}\"")

    # Context accumulation
    context: Dict[str, Any] = {
        "issue_url": issue_url,
        "issue_content": issue_content,
        "repo_owner": repo_owner,
        "repo_name": repo_name,
        "issue_number": issue_number,
        "issue_author": issue_author,
        "issue_title": issue_title,
    }

    total_cost = 0.0
    last_model_used = "unknown"
    changed_files: List[str] = []
    current_cwd = cwd
    worktree_path: Optional[Path] = None

    # Step Definitions
    steps = [
        (1, "duplicate", "Searching for duplicate issues"),
        (2, "docs", "Checking documentation for user error"),
        (3, "triage", "Assessing information completeness"),
        (4, "reproduce", "Attempting to reproduce the bug"),
        (5, "root_cause", "Analyzing root cause"),
        (6, "test_plan", "Designing test strategy"),
        (7, "generate", "Generating failing unit test"),
        (8, "verify", "Verifying test catches the bug"),
        (9, "pr", "Creating draft PR"),
    ]

    for step_num, name, description in steps:
        
        # --- Pre-Step Logic: Worktree Creation ---
        if step_num == 7:
            wt_path, err = _setup_worktree(cwd, issue_number, quiet)
            if not wt_path:
                return False, f"Failed to create worktree: {err}", total_cost, last_model_used, changed_files
            
            worktree_path = wt_path
            current_cwd = worktree_path
            context["worktree_path"] = str(worktree_path)
            
            if not quiet:
                console.print(f"[blue]Working in worktree: {worktree_path}[/blue]")

        # --- Step Execution ---
        if not quiet:
            console.print(f"[bold][Step {step_num}/9][/bold] {description}...")

        template_name = f"agentic_bug_step{step_num}_{name}_LLM"
        prompt_template = load_prompt_template(template_name)
        
        if not prompt_template:
            return False, f"Missing prompt template: {template_name}", total_cost, last_model_used, changed_files

        # Format prompt with accumulated context
        try:
            formatted_prompt = prompt_template.format(**context)
        except KeyError as e:
            return False, f"Prompt formatting error in step {step_num}: missing {e}", total_cost, last_model_used, changed_files

        # Run the task
        success, output, cost, model = run_agentic_task(
            instruction=formatted_prompt,
            cwd=current_cwd,
            verbose=verbose,
            quiet=quiet,
            label=f"step{step_num}"
        )

        # Update tracking
        total_cost += cost
        last_model_used = model
        context[f"step{step_num}_output"] = output

        # --- Post-Step Logic: Hard Stops & Parsing ---

        # Step 1: Duplicate Check
        if step_num == 1 and "Duplicate of #" in output:
            msg = f"Stopped at Step 1: Issue is a duplicate. {output.strip()}"
            if not quiet:
                console.print(f"⏹️  {msg}")
            return False, msg, total_cost, last_model_used, changed_files

        # Step 2: User Error / Feature Request
        if step_num == 2:
            if "Feature Request (Not a Bug)" in output:
                msg = "Stopped at Step 2: Identified as Feature Request."
                if not quiet: console.print(f"⏹️  {msg}")
                return False, msg, total_cost, last_model_used, changed_files
            if "User Error (Not a Bug)" in output:
                msg = "Stopped at Step 2: Identified as User Error."
                if not quiet: console.print(f"⏹️  {msg}")
                return False, msg, total_cost, last_model_used, changed_files

        # Step 3: Needs Info
        if step_num == 3 and "Needs More Info" in output:
            msg = "Stopped at Step 3: Insufficient information provided."
            if not quiet: console.print(f"⏹️  {msg}")
            return False, msg, total_cost, last_model_used, changed_files

        # Step 7: File Extraction
        if step_num == 7:
            # Parse output for FILES_CREATED or FILES_MODIFIED
            extracted_files = []
            for line in output.splitlines():
                if line.startswith("FILES_CREATED:") or line.startswith("FILES_MODIFIED:"):
                    file_list = line.split(":", 1)[1].strip()
                    extracted_files.extend([f.strip() for f in file_list.split(",") if f.strip()])
            
            changed_files = extracted_files
            
            if not changed_files:
                msg = "Stopped at Step 7: No test file generated."
                if not quiet: console.print(f"⏹️  {msg}")
                return False, msg, total_cost, last_model_used, changed_files

        # Step 8: Verification Failure
        if step_num == 8 and "FAIL: Test does not work as expected" in output:
            msg = "Stopped at Step 8: Generated test does not fail correctly (verification failed)."
            if not quiet: console.print(f"⏹️  {msg}")
            return False, msg, total_cost, last_model_used, changed_files

        # Soft Failure Logging (if not a hard stop)
        if not success and not quiet:
            console.print(f"[yellow]Warning: Step {step_num} reported failure, but proceeding as no hard stop condition met.[/yellow]")
        elif not quiet:
            # Extract a brief result for display if possible, otherwise generic
            console.print(f"  → Step {step_num} complete.")

    # --- Final Summary ---
    final_msg = "Investigation complete"
    if not quiet:
        console.print(f"✅ {final_msg}")
        console.print(f"   Total cost: ${total_cost:.4f}")
        console.print(f"   Files changed: {', '.join(changed_files)}")
        if worktree_path:
            console.print(f"   Worktree: {worktree_path}")

    return True, final_msg, total_cost, last_model_used, changed_files

if __name__ == "__main__":
    # Example usage logic could go here if needed for testing
    pass

