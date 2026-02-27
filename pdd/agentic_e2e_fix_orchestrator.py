from __future__ import annotations

import hashlib
import os
import subprocess
import sys
import time
import json
from datetime import datetime
from pathlib import Path
from typing import List, Tuple, Dict, Any, Optional, Set

from rich.console import Console

from .agentic_common import (
    run_agentic_task,
    load_workflow_state,
    save_workflow_state,
    clear_workflow_state,
    validate_cached_state,
    DEFAULT_MAX_RETRIES,
)
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess

# Constants
STEP_NAMES = {
    1: "unit_tests",
    2: "e2e_tests",
    3: "root_cause",
    4: "fix_e2e_tests",
    5: "identify_devunits",
    6: "create_unit_tests",
    7: "verify_tests",
    8: "run_pdd_fix",
    9: "verify_all",
}

STEP_DESCRIPTIONS = {
    1: "Running unit tests from issue",
    2: "Running e2e tests",
    3: "Analyzing root cause",
    4: "Fixing e2e tests",
    5: "Identifying dev units",
    6: "Creating unit tests",
    7: "Verifying tests detect bugs",
    8: "Running pdd fix",
    9: "Final verification",
}

# Per-step timeouts for the 9-step agentic e2e fix workflow
E2E_FIX_STEP_TIMEOUTS: Dict[int, float] = {
    1: 340.0,   # Run unit tests from issue, pdd fix failures
    2: 240.0,   # Run e2e tests, check completion (early exit)
    3: 340.0,   # Root cause analysis (code vs test vs both)
    4: 340.0,   # Fix e2e tests if needed
    5: 340.0,   # Identify dev units involved in failures
    6: 600.0,   # Create/append unit tests for dev units (Complex)
    7: 600.0,   # Verify unit tests detect bugs (Complex)
    8: 1000.0,  # Run pdd fix on failing dev units (Most Complex - multiple LLM calls)
    9: 240.0,   # Final verification, loop control
}

console = Console()

def _get_state_dir(cwd: Path) -> Path:
    """Returns the state directory .pdd/e2e-fix-state/ relative to git root."""
    # Simple heuristic: look for .git, otherwise use cwd
    d = cwd.resolve()
    root = d
    while d != d.parent:
        if (d / ".git").exists():
            root = d
            break
        d = d.parent
    
    state_dir = root / ".pdd" / "e2e-fix-state"
    state_dir.mkdir(parents=True, exist_ok=True)
    return state_dir

def _parse_changed_files(output: str) -> List[str]:
    """Parses FILES_CREATED and FILES_MODIFIED from agent output."""
    files = []
    for line in output.splitlines():
        if line.startswith("FILES_CREATED:") or line.startswith("FILES_MODIFIED:"):
            # Extract content after colon
            content = line.split(":", 1)[1].strip()
            if content:
                # Split by comma and strip
                paths = [p.strip() for p in content.split(",") if p.strip()]
                files.extend(paths)
    return files

def _parse_dev_units(output: str) -> str:
    """Parses DEV_UNITS_IDENTIFIED from output."""
    for line in output.splitlines():
        if line.startswith("DEV_UNITS_IDENTIFIED:"):
            return line.split(":", 1)[1].strip()
    return ""

def _update_dev_unit_states(output: str, current_states: Dict[str, Any], identified_units_str: str) -> Dict[str, Any]:
    """Updates dev unit states based on Step 8 output."""
    identified_units = [u.strip() for u in identified_units_str.split(",") if u.strip()]
    
    # Initialize if not present
    for unit in identified_units:
        if unit not in current_states:
            current_states[unit] = {"fixed": False, "fix_attempts": 0}
        current_states[unit]["fix_attempts"] += 1

    # Parse results from output
    # Heuristic: look for "unit_name: FIXED" or "unit_name: Failed"
    # This depends on the LLM following instructions in Step 8 prompt.
    for line in output.splitlines():
        for unit in identified_units:
            if unit in line:
                if "FIXED" in line:
                    current_states[unit]["fixed"] = True
                elif "Failed" in line or "FAIL" in line:
                    current_states[unit]["fixed"] = False
    
    return current_states

def _check_staleness(state: Dict[str, Any], cwd: Path) -> None:
    """Checks if files have changed since state was saved."""
    last_saved_str = state.get("last_saved_at")
    if not last_saved_str:
        return

    try:
        last_saved = datetime.fromisoformat(last_saved_str)
    except ValueError:
        return

    changed_files = state.get("changed_files", [])
    stale = False
    
    for file_path in changed_files:
        p = cwd / file_path
        if not p.exists():
            console.print(f"[yellow]Warning: File '{file_path}' from previous state is missing.[/yellow]")
            continue
        
        # Check mtime
        mtime = datetime.fromtimestamp(p.stat().st_mtime)
        if mtime > last_saved:
            stale = True
            break
    
    if stale:
        console.print("[yellow]Warning: Codebase may have changed since last run. Consider --no-resume for fresh start.[/yellow]")


def _get_modified_and_untracked(cwd: Path) -> Set[str]:
    """Returns set of modified tracked files plus untracked files."""
    files: Set[str] = set()

    # Get modified tracked files
    result = subprocess.run(
        ["git", "diff", "--name-only", "HEAD"],
        cwd=cwd,
        capture_output=True,
        text=True
    )
    if result.returncode == 0:
        files.update(f for f in result.stdout.strip().split("\n") if f)

    # Get untracked files
    result = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard"],
        cwd=cwd,
        capture_output=True,
        text=True
    )
    if result.returncode == 0:
        files.update(f for f in result.stdout.strip().split("\n") if f)

    return files


def _get_file_hashes(cwd: Path) -> Dict[str, Optional[str]]:
    """
    Returns {filepath: md5_hash} for all modified and untracked files.

    If a file is deleted or unreadable, stores None for that file.
    """
    hashes: Dict[str, Optional[str]] = {}
    for filepath in _get_modified_and_untracked(cwd):
        path = cwd / filepath
        if path.exists() and path.is_file():
            try:
                hashes[filepath] = hashlib.md5(path.read_bytes()).hexdigest()
            except (IOError, OSError):
                hashes[filepath] = None
        else:
            hashes[filepath] = None  # Deleted or not a file
    return hashes


def _detect_changed_files(cwd: Path, initial_file_hashes: Dict[str, Optional[str]]) -> List[str]:
    """Detects files actually changed during the workflow using hash comparison.

    Compares current file hashes against the snapshot taken before the workflow
    started to find files that were created or modified on disk, regardless of
    whether the LLM output included FILES_MODIFIED/FILES_CREATED markers.
    """
    current_hashes = _get_file_hashes(cwd)
    changed: List[str] = []
    for filepath, current_hash in current_hashes.items():
        if filepath not in initial_file_hashes:
            changed.append(filepath)
        elif initial_file_hashes[filepath] != current_hash:
            changed.append(filepath)
    return changed


def _has_unpushed_commits(cwd: Path) -> bool:
    """Check if there are commits ahead of the remote tracking branch."""
    result = subprocess.run(
        ["git", "rev-list", "--count", "@{u}..HEAD"],
        cwd=cwd,
        capture_output=True,
        text=True
    )
    if result.returncode == 0:
        count = int(result.stdout.strip() or "0")
        return count > 0
    return False


def _push_with_retry(
    cwd: Path,
    repo_owner: str,
    repo_name: str,
) -> Tuple[bool, str]:
    """
    Pushes to remote, retrying with PDD_GH_TOKEN_FILE on auth failure.

    On push auth failure (Authentication failed, HTTP 401, could not read Username,
    or HTTP Basic: Access denied):
    - If PDD_GH_TOKEN_FILE env var is set and the file exists with non-empty content:
      - Read the token from the file (strip whitespace)
      - Save the current remote origin URL
      - Set remote origin URL to https://x-access-token:{token}@github.com/{repo_owner}/{repo_name}.git
      - Retry the push once
      - Restore the original remote URL in a finally block (prevents token leakage in git config)
    - If no token file available, file is empty, or retry also fails: return (False, error)

    Returns:
        (success, message)
    """
    push_result = subprocess.run(
        ["git", "push"],
        cwd=cwd,
        capture_output=True,
        text=True
    )

    if push_result.returncode == 0:
        return True, ""

    stderr = push_result.stderr
    auth_errors = ["Authentication failed", "HTTP 401", "could not read Username", "HTTP Basic: Access denied"]
    is_auth_failure = any(err in stderr for err in auth_errors)

    if not is_auth_failure:
        return False, stderr

    # Auth failure — try PDD_GH_TOKEN_FILE
    token_file_path = os.environ.get("PDD_GH_TOKEN_FILE")
    if not token_file_path:
        return False, stderr

    token_path = Path(token_file_path)
    if not token_path.exists():
        return False, stderr

    token = token_path.read_text().strip()
    if not token:
        return False, stderr

    # Save original remote URL — abort retry if we can't capture it
    url_result = subprocess.run(
        ["git", "remote", "get-url", "origin"],
        cwd=cwd,
        capture_output=True,
        text=True
    )
    if url_result.returncode != 0:
        return False, stderr
    original_url = url_result.stdout.strip()

    try:
        # Set remote URL with token (URL-encode to guard against reserved characters)
        from urllib.parse import quote
        token_url = f"https://x-access-token:{quote(token, safe='')}@github.com/{repo_owner}/{repo_name}.git"
        subprocess.run(
            ["git", "remote", "set-url", "origin", token_url],
            cwd=cwd,
            capture_output=True,
            text=True
        )

        # Retry push
        retry_result = subprocess.run(
            ["git", "push"],
            cwd=cwd,
            capture_output=True,
            text=True
        )

        if retry_result.returncode == 0:
            return True, ""
        else:
            return False, retry_result.stderr
    finally:
        # Restore original remote URL (prevents token leakage in git config)
        if original_url:
            restore = subprocess.run(
                ["git", "remote", "set-url", "origin", original_url],
                cwd=cwd,
                capture_output=True,
                text=True
            )
            if restore.returncode != 0:
                print(f"WARNING: Failed to restore original remote URL: {restore.stderr}")


def _commit_and_push(
    cwd: Path,
    issue_number: int,
    issue_title: str,
    repo_owner: str,
    repo_name: str,
    initial_file_hashes: Dict[str, Optional[str]],
    quiet: bool = False
) -> Tuple[bool, str]:
    """
    Commits only files that changed during the workflow and pushes.

    Uses hash comparison to detect actual content changes, avoiding
    staging pre-existing modified/untracked files.

    The PR was already created by `pdd bug`, so pushing
    automatically updates it.

    On push auth failure, retries using PDD_GH_TOKEN_FILE if available.

    Args:
        cwd: Working directory
        issue_number: GitHub issue number
        issue_title: Issue title for commit message
        repo_owner: GitHub repository owner
        repo_name: GitHub repository name
        initial_file_hashes: File hashes from before workflow started
        quiet: Suppress output

    Returns:
        (success, message)
    """
    # Get current file hashes
    current_hashes = _get_file_hashes(cwd)

    # Find files that changed during workflow
    files_to_commit: List[str] = []
    for filepath, current_hash in current_hashes.items():
        if filepath not in initial_file_hashes:
            # New file created during workflow
            files_to_commit.append(filepath)
        elif initial_file_hashes[filepath] != current_hash:
            # Content changed during workflow
            files_to_commit.append(filepath)

    if not files_to_commit:
        # Fallback: hash snapshot may be tainted (captured after a prior
        # interrupted run's modifications already existed on disk). Check
        # git diff directly to catch orphaned unstaged changes (#545).
        fallback_files = _get_modified_and_untracked(cwd)
        if fallback_files:
            files_to_commit = list(fallback_files)
        elif _has_unpushed_commits(cwd):
            # Check if there are unpushed commits to push
            push_ok, push_err = _push_with_retry(cwd, repo_owner, repo_name)
            if push_ok:
                return True, "Pushed existing commits"
            else:
                return False, f"Push failed: {push_err}"
        else:
            return True, "No changes to commit"

    # Stage only workflow-changed files
    for filepath in files_to_commit:
        stage_result = subprocess.run(
            ["git", "add", filepath],
            cwd=cwd,
            capture_output=True,
            text=True
        )
        if stage_result.returncode != 0:
            return False, f"Failed to stage {filepath}: {stage_result.stderr}"

    # Commit with message referencing issue
    commit_msg = f"fix: {issue_title}\n\nFixes #{issue_number}"
    commit_result = subprocess.run(
        ["git", "commit", "-m", commit_msg],
        cwd=cwd,
        capture_output=True,
        text=True
    )
    if commit_result.returncode != 0:
        return False, f"Failed to commit: {commit_result.stderr}"

    # Push to remote with retry on auth failure
    push_ok, push_err = _push_with_retry(cwd, repo_owner, repo_name)

    if push_ok:
        return True, f"Committed and pushed {len(files_to_commit)} file(s)"
    else:
        return False, f"Push failed: {push_err}"


def run_agentic_e2e_fix_orchestrator(
    issue_url: str,
    issue_content: str,
    repo_owner: str,
    repo_name: str,
    issue_number: int,
    issue_author: str,
    issue_title: str,
    *,
    cwd: Path,
    timeout_adder: float = 0.0,
    max_cycles: int = 5,
    resume: bool = True,
    verbose: bool = False,
    quiet: bool = False,
    use_github_state: bool = True,
    protect_tests: bool = False
) -> Tuple[bool, str, float, str, List[str]]:
    """
    Orchestrator for the 9-step agentic e2e fix workflow.
    
    Returns:
        Tuple[bool, str, float, str, List[str]]: 
        (success, final_message, total_cost, model_used, changed_files)
    """
    state_dir = _get_state_dir(cwd)
    workflow_name = "e2e_fix"
    
    # Initialize state variables
    current_cycle = 0
    last_completed_step = 0
    step_outputs: Dict[str, str] = {}
    total_cost = 0.0
    model_used = "unknown"
    changed_files: List[str] = []
    dev_unit_states: Dict[str, Any] = {}
    github_comment_id: Optional[int] = None
    
    # Resume Logic
    if resume:
        loaded_state, gh_id = load_workflow_state(
            cwd, issue_number, workflow_name, state_dir, repo_owner, repo_name, use_github_state
        )
        if loaded_state:
            console.print(f"[blue]Resuming from cycle {loaded_state.get('current_cycle', 1)} step {loaded_state.get('last_completed_step', 0)}...[/blue]")
            current_cycle = loaded_state.get("current_cycle", 0)
            last_completed_step = loaded_state.get("last_completed_step", 0)
            step_outputs = loaded_state.get("step_outputs", {})
            total_cost = loaded_state.get("total_cost", 0.0)
            model_used = loaded_state.get("model_used", "unknown")
            changed_files = loaded_state.get("changed_files", [])
            dev_unit_states = loaded_state.get("dev_unit_states", {})
            github_comment_id = gh_id

            # Issue #467: Validate cached state — correct last_completed_step
            # if any cached step outputs have "FAILED:" prefix.
            last_completed_step = validate_cached_state(
                last_completed_step, step_outputs, quiet=quiet
            )

            _check_staleness(loaded_state, cwd)

            # If we finished a cycle but didn't exit, prepare for next cycle
            if last_completed_step >= 9:
                current_cycle += 1
                last_completed_step = 0
                step_outputs = {} # Clear outputs for new cycle
        else:
            # No state found, start fresh
            clear_workflow_state(cwd, issue_number, workflow_name, state_dir, repo_owner, repo_name, use_github_state)
    else:
        clear_workflow_state(cwd, issue_number, workflow_name, state_dir, repo_owner, repo_name, use_github_state)

    console.print(f"Fixing e2e tests for issue #{issue_number}: \"{issue_title}\"")

    # Snapshot file state before workflow (for hash-based commit detection)
    initial_file_hashes = _get_file_hashes(cwd)

    success = False
    final_message = ""

    try:
        # Outer Loop
        if current_cycle == 0:
            current_cycle = 1
        
        while current_cycle <= max_cycles:
            console.print(f"\n[bold cyan][Cycle {current_cycle}/{max_cycles}] Starting fix cycle...[/bold cyan]")
            
            # Inner Loop (Steps 1-9)
            for step_num in range(1, 10):
                if step_num <= last_completed_step:
                    continue # Skip already completed steps in this cycle

                step_name = STEP_NAMES[step_num]
                description = STEP_DESCRIPTIONS[step_num]
                
                console.print(f"[bold][Step {step_num}/9] {description}...[/bold]")
                
                # 1. Load Prompt
                template_name = f"agentic_e2e_fix_step{step_num}_{step_name}_LLM"
                prompt_template = load_prompt_template(template_name)
                if not prompt_template:
                    raise ValueError(f"Could not load prompt template: {template_name}")

                # 2. Prepare Context
                context = {
                    "issue_url": issue_url,
                    "repo_owner": repo_owner,
                    "repo_name": repo_name,
                    "issue_number": issue_number,
                    "cycle_number": current_cycle,
                    "max_cycles": max_cycles,
                    "issue_content": issue_content,
                    "protect_tests": "true" if protect_tests else "false",
                    "protect_tests_flag": "--protect-tests" if protect_tests else "",
                }
                
                # Add previous step outputs
                for prev_step in range(1, step_num):
                    key = f"step{prev_step}_output"
                    context[key] = step_outputs.get(str(prev_step), "")

                # Derived variables for specific steps
                if step_num >= 6:
                    s5_out = step_outputs.get("5", "")
                    context["dev_units_identified"] = _parse_dev_units(s5_out)
                
                if step_num == 8:
                    s5_out = step_outputs.get("5", "")
                    context["failing_dev_units"] = _parse_dev_units(s5_out)

                if step_num == 9:
                    context["next_cycle"] = current_cycle + 1

                # Preprocess to escape curly braces in included content
                exclude_keys = list(context.keys())
                prompt_template = preprocess(prompt_template, recursive=True, double_curly_brackets=True, exclude_keys=exclude_keys)
                # Safe substitution (Issue #549): un-double template braces first, then substitute.
                prompt_template = prompt_template.replace("{{", "{").replace("}}", "}")
                formatted_prompt = prompt_template
                for key, value in context.items():
                    formatted_prompt = formatted_prompt.replace(f'{{{key}}}', str(value))

                # 3. Run Task
                base_timeout = E2E_FIX_STEP_TIMEOUTS.get(step_num, 340.0)
                timeout = base_timeout + timeout_adder

                step_success, step_output, step_cost, step_model = run_agentic_task(
                    instruction=formatted_prompt,
                    cwd=cwd,
                    verbose=verbose,
                    quiet=quiet,
                    timeout=timeout,
                    label=f"cycle{current_cycle}_step{step_num}",
                    max_retries=DEFAULT_MAX_RETRIES,
                )

                # 4. Store Output & Accumulate
                # Only mark step completed if it succeeded; failed steps get "FAILED:" prefix
                # and last_completed_step stays at previous step (ensures resume re-runs failed step)
                if step_success:
                    step_outputs[str(step_num)] = step_output
                    last_completed_step = step_num
                else:
                    step_outputs[str(step_num)] = f"FAILED: {step_output}"
                    # Don't update last_completed_step - keep it at previous value

                total_cost += step_cost
                model_used = step_model if step_model else model_used

                # Parse changed files
                new_files = _parse_changed_files(step_output)
                for f in new_files:
                    if f not in changed_files:
                        changed_files.append(f)

                # Parse dev unit states (Step 8)
                if step_num == 8:
                    s5_out = step_outputs.get("5", "")
                    dev_units_str = _parse_dev_units(s5_out)
                    dev_unit_states = _update_dev_unit_states(step_output, dev_unit_states, dev_units_str)

                # Print brief result
                if step_success:
                    console.print(f"  -> Step {step_num} complete. Cost: ${step_cost:.4f}")
                else:
                    console.print(f"  -> Step {step_num} [red]failed[/red]. Cost: ${step_cost:.4f}")

                # 5. Save State
                state_data = {
                    "workflow": workflow_name,
                    "issue_url": issue_url,
                    "issue_number": issue_number,
                    "current_cycle": current_cycle,
                    "last_completed_step": last_completed_step,
                    "step_outputs": step_outputs.copy(),  # Copy to avoid shared reference
                    "dev_unit_states": dev_unit_states.copy(),  # Copy to avoid shared reference
                    "total_cost": total_cost,
                    "model_used": model_used,
                    "changed_files": changed_files.copy(),  # Copy to avoid shared reference
                    "last_saved_at": datetime.now().isoformat(),
                    "github_comment_id": github_comment_id
                }
                
                new_gh_id = save_workflow_state(
                    cwd, issue_number, workflow_name, state_data, state_dir, repo_owner, repo_name, use_github_state, github_comment_id
                )
                if new_gh_id:
                    github_comment_id = new_gh_id

                # Check Early Exit (Step 2): ALL_TESTS_PASS
                if step_num == 2 and "ALL_TESTS_PASS" in step_output:
                    console.print("[green]ALL_TESTS_PASS detected in Step 2. Exiting loop.[/green]")
                    success = True
                    final_message = "All tests passed during e2e check."
                    break

                # Check Early Exit (Step 3): NOT_A_BUG
                if step_num == 3 and "NOT_A_BUG" in step_output:
                    console.print("[yellow]NOT_A_BUG detected in Step 3. Issue is not a bug, stopping workflow.[/yellow]")
                    success = False
                    final_message = "Issue determined to be not a bug."
                    break

                # Check Loop Control (Step 9)
                if step_num == 9:
                    if "ALL_TESTS_PASS" in step_output:
                        console.print("[green]ALL_TESTS_PASS detected in Step 9.[/green]")
                        success = True
                        final_message = "All tests passed after fixes."
                        break
                    elif "MAX_CYCLES_REACHED" in step_output:
                        console.print("[yellow]MAX_CYCLES_REACHED detected in Step 9.[/yellow]")
                    elif "CONTINUE_CYCLE" not in step_output:
                        console.print("[yellow]Warning: No loop control token found in Step 9. Defaulting to CONTINUE_CYCLE.[/yellow]")

            # Check if we should exit the outer loop
            if success:
                break
            
            # Check if NOT_A_BUG was detected (exit outer loop too)
            if step_num == 3 and "NOT_A_BUG" in step_outputs.get("3", ""):
                break
            
            # Prepare for next cycle
            current_cycle += 1
            last_completed_step = 0
            step_outputs = {} # Clear outputs for next cycle
            
            state_data["current_cycle"] = current_cycle
            state_data["last_completed_step"] = 0
            state_data["step_outputs"] = {}
            state_data["last_saved_at"] = datetime.now().isoformat()
            
            if current_cycle <= max_cycles:
                 save_workflow_state(
                    cwd, issue_number, workflow_name, state_data, state_dir, repo_owner, repo_name, use_github_state, github_comment_id
                )

        if success:
            clear_workflow_state(cwd, issue_number, workflow_name, state_dir, repo_owner, repo_name, use_github_state)

            # Detect actual file changes via hash comparison (not LLM output parsing)
            # This fixes issue #355: summary showing empty "Files changed" despite
            # real modifications, especially on early exit at Step 2.
            actual_changed_files = _detect_changed_files(cwd, initial_file_hashes)
            if actual_changed_files:
                changed_files = actual_changed_files

            console.print("\n[bold green]E2E fix complete[/bold green]")
            console.print(f"   Total cost: ${total_cost:.4f}")
            console.print(f"   Cycles used: {current_cycle if current_cycle <= max_cycles else max_cycles}/{max_cycles}")
            console.print(f"   Files changed: {', '.join(changed_files)}")
            fixed_units = [u for u, s in dev_unit_states.items() if s.get("fixed")]
            console.print(f"   Dev units fixed: {', '.join(fixed_units)}")

            # Commit and push changes to update the existing PR
            commit_success, commit_message = _commit_and_push(
                cwd=cwd,
                issue_number=issue_number,
                issue_title=issue_title,
                repo_owner=repo_owner,
                repo_name=repo_name,
                initial_file_hashes=initial_file_hashes,
                quiet=quiet
            )
            if commit_success:
                console.print(f"   [green]{commit_message}[/green]")
            else:
                console.print(f"   [yellow]Warning: {commit_message}[/yellow]")

            return True, final_message, total_cost, model_used, changed_files
        else:
            if not final_message:
                final_message = f"Max cycles ({max_cycles}) reached without all tests passing"
            if "not a bug" in final_message.lower():
                console.print(f"\n[bold yellow]E2E fix stopped: not a bug[/bold yellow]")
            else:
                console.print(f"\n[bold red]E2E fix incomplete[/bold red]")
            console.print(f"   Total cost: ${total_cost:.4f}")
            remaining = [u for u, s in dev_unit_states.items() if not s.get("fixed")]
            if remaining:
                console.print(f"   Remaining failures: {', '.join(remaining)}")
            return False, final_message, total_cost, model_used, changed_files

    except KeyboardInterrupt:
        console.print("\n[bold red]Interrupted by user. Saving state...[/bold red]")
        state_data = {
            "workflow": workflow_name,
            "issue_url": issue_url,
            "issue_number": issue_number,
            "current_cycle": current_cycle,
            "last_completed_step": last_completed_step,
            "step_outputs": step_outputs,
            "dev_unit_states": dev_unit_states,
            "total_cost": total_cost,
            "model_used": model_used,
            "changed_files": changed_files,
            "last_saved_at": datetime.now().isoformat(),
            "github_comment_id": github_comment_id
        }
        save_workflow_state(
            cwd, issue_number, workflow_name, state_data, state_dir, repo_owner, repo_name, use_github_state, github_comment_id
        )
        raise

    except Exception as e:
        console.print(f"\n[bold red]Fatal error: {e}[/bold red]")
        try:
            state_data = {
                "workflow": workflow_name,
                "issue_url": issue_url,
                "issue_number": issue_number,
                "current_cycle": current_cycle,
                "last_completed_step": last_completed_step,
                "step_outputs": step_outputs,
                "dev_unit_states": dev_unit_states,
                "total_cost": total_cost,
                "model_used": model_used,
                "changed_files": changed_files,
                "last_saved_at": datetime.now().isoformat(),
                "github_comment_id": github_comment_id
            }
            save_workflow_state(
                cwd, issue_number, workflow_name, state_data, state_dir, repo_owner, repo_name, use_github_state, github_comment_id
            )
        except Exception:
            pass
        return False, f"Stopped at cycle {current_cycle} step {last_completed_step}: {str(e)}", total_cost, model_used, changed_files
