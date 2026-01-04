from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import List, Tuple, Optional, Dict, Any

from rich.console import Console
from rich.panel import Panel
from rich.text import Text

# Internal imports using relative syntax
from .agentic_common import run_agentic_task
from .load_prompt_template import load_prompt_template

# Initialize Rich console
console = Console()


def _extract_files_created(output: str) -> List[str]:
    """
    Extract file paths from FILES_CREATED line in agent output.

    Looks for pattern: FILES_CREATED: path1, path2, ...

    Args:
        output: The agent's output text.

    Returns:
        List of file paths, or empty list if not found.
    """
    # Match FILES_CREATED: followed by comma-separated paths
    pattern = r"FILES_CREATED:\s*(.+)"
    match = re.search(pattern, output)
    if not match:
        return []

    paths_str = match.group(1).strip()
    if not paths_str:
        return []

    # Split by comma and clean up each path
    paths = [p.strip() for p in paths_str.split(",")]
    # Filter out empty strings and backticks (in case of markdown formatting)
    paths = [p.strip("`") for p in paths if p.strip() and p.strip() != "`"]
    return paths


def _print_step_header(step_num: int, total_steps: int, description: str, quiet: bool) -> None:
    """Helper to print a standardized step header."""
    if quiet:
        return
    console.print(f"\n[bold cyan][Step {step_num}/{total_steps}][/bold cyan] {description}...")


def _print_result(result: str, quiet: bool) -> None:
    """Helper to print the result of a step."""
    if quiet:
        return
    console.print(f"  [dim]→ {result}[/dim]")


def _check_hard_stop(step_num: int, output: str) -> Optional[str]:
    """
    Checks output for specific hard stop conditions based on the step number.
    Returns the reason string if a stop is triggered, otherwise None.
    """
    output_lower = output.lower()
    
    if step_num == 1:
        if "duplicate of #" in output_lower:
            return "Issue is a duplicate"
            
    elif step_num == 2:
        if "feature request (not a bug)" in output_lower:
            return "Feature Request (Not a Bug)"
        if "user error (not a bug)" in output_lower:
            return "User Error (Not a Bug)"
            
    elif step_num == 3:
        if "needs more info" in output_lower:
            return "Needs more info from author"
            
    elif step_num == 8:
        if "fail: test does not work as expected" in output_lower:
            return "Test verification failed"

    return None


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

    Args:
        issue_url: Full URL of the GitHub issue.
        issue_content: Body text of the issue.
        repo_owner: Owner of the repository.
        repo_name: Name of the repository.
        issue_number: The issue number.
        issue_author: Username of the issue creator.
        issue_title: Title of the issue.
        cwd: Current working directory for the agent.
        verbose: If True, prints detailed agent output.
        quiet: If True, suppresses standard output (except errors).

    Returns:
        Tuple containing:
        - success (bool): True if the workflow completed without hard stops.
        - final_message (str): Summary message or stop reason.
        - total_cost (float): Accumulated cost of all steps.
        - model_used (str): The last model used (or dominant model).
        - changed_files (List[str]): List of files modified during the process.
    """
    
    if not quiet:
        console.print(Panel(
            f"Investigating issue #{issue_number}: \"{issue_title}\"\n[link={issue_url}]{issue_url}[/link]",
            title="🔍 Agentic Bug Investigation",
            border_style="blue"
        ))

    # Initialize state
    total_cost = 0.0
    all_changed_files: List[str] = []
    last_model_used = "N/A"
    
    # Context accumulation dictionary
    # Keys will be 'step1_output', 'step2_output', etc.
    context: Dict[str, str] = {}

    # Define the steps
    steps = [
        (1, "duplicate", "Search for duplicate issues"),
        (2, "docs", "Check documentation for user error"),
        (3, "triage", "Assess if enough info to proceed"),
        (4, "reproduce", "Attempt to reproduce the bug"),
        (5, "root_cause", "Analyze root cause"),
        (6, "test_plan", "Design test strategy"),
        (7, "generate", "Generate failing unit test"),
        (8, "verify", "Verify test catches the bug"),
        (9, "pr", "Create draft PR and link to issue"),
    ]

    for step_num, name, description in steps:
        _print_step_header(step_num, len(steps), description, quiet)

        # 1. Load Prompt Template
        template_name = f"agentic_bug_step{step_num}_{name}_LLM"
        prompt_template = load_prompt_template(template_name)
        
        if not prompt_template:
            error_msg = f"Failed to load prompt template: {template_name}"
            console.print(f"[bold red]{error_msg}[/bold red]")
            return False, error_msg, total_cost, last_model_used, all_changed_files

        # 2. Format Template
        # Prepare arguments for formatting. We pass all accumulated context.
        format_args = {
            "issue_url": issue_url,
            "repo_owner": repo_owner,
            "repo_name": repo_name,
            "issue_number": issue_number,
            "issue_content": issue_content,
            "issue_author": issue_author,
            **context  # Unpack step1_output, step2_output, etc.
        }

        # Handle potential missing keys in template formatting gracefully
        # (though templates should be designed to match this context)
        try:
            formatted_prompt = prompt_template.format(**format_args)
        except KeyError as e:
            # Fallback: if a template expects a key we don't have, try to fill it with empty string
            # or fail gracefully. For now, we assume templates are correct.
            error_msg = f"Template formatting error in step {step_num}: Missing key {e}"
            console.print(f"[bold red]{error_msg}[/bold red]")
            return False, error_msg, total_cost, last_model_used, all_changed_files

        # 3. Run Agentic Task
        step_success, step_output, step_cost, step_provider = run_agentic_task(
            instruction=formatted_prompt,
            cwd=cwd,
            verbose=verbose,
            quiet=quiet,
            label=f"step{step_num}"
        )

        # Update tracking variables
        total_cost += step_cost
        if step_provider:
            last_model_used = step_provider

        # 4. Store Output for Context
        # Even if the step "failed" (returned False), we store the output because
        # the agent might have provided useful error info, unless it's a hard stop.
        context[f"step{step_num}_output"] = step_output

        # 5. Check Hard Stop Conditions
        stop_reason = _check_hard_stop(step_num, step_output)

        # Special check for Step 7 (File generation)
        # Parse the output for FILES_CREATED to verify test files were created
        if step_num == 7:
            step_files = _extract_files_created(step_output)
            if step_files:
                # Add created files to tracking list
                for f in step_files:
                    if f not in all_changed_files:
                        all_changed_files.append(f)
            else:
                stop_reason = "No test file generated"

        if stop_reason:
            if not quiet:
                console.print(f"\n[bold yellow]⏹️  Investigation stopped at Step {step_num}: {stop_reason}[/bold yellow]")
                _print_result(step_output.split('\n')[0][:100] + "...", quiet)  # Print brief output
            
            return False, f"Stopped at step {step_num}: {stop_reason}", total_cost, last_model_used, all_changed_files

        # Soft failure handling (Agent returned False, but no hard stop pattern matched)
        if not step_success:
            if not quiet:
                console.print(f"[yellow]Warning: Step {step_num} reported failure, but continuing workflow.[/yellow]")

        # Print brief result for the user
        # We take the first line or a snippet of the output as a summary
        summary_snippet = step_output.strip().split('\n')[0]
        if len(summary_snippet) > 80:
            summary_snippet = summary_snippet[:77] + "..."
        _print_result(summary_snippet, quiet)

    # Final Summary
    final_msg = "Investigation complete"
    if not quiet:
        console.print(Panel(
            f"Total Cost: ${total_cost:.4f}\n"
            f"Files Changed: {', '.join(all_changed_files) if all_changed_files else 'None'}\n"
            f"Model: {last_model_used}",
            title="✅ Investigation Complete",
            border_style="green"
        ))

    return True, final_msg, total_cost, last_model_used, all_changed_files