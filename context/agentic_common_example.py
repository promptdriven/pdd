from __future__ import annotations

import os
import sys
import json
import re
import shutil
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple, Union
from rich.console import Console

# Configure absolute import reference relative to the project root
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.agentic_common import (
    SteerEntry,
    AgenticTaskResult,
    EffortCapability,
    run_agentic_task as _run_agentic_task,
    load_workflow_state as _load_workflow_state,
    save_workflow_state,
    clear_workflow_state as _clear_workflow_state,
    get_agent_provider_preference,
    get_available_agents,
    get_agentic_capabilities,
    validate_claude_policy,
    build_agentic_task_instruction,
    select_harness_for_task,
    detect_control_token,
    classify_step_output,
    validate_cached_state,
    github_save_state,
    github_load_state,
    github_clear_state,
    drain_issue_steers,
    post_step_comment,
    post_pr_comment,
    post_final_comment,
    post_step_comment_once,
    normalize_step_comments_state,
    extract_step_report,
    _extract_step_report,
)

console = Console()

# Ensure output directory exists
OUTPUT_DIR = Path("./output")
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)


def run_agentic_task(*args: Any, **kwargs: Any) -> AgenticTaskResult:
    """Delegate to the public agentic task runner for selector-based prompts."""
    return _run_agentic_task(*args, **kwargs)


def load_workflow_state(
    cwd: Path,
    issue_number: int,
    workflow_type: str,
    state_dir: Path,
    repo_owner: str,
    repo_name: str,
    use_github_state: bool = True,
) -> Tuple[Optional[Dict], Optional[int]]:
    """Delegate to the shared workflow-state loader."""
    return _load_workflow_state(
        cwd,
        issue_number,
        workflow_type,
        state_dir,
        repo_owner,
        repo_name,
        use_github_state,
    )


def clear_workflow_state(
    cwd: Path,
    issue_number: int,
    workflow_type: str,
    state_dir: Path,
    repo_owner: str,
    repo_name: str,
    use_github_state: bool = True,
) -> bool:
    """Delegate to the shared workflow-state clearer."""
    return _clear_workflow_state(
        cwd,
        issue_number,
        workflow_type,
        state_dir,
        repo_owner,
        repo_name,
        use_github_state,
    )


# Helper to simulate fetching comments internally
def _fetch_comments(repo_owner: str, repo_name: str, issue_number: int) -> List[Dict[str, Any]]:
    """Simulate fetching issue comments."""
    return [
        {
            "id": 101,
            "user": {"login": "collaborator1", "type": "User"},
            "body": "Let's focus only on validating Python files for now.",
            "created_at": "2026-01-01T12:00:00Z"
        }
    ]

# Helper for brace replacement
def _escape_format_braces(template: str) -> str:
    """Escape raw JSON braces so they are not treated as format placeholders."""
    return template.replace("{", "{{").replace("}", "}}")

# Helper for JSON extraction
def _extract_json_from_text(text: str) -> Optional[Dict[str, Any]]:
    """Find first complete JSON block in raw text."""
    match = re.search(r"\{.*\}", text, re.DOTALL)
    if match:
        try:
            return json.loads(match.group(0))
        except json.JSONDecodeError:
            pass
    return None

# Helpers for GitHub URL parsing
def _parse_pr_url(url: str) -> Optional[Tuple[str, str, int]]:
    """Extract repo owner, name, and PR number from a standard GitHub URL."""
    match = re.match(r"https://github\.com/([^/]+)/([^/]+)/pull/(\d+)", url)
    if match:
        return match.group(1), match.group(2), int(match.group(3))
    return None

def _is_github_issue_url(url: str) -> bool:
    """Check if the URL points to a GitHub issue."""
    return bool(re.match(r"https://github\.com/[^/]+/[^/]+/issues/\d+", url))

def _sanitize_comment_body(body: str) -> str:
    """Sanitize comments by removing possible sensitive patterns like API keys."""
    return re.sub(r"(sk-[a-zA-Z0-9]+)", "[REDACTED_API_KEY]", body)


def example_provider_preference() -> None:
    """Demonstrate how to fetch provider preference order and verify availability."""
    console.print("[bold blue]--- Provider Preference & Availability Example ---[/bold blue]")
    
    # Check overall agent availability based on system PATH and keys
    available = get_available_agents()
    console.print(f"Available agents detected: {available}")
    
    # Retrieve active provider preference sequence
    prefs = get_agent_provider_preference()
    console.print(f"Active provider preferences: {prefs}")
    
    # Resolve prioritized candidates
    candidates = [p for p in prefs if p in available]
    console.print(f"Effective candidates resolved: {candidates}\n")


def example_run_agentic_task() -> None:
    """Demonstrate launching an agentic workspace task using available CLIs."""
    console.print("[bold blue]--- Run Agentic Task Example ---[/bold blue]")
    
    # Verify required environment configuration beforehand
    api_key_check = os.environ.get("ANTHROPIC_API_KEY") or os.environ.get("OPENAI_API_KEY")
    if not api_key_check:
        console.print("[yellow]Neither ANTHROPIC_API_KEY nor OPENAI_API_KEY is configured. Skipping run demonstration.[/yellow]\n")
        return

    # Define task specifications
    instruction = "Check the current project structure and generate a summary report inside './output/report.txt'."
    cwd_path = Path(".")
    
    # Construct the formatted task prompt structure
    full_instruction = build_agentic_task_instruction(
        instruction=instruction, 
        user_feedback="Verify there are no unresolved syntax errors."
    )
    console.print(f"Generated Workspace Prompt Payload:\n[dim]{full_instruction}[/dim]")

    # Set up a strict tool/filesystem access policy for Claude if applicable
    policy_config = {
        "allowedTools": "Read,Write,Bash",
        "addDirs": ["./output"],
        "writableRoots": ["./output"],
        "readOnlyRoots": ["./pdd"],
        "noSessionPersistence": True,
        "outputFormat": "json"
    }
    
    try:
        validated_policy = validate_claude_policy(policy_config)
    except Exception as exc:
        console.print(f"[red]Claude policy validation failed: {exc}[/red]")
        return

    # Execute the agentic cycle
    result = run_agentic_task(
        instruction=instruction,
        cwd=cwd_path,
        verbose=False,
        label="generate_report_step",
        timeout=180.0,  # Bounded execution window (seconds)
        max_retries=2,
        claude_policy=validated_policy,
        task_class="single_file"
    )
    
    console.print(f"Execution Outcome: {result.success}")
    console.print(f"Active Provider: {result.provider}")
    console.print(f"Attributed Model: {result.model_id}")
    console.print(f"Incurred Cost (USD): ${result.cost_usd:.5f}")
    console.print(f"Cumulative Cost (USD): ${result.cumulative_cost_usd:.5f}")
    console.print(f"Modified Files: {result.changed_files}")
    console.print(f"Usage Source: {result.usage_source} ({result.estimate_method})\n")


def example_validate_cached_state() -> None:
    """Demonstrate how to detect and correct the 'blind resume' issue."""
    console.print("[bold blue]--- Cached State Validation Example ---[/bold blue]")
    
    # State with step '2' containing a recorded failure marker
    step_outputs = {
        "1": "Success: File created.",
        "2": "FAILED: Permission denied trying to bind port.",
        "3": "Success: Cleaned up temp assets."
    }
    
    # Validate and rewind 'last_completed_step' to the last functional milestone
    last_completed = 3
    corrected_step = validate_cached_state(
        last_completed_step=last_completed,
        step_outputs=step_outputs,
        step_order=[1, 2, 3]
    )
    console.print(f"Stated last step: {last_completed} -> Corrected resume target milestone: {corrected_step}\n")


def example_post_step_comment() -> None:
    """Demonstrate the visible comment reporting pipeline."""
    console.print("[bold blue]--- Visible Step Comment Reporting Example ---[/bold blue]")
    
    # Scenario A: Visible summary extracted from successful agent execution block
    raw_model_response = """Some analysis prose.
<step_report>
### Step Completed Successfully
- Analyzed routing policies
- Identified 2 duplicate records
</step_report>
More trailing output metadata."""
    
    extracted = extract_step_report(raw_model_response)
    console.print(f"Extracted report content: {repr(extracted)}")
    
    # Scenario B: Redaction and formatting of comments to post on GitHub
    raw_secret_report = "An error occurred while calling sk-API_KEY_OR_SECRET_TOKEN."
    sanitized = _sanitize_comment_body(raw_secret_report)
    console.print(f"Sanitized Body (Redacted Secrets): {repr(sanitized)}")
    
    # Scenario C: Posting step comments using the state set
    posted_set: Set[int] = set()
    mock_body = "### Automated step status update."
    
    # Idempotent first post
    posted_first = post_step_comment_once(
        repo_owner="pdd-org",
        repo_name="pdd-core",
        issue_number=45,
        step_num=1,
        body=mock_body,
        posted_steps=posted_set,
        cwd=Path(".")
    )
    console.print(f"First Comment Attempt success (or skipped due to mock mode): {posted_first}")
    console.print(f"Active posted steps tracker: {posted_set}")
    
    # Re-evaluating tracking rehydration
    persisted_state = {"1": {"posted": True}, "2": {"failed_pending": True}}
    rehydrated_set = normalize_step_comments_state(persisted_state)
    console.print(f"Rehydrated sets from state object: {rehydrated_set}\n")


def example_post_pr_comment():
    """Demonstrate posting standard PR validation status comments."""
    console.print("[bold blue]--- Post PR Comment Example ---[/bold blue]")
    
    # Check if gh binary is available
    gh_available = any(shutil.which(cmd) for cmd in ["gh"])
    if not gh_available:
        console.print("[yellow]gh CLI not found on PATH. Comment posting will simulate fallback behavior.[/yellow]")
    
    posted = post_pr_comment(
        repo_owner="pdd-org",
        repo_name="pdd-core",
        pr_number=101,
        body="### Integration Check\nVerification run completed cleanly.",
        cwd=Path(".")
    )
    console.print(f"PR comment invocation returned: {posted}\n")


def example_post_final_comment() -> None:
    """Demonstrate posting a final summary comment when stopping early."""
    console.print("[bold blue]--- Post Final Comment Example ---[/bold blue]")
    
    posted = post_final_comment(
        repo_owner="pdd-org",
        repo_name="pdd-core",
        issue_number=12,
        reason="NOT_A_BUG",
        total_cost=0.0825,
        steps_completed=2,
        total_steps=5,
        cwd=Path(".")
    )
    console.print(f"Final stop comment invocation returned: {posted}\n")


def example_github_state_helpers() -> None:
    """Demonstrate persisting, rehydrating, and clearing issue-state comments."""
    console.print("[bold blue]--- GitHub State Comment Persistence Example ---[/bold blue]")
    
    # Define coordinate details
    repo_owner = "pdd-org"
    repo_name = "pdd-core"
    issue_number = 45
    workflow_type = "bug-fix"
    local_state_dir = OUTPUT_DIR
    
    # Establish example state content payload
    test_state = {
        "last_completed_step": 2,
        "step_outputs": {
            "1": "Success",
            "2": "Success"
        },
        "step_comments": [1, 2]
    }
    
    # Save workflow state (local caching and GitHub POST/PATCH syncing)
    comment_id = save_workflow_state(
        cwd=Path("."),
        issue_number=issue_number,
        workflow_type=workflow_type,
        state=test_state,
        state_dir=local_state_dir,
        repo_owner=repo_owner,
        repo_name=repo_name,
        use_github_state=False,  # Set to False to prevent hitting actual gh API
        dedupe=True
    )
    console.print(f"State saved. Generated comment ID placeholder: {comment_id}")
    
    # Load state (rehydrating the local cache fallback)
    rehydrated_state, active_comment_id = load_workflow_state(
        cwd=Path("."),
        issue_number=issue_number,
        workflow_type=workflow_type,
        state_dir=local_state_dir,
        repo_owner=repo_owner,
        repo_name=repo_name,
        use_github_state=False
    )
    console.print(f"Rehydrated state last completed: {rehydrated_state.get('last_completed_step') if rehydrated_state else 'None'}")
    
    # Clear state locally and clean up workspace
    cleared = clear_workflow_state(
        cwd=Path("."),
        issue_number=issue_number,
        workflow_type=workflow_type,
        state_dir=local_state_dir,
        repo_owner=repo_owner,
        repo_name=repo_name,
        use_github_state=False
    )
    console.print(f"State files purged: {cleared}\n")


def example_consecutive_provider_failures_guard() -> None:
    """Show the provider-failure counter used by agentic orchestrators."""
    consecutive_provider_failures = 0
    for step_success in [False, False, True]:
        if step_success:
            consecutive_provider_failures = 0
        else:
            consecutive_provider_failures += 1
    console.print(f"Consecutive provider failures: {consecutive_provider_failures}")


def main() -> None: 
    """Run all agentic infrastructure usage examples sequentially."""
    console.print("[bold green]=== PDD Agentic Common Infrastructure Demonstration ===[/bold green]\n")
    example_provider_preference()
    example_run_agentic_task()
    example_validate_cached_state()
    example_post_step_comment()
    example_post_pr_comment()
    example_post_final_comment()
    example_github_state_helpers()
    example_consecutive_provider_failures_guard()
    console.print("[bold green]=== Demonstration Finished Successfully ===[/bold green]")


if __name__ == "__main__":
    main()
