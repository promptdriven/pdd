from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

from rich.console import Console

# Ensure the pdd package is discoverable relative to this script
sys.path.append(str(Path(__file__).resolve().parent.parent))

from pdd.agentic_common import (
    post_pr_comment,
    get_agent_provider_preference,
    get_available_agents,
    run_agentic_task,
    detect_control_token,
    validate_claude_policy,
    AgenticTaskResult,
)

console = Console()

def main() -> None:
    """
    Demonstrates how to discover available agentic providers, validate an Anthropic
    execution policy, run a simple code modification task, and detect control tokens
    from the output.
    """
    # Create output directory for temporary run files as requested
    output_dir = Path("./output")
    output_dir.mkdir(exist_ok=True)

    # 1. Inspect configured and available providers
    console.print("[bold]1. Checking Agent Preferences & Availability[/bold]")
    provider_prefs = get_agent_provider_preference()
    available_agents = get_available_agents()

    console.print(f"  Configured provider preference order: {provider_prefs}")
    console.print(f"  Available local agents (CLI + Auth present): {available_agents}")

    # Check for Claude CLI/Auth for this example
    if "anthropic" not in available_agents:
        console.print("\n[yellow]Anthropic (Claude CLI) is not available or not logged in.[/yellow]")
        console.print("Please set up Claude Code (`claude auth login`) to run the execution part of this example.")
        sys.exit(0)

    # 2. Build and Validate a Claude Execution Policy
    console.print("\n[bold]2. Validating Claude Policy Contract[/bold]")
    # This restricts what tools Claude can run and audits modifications post-run
    raw_policy = {
        "allowedTools": "Read,Write",
        "addDirs": [str(output_dir.resolve())],
        "writableRoots": [str(output_dir.resolve())],
        "readOnlyRoots": [],
        "noSessionPersistence": True,
        "outputFormat": "json"
    }

    try:
        validated_policy = validate_claude_policy(raw_policy, interactive=False)
        console.print("  Policy validated successfully!")
    except Exception as e:
        console.print(f"  [red]Policy validation failed: {e}[/red]")
        sys.exit(0)

    # 3. Execute an Agentic Task
    console.print("\n[bold]3. Running Agentic Task[/bold]")
    instruction = (
        f"Create a file named 'hello.py' inside the directory '{output_dir}' "
        "containing a simple hello world print statement. "
        "Once done, write the token 'ALL_TESTS_PASS' to your output response."
    )

    console.print(f"  Instruction: {instruction}")
    console.print("  Executing... (this may take up to a minute depending on network)")

    # Execute the task
    result: AgenticTaskResult = run_agentic_task(
        instruction=instruction,
        cwd=Path("."),
        label="example_hello_world",
        claude_policy=validated_policy,
        verbose=False,
        quiet=True
    )

    # Unpack AgenticTaskResult
    success = result.success
    output_text = result.output_text
    cost_usd = result.cost_usd
    provider_used = result.provider
    changed_files = result.changed_files

    console.print(f"  Run Success Status: {success}")
    console.print(f"  Provider Used: {provider_used}")
    console.print(f"  Cost Incurred: ${cost_usd:.5f} USD")
    console.print(f"  Files modified/created: {changed_files}")
    console.print(f"  Raw Response Output Preview:\n---\n{output_text[:300]}\n---")

    # 4. Parse output for Control Tokens
    console.print("\n[bold]4. Detecting Control Tokens[/bold]")
    match = detect_control_token(output_text, "ALL_TESTS_PASS")
    if match:
        console.print(f"  [green]✓ Detected control token[/green] via tier: [bold]{match.tier}[/bold]")
    else:
        console.print("  [red]✗ Control token 'ALL_TESTS_PASS' not found in response.[/red]")


def example_post_pr_comment():
    """Demonstrate the PR comment helper used by CI validation."""
    with patch("pdd.agentic_common.shutil.which", return_value="/usr/bin/gh"), \
         patch("pdd.agentic_common.subprocess.run") as mock_run:
        mock_run.return_value = subprocess.CompletedProcess(
            args=["gh"],
            returncode=0,
            stdout="",
            stderr="",
        )
        posted = post_pr_comment(
            repo_owner="example-owner",
            repo_name="example-repo",
            pr_number=42,
            body="CI validation exhausted retries; lint is still failing.",
            cwd=Path.cwd(),
        )

    console.print(f"PR comment posted: {posted}")


if __name__ == "__main__":
    main()
