from __future__ import annotations

import os
import sys
from pathlib import Path
from pdd.agentic_common import (
    get_agent_provider_preference,
    get_available_agents,
    get_agentic_capabilities,
    validate_claude_policy,
    run_agentic_task,
    detect_control_token,
    AgenticUnsupportedSemanticsError,
)
from rich.console import Console

console = Console()


def run_agentic_pipeline_demo() -> None:
    """Demonstrates discovering agents, validating policy, and executing an agentic task.

    This script runs in a completely non-interactive headless manner.
    It performs the following:
      1. Inspects the environment to see which local CLI agents are configured.
      2. Validates a security policy (restricting file modifications to specific directories).
      3. Simulates/runs a simple file-creation task using the highest-priority agent.
      4. Audits the response for control tokens.
    """
    console.print("[bold blue]=== PDD Agentic Common Infrastructure Demo ===[/bold blue]\n")

    # 1. Discover Provider Preferences and Available Agents
    # get_agent_provider_preference() returns list of providers ordered by preference (e.g., ["anthropic", "google"])
    # get_available_agents() checks local executable paths and API key existence
    preferred_providers = get_agent_provider_preference()
    available_agents = get_available_agents()

    console.print(f"Preferred provider order: [cyan]{preferred_providers}[/cyan]")
    console.print(f"Locally available CLI agents: [cyan]{available_agents}[/cyan]")

    if not available_agents:
        console.print(
            "[yellow]No agent CLI executors (claude, agy, gemini, codex, or opencode) "
            "are currently available. Check CLI installations or configure API keys "
            "to run a live task.[/yellow]"
        )
        # We will exit gracefully with 0 as no agents are available to test the execution
        sys.exit(0)

    # 2. Setup a Sandboxed Output/Working Directory
    # We will create our workspace inside the ./output directory as required
    output_dir = Path("./output").resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    # Create dummy files to mimic a git worktree or project workspace
    dummy_src = output_dir / "app.py"
    dummy_src.write_text("def hello():\n    pass\n", encoding="utf-8")

    # 3. Define and Validate a Claude Security Policy
    # This policy restricts Claude to only write files inside our designated output_dir
    raw_policy = {
        "allowedTools": "Bash,Read,Write",
        "addDirs": [str(output_dir)],
        "writableRoots": [str(output_dir)],
        "readOnlyRoots": [],
        "noSessionPersistence": True,
        "outputFormat": "json",
    }

    try:
        validated_policy = validate_claude_policy(raw_policy, interactive=False)
        console.print("\n[green]✓ Claude Policy Contract successfully validated:[/green]")
        console.print(validated_policy)
    except AgenticUnsupportedSemanticsError as exc:
        console.print(f"[red]✗ Policy validation failed: {exc}[/red]")
        sys.exit(0)

    # 4. Execute the Task via the Primary Available Agent
    # We target the first available provider that intersects with our preferences.
    target_provider = [p for p in preferred_providers if p in available_agents][0]
    console.print(
        f"\nExecuting simple task via [bold green]{target_provider}[/bold green]..."
    )

    instruction = (
        f"Modify the file {dummy_src.name} to return 'Hello World!' "
        "and print 'ALL_TESTS_PASS' when you are done."
    )

    # run_agentic_task returns an AgenticTaskResult tuple containing:
    # 0: success (bool) - True if execution was successful
    # 1: output_text (str) - Final response from the agent
    # 2: cost_usd (float) - Total cost of this step in USD
    # 3: provider (str) - The provider name used
    # 4: usage (dict) - Detailed token counts (input, output, cache-hits)
    result = run_agentic_task(
        instruction=instruction,
        cwd=output_dir,
        verbose=True,
        quiet=False,
        label="fix-hello-world-step",
        timeout=180.0,  # 3 minutes maximum runtime
        max_retries=2,
        claude_policy=validated_policy if target_provider == "anthropic" else None,
    )

    console.print("\n[bold blue]=== Execution Results ===[/bold blue]")
    console.print(f"Success: [yellow]{result.success}[/yellow]")
    console.print(f"Provider Used: [yellow]{result.provider}[/yellow]")
    console.print(f"Cost Incurred: [yellow]${result.cost_usd:.5f} USD[/yellow]")

    if result.success:
        console.print(f"Changed Files audited: [cyan]{result.changed_files}[/cyan]")
        console.print("\nAgent Output snippet:")
        console.print(f"[dim]{result.output_text[:500]}...[/dim]")

        # 5. Detect Control Tokens in the Output
        # detect_control_token parses the last 30 lines (default) of the response
        # using substring matching, case-insensitive checks, and semantic fallbacks
        token_match = detect_control_token(result.output_text, "ALL_TESTS_PASS")
        if token_match:
            console.print(
                f"\n[green]✓ Control token detected! Tier: {token_match.tier}[/green]"
            )
        else:
            console.print("\n[yellow]No control tokens were found in output.[/yellow]")
    else:
        console.print(f"\n[red]Task failed with error: {result.output_text}[/red]")


if __name__ == "__main__":
    run_agentic_pipeline_demo()