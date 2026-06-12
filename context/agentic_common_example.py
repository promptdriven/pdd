from __future__ import annotations

import os
import sys
from pathlib import Path
from typing import Any, Dict, List

from rich.console import Console

# Ensure the package is importable
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.agentic_common import (
    AgenticTaskResult,
    ClaudePolicy,
    TokenMatch,
    detect_control_token,
    extract_step_report,
    get_agent_provider_preference,
    get_available_agents,
    run_agentic_task,
    validate_claude_policy,
)

console = Console()


def demonstrate_provider_discovery() -> None:
    """
    Demonstrates how to discover configured agentic CLI providers and user preferences.

    Outputs:
        Prints lists of available and preferred providers to the console.
    """
    console.print("[bold cyan]--- Discovery & Preferences ---[/bold cyan]")

    # Get preferred order from env (PDD_AGENTIC_PROVIDER) or defaults
    preferences: List[str] = get_agent_provider_preference()
    console.print(f"[green]Preferred providers:[/green] {preferences}")

    # Get providers actually available based on installed CLIs and credentials
    available: List[str] = get_available_agents()
    console.print(f"[green]Available providers on this machine:[/green] {available}")
    console.print()


def demonstrate_policy_validation() -> None:
    """
    Demonstrates how to validate and normalize security policies for Claude execution.

    Outputs:
        Prints the normalized validated policy schema.
    """
    console.print("[bold cyan]--- Claude Policy Validation ---[/bold cyan]")

    raw_policy: Dict[str, Any] = {
        "allowedTools": "Read,Write,Bash",
        "addDirs": ["./src", "./tests"],
        "writableRoots": ["./src"],
        "readOnlyRoots": ["./tests"],
        "noSessionPersistence": True,
        "outputFormat": "json",
    }

    # Validate and normalize the policy schema
    normalized_policy: ClaudePolicy = validate_claude_policy(raw_policy, interactive=False)
    console.print("[green]Validated Policy Shape:[/green]")
    console.print(normalized_policy)
    console.print()


def demonstrate_text_parsing() -> None:
    """
    Demonstrates extracting structured step reports and detecting workflow control tokens
    from raw LLM agent stdout.

    Outputs:
        Prints extracted blocks and detected control token match states.
    """
    console.print("[bold cyan]--- Output Parsing & Control Tokens ---[/bold cyan]")

    # Simulated raw output containing metadata blocks and text
    raw_llm_output = (
        "We analyzed the codebase and implemented the requested fixes.\n"
        "<step_report>\n"
        "## Fix Summary\n"
        "Modified math utility to prevent zero division errors.\n"
        "</step_report>\n"
        "All checks are green. ALL_TESTS_PASS"
    )

    # Extract step report block from tagged markup
    extracted_report: str | None = extract_step_report(raw_llm_output)
    console.print("[green]Extracted Step Report:[/green]")
    console.print(extracted_report)

    # Parse control token using exact, case-insensitive, or semantic fallback regex
    match: TokenMatch | None = detect_control_token(raw_llm_output, "ALL_TESTS_PASS")
    if match:
        console.print(
            f"[green]Detected control token:[/green] {match.token} "
            f"(Matched via [yellow]{match.tier}[/yellow] tier)"
        )
    console.print()


def demonstrate_agentic_task(output_dir: Path) -> None:
    """
    Demonstrates running an agentic CLI task in a sandboxed target directory.

    Inputs:
        output_dir: Path to the target workspace directory.

    Outputs:
        Runs the task and prints results, costs, and modified file parameters.
    """
    console.print("[bold cyan]--- Running Agentic Task ---[/bold cyan]")

    # Check if we have at least one usable agent available
    available = get_available_agents()
    if not available:
        console.print(
            "[yellow]No providers are currently available. "
            "Set ANTHROPIC_API_KEY, GOOGLE_API_KEY, or OPENAI_API_KEY "
            "to execute real tasks.[/yellow]"
        )
        return

    # Define the workspace directory for the task run
    workspace: Path = output_dir / "workspace"
    workspace.mkdir(parents=True, exist_ok=True)

    # Create a dummy file for the agent to inspect
    test_file = workspace / "todo.txt"
    test_file.write_text("Task list:\n- Fix formatting in main.py", encoding="utf-8")

    instruction = "Read the file todo.txt and tell me what the first task is."
    console.print(f"Executing Instruction: [dim]{instruction}[/dim]")

    # Run the task through the provider preference waterfall
    result: AgenticTaskResult = run_agentic_task(
        instruction=instruction,
        cwd=workspace,
        verbose=False,
        quiet=True,
        label="todo-check",
        timeout=60.0,
    )

    # Unpack AgenticTaskResult. Tuple-unpacking iteration is also supported
    console.print(f"[green]Success Status:[/green] {result.success}")
    console.print(f"[green]Output Text:[/green] {result.output_text.strip()}")
    console.print(f"[green]Cost Incurred:[/green] ${result.cost_usd:.6f}")
    console.print(f"[green]Provider Used:[/green] {result.provider}")
    if result.changed_files:
        console.print(f"[green]Changed Files:[/green] {result.changed_files}")
    console.print()


def main() -> None: 
    # Set up sandboxed output directory relative to this script
    output_dir = Path(__file__).resolve().parent / "output"
    output_dir.mkdir(parents=True, exist_ok=True)

    demonstrate_provider_discovery()
    demonstrate_policy_validation()
    demonstrate_text_parsing()
    demonstrate_agentic_task(output_dir)


if __name__ == "__main__":
    main()