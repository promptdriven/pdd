from __future__ import annotations

import os
import sys
from pathlib import Path
from rich.console import Console

# Ensure we can import from the pdd package
sys.path.append(str(Path(__file__).resolve().parent.parent))

from pdd.agentic_common import (
    get_agent_provider_preference,
    get_available_agents,
    run_agentic_task,
    detect_control_token,
    substitute_template_variables,
    validate_claude_policy,
)

console = Console()


def demonstrate_template_substitution() -> None:
    """
    Demonstrates safe template variable substitution.
    
    Template substitution replaces placeholders without raising KeyError for unknown keys,
    which is essential when processing raw LLM outputs containing nested curly braces (like JSON).
    """
    console.print("[bold ceaser]=== 1. Template Variable Substitution ===[/bold ceaser]")
    
    template = "Fixing bug in {filename}. Expected ELO: {elo}. Custom JSON format: {{'key': 'val'}}"
    context = {"filename": "src/main.py", "elo": 1250}
    
    # Substitutes variables safely
    rendered = substitute_template_variables(template, context)
    console.print(f"Template:  [dim]{template}[/dim]")
    console.print(f"Context:   [dim]{context}[/dim]")
    console.print(f"Rendered:  [green]{rendered}[/green]\n")


def demonstrate_control_token_detection() -> None:
    """
    Demonstrates multi-tier control token detection from LLM outputs.
    
    This function searches the tail of LLM responses using exact substring,
    case-insensitive, and semantic regex checks to find structural signals.
    """
    console.print("[bold ceaser]=== 2. Control Token Detection ===[/bold ceaser]")
    
    # Example LLM output containing a paraphrased pass condition at the end
    llm_output = (
        "Analyzing codebase...\n"
        "Running test suite...\n"
        "All 42 tests passed successfully! Done."
    )
    
    # Search for 'ALL_TESTS_PASS'
    match = detect_control_token(llm_output, "ALL_TESTS_PASS")
    
    if match:
        console.print(f"Detected token: [green]{match.token}[/green]")
        console.print(f"Detection tier: [cyan]{match.tier}[/cyan]")
        if match.pattern:
            console.print(f"Matched regex pattern: [dim]{match.pattern}[/dim]")
    else:
        console.print("[yellow]No control token matched.[/yellow]")
    console.print()


def demonstrate_agent_discovery_and_policy() -> None:
    """
    Demonstrates how to query configured agents, validate policies, and prepare task parameters.
    """
    console.print("[bold ceaser]=== 3. Agent Discovery & Policy Validation ===[/bold ceaser]")
    
    # Get prioritized preference and check currently available agents
    preferences = get_agent_provider_preference()
    available = get_available_agents()
    
    console.print(f"Configured provider preference order: [cyan]{preferences}[/cyan]")
    console.print(f"Currently available agents on this machine: [green]{available}[/green]")
    
    # Define and validate a Claude CLI policy contract
    # This forces limits on tools and limits writes to specified roots
    raw_policy = {
        "allowedTools": "Bash,Read,Write",
        "writableRoots": ["./output"],
        "readOnlyRoots": ["/etc"],
        "noSessionPersistence": False,
        "outputFormat": "json",
    }
    
    try:
        validated_policy = validate_claude_policy(raw_policy, interactive=False)
        console.print("[green]Successfully validated Claude Policy contract:[/green]")
        console.print(validated_policy)
    except Exception as exc:
        console.print(f"[red]Policy validation failed: {exc}[/red]")
    console.print()


def main() -> None:
    """
    Main execution demonstrating the high-level capabilities of agentic_common.
    All files are read/written inside the local './output' directory.
    """
    # Ensure output directory exists
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # 1. Run basic utility demonstrations
    demonstrate_template_substitution()
    demonstrate_control_token_detection()
    demonstrate_agent_discovery_and_policy() 

    # 2. Setup mock environment and run a safe task if an agent is configured
    console.print("[bold ceaser]=== 4. Running an Agentic Task (Safety Demonstration) ===[/bold ceaser]")
    
    available = get_available_agents()
    if not available:
        console.print("[yellow]No agent CLI or keys configured. Skipping live task execution demonstration.[/yellow]")
        return

    # Ensure we use anthropic/claude if configured, or fallback to whatever is available
    provider = available[0]
    console.print(f"Using available provider '[green]{provider}[/green]' to run a simple, sandboxed audit task...")
    
    # Write a dummy target file to audit inside the safe output directory
    test_file = output_dir / "audit_target.txt"
    test_file.write_text("PDD agentic platform validation target file.", encoding="utf-8")
    
    instruction = f"Please inspect the contents of {test_file.name} inside the output directory and write a summary file next to it."
    
    # Execute the agentic task safely in the current directory.
    # Restrict execution limits to prevent infinite spending loops.
    result = run_agentic_task(
        instruction=instruction,
        cwd=Path("."),
        verbose=True,
        label="demo_audit_task",
        timeout=120.0,  # 2-minute hard cap
        max_retries=1,
    )
    
    console.print(f"\n[bold]Task Execution Result (Success: {result.success})[/bold]")
    console.print(f"Provider used:  [cyan]{result.provider}[/cyan]")
    console.print(f"Execution cost: [green]${result.cost_usd:.4f}[/green]")
    if result.changed_files:
        console.print(f"Changed files:  [yellow]{result.changed_files}[/yellow]")


if __name__ == "__main__":
    main()