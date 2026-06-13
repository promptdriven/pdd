from __future__ import annotations

import os
import sys
from pathlib import Path
from typing import Optional
from rich.console import Console

# Import the shared agentic orchestration infrastructure
from pdd.agentic_common import (
    get_agent_provider_preference,
    get_available_agents,
    run_agentic_task,
    validate_claude_policy,
    detect_control_token,
    substitute_template_variables,
    AgenticTaskResult,
    TokenMatch,
)

# Initialize Rich console for beautiful output formatting
console = Console()


def run_agentic_workflow() -> None:
    """
    Demonstrates a complete, safe, and non-interactive agentic workflow.
    
    This workflow:
    1. Checks the user's preferred and currently available agent providers.
    2. Dynamically builds a parameterized prompt template.
    3. Configures and validates a security policy restricting agent modifications.
    4. Executes the agentic task to write a Python file within our sandbox.
    5. Audits the result, outputs token consumption, and detects control tokens.
    """
    console.print("[bold cyan]Starting PDD Agentic Workflow Example[/bold cyan]\n")

    # Ensure all sandbox work and output is contained within the local output directory
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)

    # 1. Discover Provider Preferences and Availabilities
    pref_providers: list[str] = get_agent_provider_preference()
    available_providers: list[str] = get_available_agents()

    console.print(f"[bold]Configured Preference Order:[/bold] {pref_providers}")
    console.print(f"[bold]Detected Available CLIs:[/bold] {available_providers}\n")

    if not available_providers:
        console.print(
            "[yellow]No agentic provider CLIs (Claude, Gemini, Codex, or OpenCode) "
            "are currently configured with active authentication.[/yellow]"
        )
        console.print("Please run [bold]pdd setup[/bold] to configure a provider first.")
        sys.exit(0)

    # 2. Variable Substitution in Prompts
    # Safely substitute variables without raising KeyError on raw JSON or unmatched braces.
    prompt_template = (
        "Create a simple math utility file named '{filename}' in the active "
        "directory. Implement a function '{func_name}(a, b)' that divides 'a' "
        "by 'b' but returns 0 if 'b' is 0 to avoid DivisionByZero. "
        "End your output with the keyword: ALL_TESTS_PASS"
    )
    
    context = {
        "filename": "math_utils.py",
        "func_name": "safe_divide",
    }
    
    instruction: str = substitute_template_variables(prompt_template, context)
    console.print(f"[bold green]Rendered Instruction:[/bold green]\n{instruction}\n")

    # 3. Create and Validate Security Policy
    # We restrict the agent's filesystem capabilities exclusively to our output directory
    claude_policy_dict = {
        "allowedTools": "Bash,Read,Write",
        "writableRoots": [str(output_dir.resolve())],
        "noSessionPersistence": True,
        "outputFormat": "json"
    }
    
    # Validates against the strict schema contract (rejects wildcards, illegal parameters)
    validated_policy = validate_claude_policy(claude_policy_dict, interactive=False)
    console.print("[bold green]Enforcing Validated Filesystem Security Policy:[/bold green]")
    console.print(validated_policy)
    console.print()

    # 4. Execute the Task via the Primary Available Agent
    primary_provider = available_providers[0]
    console.print(f"[bold yellow]Executing task using primary agent: {primary_provider}...[/bold yellow]")

    # Execute task safely. All agent file modifications will be audited against the policy.
    result: AgenticTaskResult = run_agentic_task(
        instruction=instruction,
        cwd=output_dir,
        label="generate_safe_divide",
        timeout=180.0,  # Individual step timeout limit in seconds
        max_retries=1,
        claude_policy=validated_policy if primary_provider == "anthropic" else None,
    )

    # 5. Extract Result Metadata
    # AgenticTaskResult seamlessly unpacks like a 4-item tuple for legacy code,
    # while storing structured token usage metrics and changed files as attributes.
    success, output_text, cost_usd, provider_used = result
    usage = result.usage
    changed_files = result.changed_files

    console.print(f"\n[bold]Task Success Status:[/bold] {success}")
    console.print(f"[bold]Provider Used:[/bold] {provider_used}")
    console.print(f"[bold]Task Exec Cost:[/bold] ${cost_usd:.6f}")
    console.print(f"[bold]Files Created/Modified:[/bold] {changed_files}")

    if usage:
        console.print(f"[bold]Detailed Token Accounting metrics:[/bold] {usage}")

    # 6. Parse Control Tokens from LLM output
    # Scan only the tail of the output using portable splitlines bounds to prevent false positives
    token_match: Optional[TokenMatch] = detect_control_token(output_text, "ALL_TESTS_PASS")
    if token_match:
        console.print(
            f"\n[bold green]Control Token Detected![/bold green] "
            f"Token: '{token_match.token}' (Match tier: {token_match.tier})"
        )

    # Output verification
    console.print("\n[bold green]Workflow completed successfully.[/bold green]")


if __name__ == "__main__":
    run_agentic_workflow()