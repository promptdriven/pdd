"""
This module provides the agentic fallback functionality for the 'fix' command.
When the standard fix process fails, this module invokes a CLI agent
to attempt a fix with a broader, project-wide context.
"""
import subprocess
from pathlib import Path
from typing import Tuple, List, Dict
import os
from rich.console import Console
from .llm_invoke import _load_model_data

console = Console()

# Define the preference order for agent providers
AGENT_PROVIDER_PREFERENCE = ["anthropic", "google", "openai"]

def get_agent_command(provider: str, instruction_file: Path) -> List[str]:
    """Constructs the shell command for a given agent provider."""
    provider = provider.lower()
    # These commands are based on the conventions in spec.py
    if provider == "anthropic":
        return ["claude", "sh", "-c", f"/implement {instruction_file.resolve()}"]
    elif provider == "google":
        return ["gemini", "implement", str(instruction_file.resolve())]
    elif provider == "openai":
        return ["codex", "implement", str(instruction_file.resolve())]
    return []

def find_llm_csv_path() -> Path | None:
    """Finds the llm_model.csv file in standard locations."""
    home_path = Path.home() / ".pdd" / "llm_model.csv"
    project_path = Path.cwd() / ".pdd" / "llm_model.csv"
    if home_path.is_file():
        return home_path
    if project_path.is_file():
        return project_path
    return None

def run_agentic_fix(
    prompt_file: str,
    code_file: str,
    unit_test_file: str,
    error_log_file: str,
) -> Tuple[bool, str]:
    """
    Invokes a CLI agent to perform a project-wide fix by trying available agents in sequence.
    """
    console.print("[bold yellow]Standard fix failed. Initiating agentic fallback...[/bold yellow]")

    try:
        # 1. Load model data to find configured API keys
        csv_path = find_llm_csv_path()
        model_df = _load_model_data(csv_path)

        # 2. Determine available agents based on set environment variables
        available_agents = []
        checked_providers = set()
        for provider in AGENT_PROVIDER_PREFERENCE:
            provider_df = model_df[model_df['provider'].str.lower() == provider]
            if not provider_df.empty:
                api_key_name = provider_df.iloc[0]['api_key']
                if api_key_name and os.getenv(api_key_name):
                    if provider not in checked_providers:
                        available_agents.append(provider)
                        checked_providers.add(provider)
        
        if not available_agents:
            return False, "No configured agent API keys found in environment for providers (anthropic, google, openai)."

        console.print(f"[cyan]Available agents found: {', '.join(available_agents)}[/cyan]")

        # 3. Construct the instruction prompt for the agent
        prompt_content = Path(prompt_file).read_text(encoding="utf-8")
        code_content = Path(code_file).read_text(encoding="utf-8")
        test_content = Path(unit_test_file).read_text(encoding="utf-8")
        error_content = Path(error_log_file).read_text(encoding="utf-8")

        instructions = f"""
The code in '{code_file}' has a bug causing tests in '{unit_test_file}' to fail.
The error log is in '{error_log_file}'.

Original prompt:
---
{prompt_content}
---
Buggy code:
---
{code_content}
---
Failing tests:
---
{test_content}
---
Error log:
---
{error_content}
---
Your task is to fix the bug in '{code_file}' so the tests pass. You have full filesystem access.
"""
        instruction_file = Path("agentic_fix_instructions.txt")
        instruction_file.write_text(instructions, encoding="utf-8")

        # 4. Try agents in order of preference
        for agent_provider in available_agents:
            agent_command = get_agent_command(agent_provider, instruction_file)
            if not agent_command:
                continue

            console.print(f"[cyan]Attempting fix with {agent_provider.capitalize()} agent...[/cyan]")
            console.print(f"Executing: {' '.join(agent_command)}")

            result = subprocess.run(
                agent_command,
                capture_output=True,
                text=True,
                check=False
            )

            if result.returncode == 0:
                console.print(f"[bold green]{agent_provider.capitalize()} agent completed successfully.[/bold green]")
                instruction_file.unlink()
                return True, f"Agentic fix successful with {agent_provider.capitalize()}."
            else:
                console.print(f"[yellow]{agent_provider.capitalize()} agent failed. Trying next available agent...[/yellow]")
                console.print(f"[red]Stderr: {result.stderr}[/red]")

        # 5. If all agents failed
        instruction_file.unlink()
        return False, "All available agents failed to fix the issue."

    except FileNotFoundError as e:
        # This can happen if the CSV is not found or if the agent command (e.g., 'claude') is not in PATH
        error_msg = f"A required file or command was not found: {e}. Is the agent CLI installed and in your PATH?"
        console.print(f"[bold red]Error:[/bold red] {error_msg}")
        if 'instruction_file' in locals() and instruction_file.exists():
            instruction_file.unlink()
        return False, error_msg
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred during agentic fix:[/bold red] {e}")
        if 'instruction_file' in locals() and instruction_file.exists():
            instruction_file.unlink()
        return False, str(e)