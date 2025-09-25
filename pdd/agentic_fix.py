"""
This module provides the agentic fallback functionality for the 'fix' command.
When the standard fix process fails, this module invokes a CLI agent
to attempt a fix with a broader, project-wide context.
"""
import subprocess
from pathlib import Path
from typing import Tuple

from rich.console import Console

console = Console()

def run_agentic_fix(
    prompt_file: str,
    code_file: str,
    unit_test_file: str,
    error_log_file: str,
) -> Tuple[bool, str]:
    """
    Invokes a CLI agent to perform a project-wide fix.

    This function constructs a detailed instruction prompt and uses a shell
    command to trigger an agent (like the one from spec.py's /implement)
    to analyze and fix the bug.

    Args:
        prompt_file: Path to the original prompt file.
        code_file: Path to the code file with the bug.
        unit_test_file: Path to the unit test file that fails.
        error_log_file: Path to the file containing the error logs.

    Returns:
        A tuple containing:
        - bool: True if the agentic fix was successful, False otherwise.
        - str: A message describing the outcome.
    """
    console.print("[bold yellow]Standard fix failed. Initiating agentic fallback...[/bold yellow]")

    try:
        # 1. Read all relevant file contents
        prompt_content = Path(prompt_file).read_text(encoding="utf-8")
        code_content = Path(code_file).read_text(encoding="utf-8")
        test_content = Path(unit_test_file).read_text(encoding="utf-8")
        error_content = Path(error_log_file).read_text(encoding="utf-8")

        # 2. Construct the instruction prompt for the agent
        instructions = f"""
The following code in '{code_file}' has a bug.
The bug is causing the tests in '{unit_test_file}' to fail.
The error log is in '{error_log_file}'.

Original prompt that generated the code:
---
{prompt_content}
---

Current code with the bug:
---
{code_content}
---

Failing unit tests:
---
{test_content}
---

Error log:
---
{error_content}
---

Your task is to analyze the entire project context, fix the bug in '{code_file}',
and ensure that the tests in '{unit_test_file}' pass.
You have access to the entire filesystem to understand the project structure and dependencies.
"""
        instruction_file = Path("agentic_fix_instructions.txt")
        instruction_file.write_text(instructions, encoding="utf-8")

        # 3. Construct and execute the agent command
        # This command mimics the behavior of the /implement slash command
        # from spec.py, using a file for the detailed instructions.
        agent_command = [
            "claude",  # Assuming 'claude' is the command for the agent
            "sh",
            "-c",
            f"/implement {instruction_file.resolve()}"
        ]

        console.print(f"[cyan]Executing agent command: {" ".join(agent_command)}[/cyan]")

        result = subprocess.run(
            agent_command,
            capture_output=True,
            text=True,
            check=False  # We'll check the return code manually
        )

        # 4. Clean up the instruction file
        instruction_file.unlink()

        # 5. Process the result
        if result.returncode == 0:
            console.print("[bold green]Agentic fix completed successfully.[/bold green]")
            return True, "Agentic fix successful."
        else:
            error_message = f"Agentic fix failed with return code {result.returncode}.\n"
            error_message += f"Stderr: {result.stderr}\n"
            error_message += f"Stdout: {result.stdout}"
            console.print(f"[bold red]{error_message}[/bold red]")
            return False, error_message

    except FileNotFoundError:
        error_msg = "Agent command not found. Is the 'claude' CLI agent installed and in your PATH?"
        console.print(f"[bold red]Error:[/bold red] {error_msg}")
        return False, error_msg
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred during agentic fix:[/bold red] {e}")
        return False, str(e)
