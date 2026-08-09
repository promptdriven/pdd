from __future__ import annotations

import os
import sys
from pathlib import Path
from rich.console import Console

# Ensure the project root is in the system path for importing pdd
project_root = Path(__file__).resolve().parent.parent
if str(project_root) not in sys.path:
    sys.path.append(str(project_root))

from pdd.agentic_test_generate import run_agentic_test_generate

console = Console()

def main() -> None:
    """
    Demonstrates how to use the agentic test generation module to automatically
    discover test frameworks, generate, and verify tests for a non-Python codebase.

    Input Parameters:
    -----------------
    - prompt_file (Path): Path to the specification file detailing what tests to generate.
    - code_file (Path): Path to the source code file to test.
    - output_test_file (Path): Target path where the test file should be written.
    - verbose (bool): Enable verbose logging (default: False).
    - quiet (bool): Suppress standard output (default: False).
    - repair_directive (str | None): Optional repair-loop instruction when retrying to
                                    prevent aggressive test churn / deletions.

    Output (TestResult):
    --------------------
    - content (str): The contents of the generated test file.
    - cost (float): Estimated LLM cost in USD.
    - model (str): Name of the agent provider/model used.
    - agentic_success (bool): Whether the agent succeeded in generating and verifying the tests.
    - error_message (str): Set on failure; otherwise an empty string.
    """
    console.print("[bold green]=== Agentic Test Generation Example ===[/bold green]")

    # 1. Environment and Key Validation
    # Agentic CLI providers require API keys (e.g., Anthropic or OpenAI)
    api_key = os.environ.get("ANTHROPIC_API_KEY") or os.environ.get("OPENAI_API_KEY")
    if not api_key:
        console.print(
            "[yellow]Warning: ANTHROPIC_API_KEY or OPENAI_API_KEY not found in environment.\n"
            "An active API key and an installed agentic CLI (like Claude CLI) are required\n"
            "to execute the full agentic loop. Skipping execution.[/yellow]"
        )
        sys.exit(0)

    # 2. Setup Work Directory and Target Files
    # We will simulate a TypeScript test generation scenario inside the './output' directory.
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)

    code_file = output_dir / "math_utils.ts"
    prompt_file = output_dir / "math_utils_spec.txt"
    output_test_file = output_dir / "math_utils.test.ts"

    # Create a dummy TypeScript file to generate tests for
    code_file.write_text(
        """export function add(a: number, b: number): number {
  return a + b;
}

export function subtract(a: number, b: number): number {
  return a - b;
}""",
        encoding="utf-8"
    )

    # Create a prompt specifying the test expectations
    prompt_file.write_text(
        """Generate unit tests for math_utils.ts.
Ensure you cover both addition and subtraction, including negative numbers and zero.
Use a standard testing framework like Jest if available.""",
        encoding="utf-8"
    )

    console.print(f"[blue]Code file created:[/blue] {code_file}")

    # 3. Run Agentic Test Generator
    console.print("[blue]Starting agentic execution... This may take a moment.[/blue]")
    
    # Optional repair directive to ensure existing coverage is maintained
    # (often passed down from a retry orchestration framework)
    repair_directive = (
        "Add new tests without altering or deleting existing test structures."
    )

    result = run_agentic_test_generate(
        prompt_file=prompt_file,
        code_file=code_file,
        output_test_file=output_test_file,
        verbose=True,
        quiet=False,
        repair_directive=repair_directive
    )

    # 4. Process and Display Results
    console.print("\n[bold green]=== Agentic Test Run Completed ===[/bold green]")
    console.print(f"[bold]Success status:[/bold] {result.agentic_success}")
    console.print(f"[bold]Model / Agent:[/bold] {result.model}")
    console.print(f"[bold]Estimated Cost:[/bold] ${result.cost:.5f} USD")

    if result.agentic_success:
        console.print("[bold green]Generated Test Code:[/bold green]")
        console.print(f"[dim]{result.content}[/dim]")
    else:
        console.print(f"[bold red]Error/Message:[/bold red] {result.error_message}")

if __name__ == "__main__":
    main()