from __future__ import annotations

import os
import sys
from pathlib import Path

# Add the project root to sys.path to allow importing the pdd package
# This assumes the script is located in pdd/context/ relative to the package root
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.agentic_common import get_available_agents, run_agentic_task, STEP_TIMEOUTS


def main() -> None:
    """
    Demonstrates how to use the agentic_common module to:
    1. Discover available agent providers (Claude, Gemini, Codex).
    2. Run a headless agentic task to create a file.
    3. Parse the results including cost and provider used.
    4. Use step-specific timeouts for orchestrated workflows.
    """
    
    # 1. Setup the environment
    # We will use a local './output' directory as the agent's working directory (cwd).
    # The agent will have permission to read/write files in this directory.
    output_dir = Path("./output")
    output_dir.mkdir(exist_ok=True)
    
    print(f"Agent working directory: {output_dir.resolve()}")

    # 2. Check availability
    # get_available_agents() checks if the CLI tool is on PATH and if API keys are set.
    agents = get_available_agents()
    print(f"Available agents: {agents}")

    if not agents:
        print("Warning: No agents detected. Ensure CLI tools (claude, gemini, codex) are installed and API keys are set.")
        print("The run_agentic_task call below will fail gracefully.")

    # 3. Define the task
    # The instruction is natural language. We ask the agent to write a specific Python script.
    instruction = (
        "Create a file named 'generated_math.py'. "
        "Inside it, write a Python function 'calculate_factorial(n)' that returns the factorial of n. "
        "Add a main block that prints the factorial of 5."
    )

    print(f"\n--- Running Task: {instruction} ---")

    # 4. Run the agentic task
    # - cwd: The directory where the agent operates.
    # - verbose: Prints debug logs (useful to see CLI commands).
    # - label: A prefix for logs to identify this specific task.
    success, output_message, cost, provider_used = run_agentic_task(
        instruction=instruction,
        cwd=output_dir,
        verbose=True,
        quiet=False,
        label="demo"
    )

    # 5. Inspect Results
    print("\n--- Execution Results ---")
    print(f"Success       : {success}")
    print(f"Provider Used : {provider_used if provider_used else 'None'}")
    print(f"Estimated Cost: ${cost:.6f}")
    print(f"Agent Output  : {output_message}")

    # 6. Verify the side effects (File Creation)
    if success:
        target_file = output_dir / "generated_math.py"
        if target_file.exists():
            print(f"\n[Verification] File '{target_file.name}' was created successfully.")
            content = target_file.read_text(encoding="utf-8")
            print("File Content:")
            print("-" * 40)
            print(content)
            print("-" * 40)
        else:
            print(f"\n[Verification] Task succeeded, but file '{target_file.name}' was not found.")

    # 7. Demonstrate STEP_TIMEOUTS usage (Issue #261)
    # When orchestrating multi-step workflows, use step-specific timeouts:
    print("\n--- Step Timeouts (for orchestrated workflows) ---")
    print(f"STEP_TIMEOUTS: {STEP_TIMEOUTS}")
    # Example: For step 7 (complex generation), use a longer timeout:
    # success, output, cost, provider = run_agentic_task(
    #     instruction="Generate comprehensive tests",
    #     cwd=output_dir,
    #     timeout=STEP_TIMEOUTS.get(7),  # 1000 seconds for complex steps
    # )


if __name__ == "__main__":
    main()