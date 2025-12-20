from __future__ import annotations

import os
import sys
from pathlib import Path

# Add the project root to sys.path to allow importing the pdd package.
# This assumes the script is located in 'pdd/context/' and the package is in 'pdd/pdd/'.
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from pdd.agentic_common import get_available_agents, run_agentic_task


def main() -> None:
    """
    Demonstrates how to use the agentic_common module to run a CLI-based LLM agent.
    """
    
    # 1. Discover available agents
    # This checks for both the CLI binary (e.g., 'claude', 'gemini') on PATH
    # and the presence of required API key environment variables.
    print("--- Agent Discovery ---")
    available_agents = get_available_agents()
    print(f"Available agents: {available_agents}")

    if not available_agents:
        print("Warning: No agents found. Ensure CLI tools are installed and API keys are set.")

    # 2. Setup the working directory
    # The agent will execute commands relative to this path.
    # We use an 'output' directory to keep generated files contained.
    base_dir = Path(os.path.dirname(__file__))
    output_dir = base_dir / "output"
    output_dir.mkdir(parents=True, exist_ok=True)
    
    print(f"\nWorking directory: {output_dir}")

    # 3. Define the instruction
    # We give the agent a task that requires file system access to demonstrate
    # the 'agentic' capabilities (reading/writing files).
    instruction = (
        "Create a Python script named 'calculate_pi.py' that estimates Pi "
        "using the Monte Carlo method with 1000 iterations. "
        "Then, run the script and save the output to 'pi_result.txt'."
    )

    print(f"\n--- Running Task ---")
    print(f"Instruction: {instruction}")

    # 4. Run the agentic task
    # - cwd: The directory where the agent operates.
    # - verbose: Enables detailed logging from the module (using rich).
    # - label: A prefix for logs to identify this specific task run.
    success, output_log, cost, provider_used = run_agentic_task(
        instruction=instruction,
        cwd=output_dir,
        verbose=True,
        quiet=False,
        label="example_run"
    )

    # 5. Process the results
    print("\n--- Execution Results ---")
    if success:
        print(f"✅ Task completed successfully by provider: '{provider_used}'")
    else:
        print(f"❌ Task failed.")
        if provider_used:
            print(f"Last attempted provider: '{provider_used}'")

    print(f"Estimated Cost: ${cost:.6f}")
    print(f"CLI Output Log (truncated): {output_log[:200]}...")

    # 6. Verify artifacts
    # Check if the agent actually created the requested files.
    script_file = output_dir / "calculate_pi.py"
    result_file = output_dir / "pi_result.txt"

    if script_file.exists():
        print(f"\n[Verification] Generated script found at: {script_file.name}")
    
    if result_file.exists():
        content = result_file.read_text().strip()
        print(f"[Verification] Result file found. Content: {content}")


if __name__ == "__main__":
    main()