from __future__ import annotations

import os
import sys
from pathlib import Path
from pdd.agentic_verify import run_agentic_verify

def main() -> None:
    """
    Demonstrates how to use the run_agentic_verify function to perform agentic repair
    and verification exploration when standard non-agentic fixing fails.

    Input Parameters for run_agentic_verify:
        - prompt_file (Path): Path to the markdown prompt specification.
        - code_file (Path): Path to the generated code module.
        - program_file (Path): Path to the driver program validating the code.
        - verification_log_file (Path): Path containing logs of previous failures.
        - verbose (bool): Enable rich verbose diagnostics.
        - quiet (bool): Suppress standard output logs.
        - deadline (float | None): Explicit epoch timestamp deadline for execution.

    Returns:
        - success (bool): True if verification succeeded.
        - message (str): Explanation or raw tool execution output.
        - cost (float): Incurred LLM invocation cost in USD.
        - model (str): Name of the model provider used during execution.
        - changed_files (list[str]): List of project files modified during exploration.
    """
    # 1. Ensure required environment variables are set
    api_key_check = os.environ.get("ANTHROPIC_API_KEY") or os.environ.get("OPENAI_API_KEY")
    if not api_key_check:
        print("Neither ANTHROPIC_API_KEY nor OPENAI_API_KEY is configured. Skipping agentic run.")
        sys.exit(0)

    # 2. Setup mock files representing a verification failure scenario
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)

    prompt_file = output_dir / "prompt_spec.txt"
    code_file = output_dir / "math_utils.py"
    program_file = output_dir / "verify_math.py"
    verification_log_file = output_dir / "failures.log"

    # Populate files with a subtle bug (division by zero / logic mismatch)
    prompt_file.write_text("Implement a safe division function that returns 0.0 when dividing by zero.", encoding="utf-8")
    code_file.write_text("def divide(a, b):\n    return a / b\n", encoding="utf-8")
    program_file.write_text("from math_utils import divide\nassert divide(10, 0) == 0.0\n", encoding="utf-8")
    verification_log_file.write_text("ZeroDivisionError: division by zero in verify_math.py line 2", encoding="utf-8")

    print("--- Starting Agentic Verification Fallback Demo ---")
    
    # 3. Trigger the agentic verification pipeline
    success, message, cost, model, changed_files = run_agentic_verify(
        prompt_file=prompt_file,
        code_file=code_file,
        program_file=program_file,
        verification_log_file=verification_log_file,
        verbose=True,
        quiet=False
    )

    # 4. Handle results
    print("\n--- Verification Run Complete ---")
    print(f"Success Claimed: {success}")
    print(f"Agent Output: {message}")
    print(f"Associated Cost: ${cost:.5f} USD")
    print(f"Model Provider: {model}")
    print(f"Modified Files: {changed_files}")

if __name__ == "__main__":
    main()