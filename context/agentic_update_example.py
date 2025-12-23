from __future__ import annotations

import sys
import os
from pathlib import Path

# Add the project root to sys.path to allow importing the pdd package
# This assumes the script is located in pdd/context/ relative to the package root
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.agentic_update import run_agentic_update


def main() -> None:
    """
    Demonstrates how to use run_agentic_update to update a prompt file.
    
    This utility:
    1. Identifies the prompt, code, and test files.
    2. Constructs a task for an AI agent (Claude, Gemini, etc.) to read the code
       and update the prompt to match the code's current state.
    3. Executes the agent and reports costs and changes.
    """
    
    # 1. Setup the environment
    # We will use a local './output' directory for our example files.
    output_dir = Path("./output")
    output_dir.mkdir(exist_ok=True)
    
    print(f"Working directory: {output_dir.resolve()}")

    # 2. Create dummy files to simulate a development scenario
    # Scenario: The code has been updated (added 'subtract' function), 
    # but the prompt only knows about 'add'. We want the agent to update the prompt.
    
    prompt_path = output_dir / "math_module.prompt"
    code_path = output_dir / "math_module.py"
    test_path = output_dir / "test_math_module.py"

    # Initial Prompt (outdated)
    prompt_content = (
        "% You are a Python math expert.\n"
        "% Requirements\n"
        "1. Create a function `add(a, b)` that returns the sum.\n"
    )
    prompt_path.write_text(prompt_content, encoding="utf-8")

    # Current Code (has new features)
    code_content = (
        "def add(a, b):\n"
        "    return a + b\n\n"
        "def subtract(a, b):\n"
        "    return a - b\n"
    )
    code_path.write_text(code_content, encoding="utf-8")

    # Tests (verifies both)
    test_content = (
        "from math_module import add, subtract\n\n"
        "def test_add():\n"
        "    assert add(1, 2) == 3\n\n"
        "def test_subtract():\n"
        "    assert subtract(5, 3) == 2\n"
    )
    test_path.write_text(test_content, encoding="utf-8")

    print(f"Created files in {output_dir}")

    # 3. Run the Agentic Update
    # This function will:
    # - Auto-discover tests (since we named them test_math_module.py)
    # - Load the 'agentic_update_LLM' template
    # - Call the available CLI agent to update 'math_module.prompt'
    
    print("\n--- Starting Agentic Update ---")
    print("Goal: Update 'math_module.prompt' to reflect changes in 'math_module.py'")

    success, message, cost, model_used, changed_files = run_agentic_update(
        prompt_file=str(prompt_path),
        code_file=str(code_path),
        # test_files=None,  # Auto-discovery is enabled by default
        verbose=True,       # Print agent logs to console
        quiet=False         # Do not suppress summary output
    )

    # 4. Inspect Results
    print("\n--- Update Results ---")
    print(f"Success       : {success}")
    print(f"Message       : {message}")
    print(f"Cost          : ${cost:.6f}")
    print(f"Model Used    : {model_used}")
    print(f"Changed Files : {changed_files}")

    if success:
        print("\n[Verification] Prompt file was updated.")
        new_prompt = prompt_path.read_text(encoding="utf-8")
        print("-" * 40)
        print(new_prompt)
        print("-" * 40)
    else:
        print("\n[Verification] Prompt file was NOT updated (or agent failed).")
        # This might happen if no agent CLI (claude, gemini) is installed/configured.


if __name__ == "__main__":
    main()