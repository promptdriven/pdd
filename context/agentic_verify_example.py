from __future__ import annotations

import json
import os
import sys
import time
from pathlib import Path
from unittest.mock import patch

# -----------------------------------------------------------------------------
# Path Setup
# -----------------------------------------------------------------------------
# Ensure the 'pdd' package is importable.
# We assume PDD_PATH is set, or we calculate it relative to this script.
pdd_path = os.environ.get("PDD_PATH")
if not pdd_path:
    # Fallback: assume this script is in pdd/context/ and package root is pdd/
    pdd_path = str(Path(__file__).resolve().parent.parent)

if pdd_path not in sys.path:
    sys.path.append(pdd_path)

# Import the module to be demonstrated
from pdd.agentic_verify import run_agentic_verify

# -----------------------------------------------------------------------------
# Helper Functions
# -----------------------------------------------------------------------------

def setup_environment(output_dir: Path) -> tuple[Path, Path, Path, Path]:
    """Creates dummy files required for the verification process."""
    output_dir.mkdir(parents=True, exist_ok=True)

    # 1. Prompt File (The Specification)
    prompt_file = output_dir / "spec.md"
    prompt_file.write_text(
        "# Calculator Spec\nCreate a function add(a, b) that returns a + b.", 
        encoding="utf-8"
    )

    # 2. Code File (The Implementation - initially broken)
    code_file = output_dir / "calculator.py"
    code_file.write_text(
        "def add(a, b):\n    return a - b  # Bug: subtraction instead of addition", 
        encoding="utf-8"
    )

    # 3. Program File (The Driver/Test)
    program_file = output_dir / "driver.py"
    program_file.write_text(
        "from calculator import add\n\nif add(2, 2) != 4:\n    raise Exception('Math failed')", 
        encoding="utf-8"
    )

    # 4. Verification Log (History of previous failures)
    log_file = output_dir / "verification_history.log"
    log_file.write_text(
        "Attempt 1: LLM tried to fix indentation.\nAttempt 2: LLM tried to rename variables.", 
        encoding="utf-8"
    )

    return prompt_file, code_file, program_file, log_file

def mock_agent_behavior(instruction: str, cwd: Path, **kwargs) -> tuple[bool, str, float, str]:
    """
    Simulates the behavior of an agentic CLI tool.
    It modifies the code file to 'fix' the bug and returns a JSON response.
    """
    print("\n[Mock Agent] Received instruction. Analyzing...")
    
    # Simulate the agent fixing the file
    code_file = cwd / "calculator.py"
    if code_file.exists():
        print(f"[Mock Agent] Fixing bug in {code_file.name}...")
        # Fix the bug: change subtraction to addition
        code_file.write_text(
            "def add(a, b):\n    return a + b  # Fixed: addition", 
            encoding="utf-8"
        )
        # Update mtime to ensure change detection works
        os.utime(code_file, None)
    
    # Construct the JSON response the agent is expected to return
    response_data = {
        "success": True,
        "message": "I identified a logic error in calculator.py where subtraction was used instead of addition. I have corrected it.",
        "cost": 0.015,
        "model": "mock-gpt-4",
        "changed_files": ["calculator.py"]
    }
    
    return True, json.dumps(response_data), 0.015, "mock-provider"

# -----------------------------------------------------------------------------
# Main Execution
# -----------------------------------------------------------------------------

def main():
    # Define working directory for this example
    output_dir = Path("./output")
    
    # Setup dummy files
    prompt_file, code_file, program_file, log_file = setup_environment(output_dir)
    
    print(f"Files created in: {output_dir.resolve()}")
    print("-" * 50)

    # We mock the internal dependencies of pdd.agentic_verify to make this example 
    # runnable without actual API keys or external CLI tools.
    # 1. Mock load_prompt_template to return a dummy template string.
    # 2. Mock run_agentic_task to simulate the agent fixing the code.
    with patch("pdd.agentic_verify.load_prompt_template", return_value="Instructions: {prompt_path}"), \
         patch("pdd.agentic_verify.run_agentic_task", side_effect=mock_agent_behavior):

        print("Running Agentic Verify (Explore Mode)...")
        
        # Call the function
        success, message, cost, model, changed_files = run_agentic_verify(
            prompt_file=prompt_file,
            code_file=code_file,
            program_file=program_file,
            verification_log_file=log_file,
            verbose=True,
            quiet=False
        )

    # -------------------------------------------------------------------------
    # Output Results
    # -------------------------------------------------------------------------
    print("-" * 50)
    print("Execution Results:")
    print(f"Success       : {success}")
    print(f"Model Used    : {model}")
    print(f"Cost          : ${cost:.4f}")
    print(f"Changed Files : {changed_files}")
    print(f"Message       : {message}")
    
    # Verify the file was actually changed by our mock
    print("-" * 50)
    print("Content of calculator.py after verification:")
    print(code_file.read_text())

if __name__ == "__main__":
    main()