import sys
import os
import json
from pathlib import Path
from unittest.mock import patch, MagicMock

# Add the project root to sys.path to allow importing the pdd package
# This assumes the script is located in pdd/context/ relative to the package root
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

from pdd.agentic_crash import run_agentic_crash


def setup_test_files(output_dir: Path):
    """Creates dummy files to simulate a crash scenario."""
    output_dir.mkdir(parents=True, exist_ok=True)

    # 1. The Prompt (Spec)
    prompt_file = output_dir / "factorial_spec.md"
    prompt_file.write_text(
        "Write a function that calculates the factorial of a number.", 
        encoding="utf-8"
    )

    # 2. The Code (Buggy implementation)
    code_file = output_dir / "math_lib.py"
    code_file.write_text(
        "def factorial(n):\n    raise NotImplementedError('Not done yet')", 
        encoding="utf-8"
    )

    # 3. The Program (The runner that crashed)
    program_file = output_dir / "run_factorial.py"
    program_file.write_text(
        "from math_lib import factorial\nprint(factorial(5))", 
        encoding="utf-8"
    )

    # 4. The Crash Log
    crash_log_file = output_dir / "crash.log"
    crash_log_file.write_text(
        "Traceback (most recent call last):\n  File 'run_factorial.py', line 2\n    raise NotImplementedError", 
        encoding="utf-8"
    )

    return prompt_file, code_file, program_file, crash_log_file


def main():
    # Define output directory for generated files
    output_dir = Path("./output")
    
    # Setup the scenario
    prompt_path, code_path, program_path, crash_log_path = setup_test_files(output_dir)

    print(f"Scenario setup in: {output_dir.resolve()}")
    print(f"Target Program: {program_path.name}")

    # We mock the dependencies to simulate a successful agentic fix without
    # needing real API keys or external tools for this example.
    
    # Mock 1: The Agentic Task Runner
    # Simulates the agent analyzing the code and returning a JSON response indicating a fix.
    mock_agent_response = json.dumps({
        "success": True,
        "message": "I implemented the factorial logic in math_lib.py.",
        "cost": 0.015,
        "model": "claude-3-5-sonnet",
        "changed_files": ["math_lib.py"]
    })

    # Mock 2: The Subprocess Runner
    # Simulates the verification step where the program runs successfully after the fix.
    mock_subprocess_result = MagicMock()
    mock_subprocess_result.returncode = 0
    mock_subprocess_result.stdout = "120"  # Factorial of 5
    mock_subprocess_result.stderr = ""

    print("\n--- Starting Agentic Crash Handler (Mocked) ---")

    # Apply patches to pdd.agentic_crash dependencies
    with patch("pdd.agentic_crash.run_agentic_task") as mock_run_agent, \
         patch("pdd.agentic_crash.get_run_command_for_file") as mock_get_cmd, \
         patch("pdd.agentic_crash.load_prompt_template") as mock_load_tmpl, \
         patch("subprocess.run") as mock_subprocess:

        # Configure mocks
        mock_run_agent.return_value = (True, mock_agent_response, 0.015, "claude-3-5-sonnet")
        mock_get_cmd.return_value = f"python3 {program_path}"
        mock_load_tmpl.return_value = "Fix the crash in {program_path} based on {prompt_path}..."
        mock_subprocess.return_value = mock_subprocess_result

        # Side effect: Actually update the file to simulate the agent's work
        # This ensures file mtime logic in the module is exercised if checked
        def agent_side_effect(*args, **kwargs):
            code_path.write_text(
                "def factorial(n):\n    return 1 if n <= 1 else n * factorial(n-1)", 
                encoding="utf-8"
            )
            return (True, mock_agent_response, 0.015, "claude-3-5-sonnet")
        
        mock_run_agent.side_effect = agent_side_effect

        # --- EXECUTE THE MODULE ---
        success, message, cost, model, changed_files = run_agentic_crash(
            prompt_file=prompt_path,
            code_file=code_path,
            program_file=program_path,
            crash_log_file=crash_log_path,
            verbose=True,  # Enable verbose logging to console
            quiet=False
        )

    # Output the results
    print("\n--- Result Summary ---")
    print(f"Success       : {success}")
    print(f"Model Used    : {model}")
    print(f"Cost          : ${cost:.4f}")
    print(f"Changed Files : {changed_files}")
    print("-" * 30)
    print(f"Message       :\n{message}")
    print("-" * 30)

    # Verify the file was actually "fixed" by our side effect
    print(f"\nContent of {code_path.name} after fix:")
    print(code_path.read_text())


if __name__ == "__main__":
    main()