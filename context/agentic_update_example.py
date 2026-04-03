from __future__ import annotations

"""
Example demonstrating how to use pdd.agentic_update.run_agentic_update.

run_agentic_update coordinates an agentic update of a prompt file using an
external CLI agent (Claude, Gemini, Codex). It:
  1. Validates that prompt and code files exist.
  2. Checks for available agent CLIs.
  3. Auto-discovers (or accepts explicit) test files.
  4. Loads the 'agentic_update_LLM' prompt template and formats it.
  5. Runs the agent via run_agentic_task.
  6. Detects changed files via mtime comparison.
  7. Returns (success, message, cost, model_used, changed_files).
     - success is True only if the prompt file was modified.
     - cost is in USD (e.g., 0.05 means $0.05).
"""

import os
import sys
import time
import tempfile
from pathlib import Path
from unittest.mock import patch, MagicMock

# Ensure project root is importable
project_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(project_root))

from pdd.agentic_update import run_agentic_update


def example_no_agents_available() -> None:
    """Show return value when no agentic CLI is available."""
    print("=" * 60)
    print("Example 1: No agents available")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        prompt = tmp_path / "module.prompt"
        code = tmp_path / "module.py"
        prompt.write_text("% Prompt content\n")
        code.write_text("def hello(): pass\n")

        # Mock get_available_agents to return empty list
        with patch("pdd.agentic_update.get_available_agents", return_value=[]):
            success, message, cost, model, changed = run_agentic_update(
                prompt_file=str(prompt),
                code_file=str(code),
                quiet=True,
            )

        print(f"  success      : {success}")        # False
        print(f"  message      : {message}")         # "No agentic CLI available"
        print(f"  cost (USD)   : {cost}")             # 0.0
        print(f"  model_used   : '{model}'")          # ""
        print(f"  changed_files: {changed}")          # []
        print()


def example_successful_update() -> None:
    """Simulate a successful prompt update where the agent modifies the prompt."""
    print("=" * 60)
    print("Example 2: Successful prompt update")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        prompt = tmp_path / "math_module.prompt"
        code = tmp_path / "math_module.py"
        test_file = tmp_path / "test_math_module.py"

        # Outdated prompt (only mentions add)
        prompt.write_text(
            "% You are a Python math expert.\n"
            "% Requirements\n"
            "1. Create a function `add(a, b)` that returns the sum.\n"
        )
        # Updated code (has add and subtract)
        code.write_text(
            "def add(a, b):\n    return a + b\n\n"
            "def subtract(a, b):\n    return a - b\n"
        )
        # Test file (tests both functions)
        test_file.write_text(
            "def test_add():\n    assert True\n\n"
            "def test_subtract():\n    assert True\n"
        )

        # Set prompt mtime in the past so the agent's touch is detectable
        old_time = time.time() - 100
        os.utime(prompt, (old_time, old_time))

        mock_template = MagicMock()
        mock_template.format.return_value = "Formatted instruction for the agent"

        def simulate_agent_modifying_prompt(*args, **kwargs):
            """Side effect: agent touches the prompt file, simulating a real edit."""
            prompt.write_text(
                "% You are a Python math expert.\n"
                "% Requirements\n"
                "1. Create a function `add(a, b)` that returns the sum.\n"
                "2. Create a function `subtract(a, b)` that returns the difference.\n"
            )
            return (True, "Updated prompt with subtract requirement", 0.05, "claude")

        with patch("pdd.agentic_update.get_available_agents", return_value=["claude"]), \
             patch("pdd.agentic_update.load_prompt_template", return_value=mock_template), \
             patch("pdd.agentic_update.run_agentic_task", side_effect=simulate_agent_modifying_prompt):
            success, message, cost, model, changed = run_agentic_update(
                prompt_file=str(prompt),
                code_file=str(code),
                quiet=True,
            )

        print(f"  success      : {success}")        # True
        print(f"  message      : {message}")         # contains "updated successfully"
        print(f"  cost (USD)   : {cost}")             # 0.05
        print(f"  model_used   : {model}")            # "claude"
        print(f"  changed_files: {len(changed)} file(s)")
        if changed:
            print(f"    -> {changed[0]}")
        print()


def example_agent_runs_but_no_change() -> None:
    """Show outcome when agent runs successfully but doesn't modify the prompt."""
    print("=" * 60)
    print("Example 3: Agent runs but prompt unchanged")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        prompt = tmp_path / "module.prompt"
        code = tmp_path / "module.py"
        prompt.write_text("% Already up to date\n")
        code.write_text("def foo(): pass\n")

        mock_template = MagicMock()
        mock_template.format.return_value = "Formatted instruction"

        with patch("pdd.agentic_update.get_available_agents", return_value=["claude"]), \
             patch("pdd.agentic_update.load_prompt_template", return_value=mock_template), \
             patch("pdd.agentic_update.run_agentic_task", return_value=(True, "No changes needed", 0.02, "claude")):
            success, message, cost, model, changed = run_agentic_update(
                prompt_file=str(prompt),
                code_file=str(code),
                quiet=True,
            )

        print(f"  success      : {success}")        # False (prompt not modified)
        print(f"  message      : {message}")         # "did not modify"
        print(f"  cost (USD)   : {cost}")             # 0.02
        print(f"  changed_files: {changed}")          # []
        print()


def example_explicit_test_files() -> None:
    """Show how to pass explicit test file paths (with validation)."""
    print("=" * 60)
    print("Example 4: Explicit test files (missing file error)")
    print("=" * 60)

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        prompt = tmp_path / "module.prompt"
        code = tmp_path / "module.py"
        prompt.write_text("% Prompt\n")
        code.write_text("pass\n")

        missing_test = tmp_path / "nonexistent_test.py"

        with patch("pdd.agentic_update.get_available_agents", return_value=["claude"]):
            success, message, cost, model, changed = run_agentic_update(
                prompt_file=str(prompt),
                code_file=str(code),
                test_files=[missing_test],
                quiet=True,
            )

        print(f"  success      : {success}")        # False
        print(f"  message      : {message}")         # "Test file(s) not found: ..."
        print(f"  cost (USD)   : {cost}")             # 0.0
        print()


def example_missing_input_files() -> None:
    """Show early failure when prompt or code file doesn't exist."""
    print("=" * 60)
    print("Example 5: Missing input files")
    print("=" * 60)

    success, message, cost, model, changed = run_agentic_update(
        prompt_file="/tmp/does_not_exist.prompt",
        code_file="/tmp/does_not_exist.py",
        quiet=True,
    )

    print(f"  success      : {success}")        # False
    print(f"  message      : {message}")         # "Prompt file not found: ..."
    print(f"  cost (USD)   : {cost}")             # 0.0
    print()


def main() -> None:
    """Run all examples demonstrating run_agentic_update behavior."""
    print("pdd.agentic_update — Usage Examples")
    print("=" * 60)
    print()

    example_no_agents_available()
    example_successful_update()
    example_agent_runs_but_no_change()
    example_explicit_test_files()
    example_missing_input_files()

    print("All examples completed successfully.")


if __name__ == "__main__":
    main()
