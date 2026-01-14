# To run this example:
# From project root: python examples/cli_example.py
# Note: sys.path manipulation in this script ensures imports work from project root
import asyncio
import sys
from pathlib import Path

# Ensure the project root is on sys.path so imports resolve from this script when run directly.
project_root = Path(__file__).parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from edit_file_tool import cli, core


def _fake_successful_edit(*, file_path: str, edit_instructions: str, model: str, verbose: bool, use_cache, max_iterations: int):
    """Simulates a successful edit_file invocation for demonstration."""
    async def _inner():
        await asyncio.sleep(0)
        return True, "Success", 0.0345

    return _inner()


def _fake_failed_edit(*, file_path: str, edit_instructions: str, model: str, verbose: bool, use_cache, max_iterations: int):
    """Simulates a failed edit_file invocation to show error reporting."""
    async def _inner():
        await asyncio.sleep(0)
        return False, "Simulated editing conflict", 0.0123

    return _inner()


def demonstrate_operations():
    """Demonstrates how to use edit_file_tool.cli from Python with sample files.

    The function illustrates both successful and error flow invocations, including how the
    CLI validates inputs, reports costs, and surfaces errors. The demo file is cleaned up
    in a finally block so repeated runs are safe.
    """
    print("Starting CLI demonstration using edit_file_tool.cli")
    demo_file = Path(__file__).parent / "cli_demo_target.txt"
    original_edit_file = core.edit_file
    try:
        print(f"Creating demonstration file at {demo_file}")
        with open(demo_file, "w", encoding="utf-8") as handle:
            handle.write("# Placeholder content for CLI demo\n")

        print("Running successful edit simulation...")
        core.edit_file = _fake_successful_edit
        args_success = [
            str(demo_file),
            "Replace the placeholder comment with a short summary",
            "--verbose",
        ]
        try:
            exit_code = cli.main(args_success)
        except Exception as exc:  # pragma: no cover - demonstration safety
            print(f"Unhandled exception during success scenario: {exc}")
        else:
            print(f"Success scenario exit code: {exit_code}")

        print("Running failure simulation that mimics an edit conflict...")
        core.edit_file = _fake_failed_edit
        args_conflict = [
            str(demo_file),
            "Mark this section as reviewed",
        ]
        try:
            exit_code = cli.main(args_conflict)
        except Exception as exc:
            print(f"Unexpected exception during failure scenario: {exc}")
        else:
            print(f"Failure scenario exit code: {exit_code}")

        print("Demonstrating validation error when instructions are empty...")
        args_empty = [
            str(demo_file),
            "   ",
        ]
        try:
            exit_code = cli.main(args_empty)
        except Exception as exc:
            print(f"Exception when instructions are empty: {exc}")
        else:
            print(f"Empty instruction scenario exit code: {exit_code}")

    finally:
        core.edit_file = original_edit_file
        if demo_file.exists():
            print(f"Cleaning up demonstration file at {demo_file}")
            demo_file.unlink()


if __name__ == "__main__":
    demonstrate_operations()