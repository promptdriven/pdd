"""Demonstrate how to call edit_file from edit_file_tool.core.

This script shows how to:
- Validate that the ANTHROPIC_API_KEY is set before calling the API.
- Locate an example target file relative to this script without hardcoding absolute paths.
- Supply clear edit instructions to edit_file and report the result.

Parameters exposed to edit_file:
- file_path (str): the filesystem path to edit, which must already exist and point to a regular file.
- edit_instructions (str): human-readable instructions describing the desired changes.
- model (str): Claude model to use (defaults to "claude-3-7-sonnet-20250219").
- verbose (bool): when True, enables DEBUG-style logging inside edit_file for iteration tracing.
- use_cache (Union[str, bool]): controls prompt caching behavior (default "auto").
- max_iterations (int): maximum number of tool-use exchanges before giving up.

Outputs:
- success (bool): True when Claude finished without requesting further edits, False on any validation or execution failure.
- error_message (str): empty string on success or a descriptive failure reason.
- total_cost (float): accumulated USD cost for all Claude API calls made during the edit.
"""

import asyncio
import os
import sys
from pathlib import Path

from edit_file_tool.core import edit_file


def _ensure_api_key() -> None:
    if not os.environ.get("ANTHROPIC_API_KEY"):
        print("=" * 60)
        print("ANTHROPIC_API_KEY environment variable not set.")
        print("This example requires an Anthropic API key to run.")
        print()
        print("To run this example, set your API key:")
        print("  export ANTHROPIC_API_KEY='your-api-key-here'")
        print()
        print("Get your key at: https://console.anthropic.com/")
        print("=" * 60)
        sys.exit(0)


def _prepare_example_file(example_file: Path) -> None:
    if not example_file.exists():
        example_file.write_text("# Example target file\nOriginal line." + "\n", encoding="utf-8")


async def main() -> None:
    """Run the edit_file workflow on a sample file and print the outcome.

    This coroutine demonstrates the inputs and outputs described above.
    """

    _ensure_api_key()

    script_dir = Path(__file__).resolve().parent
    sample_file = script_dir / "sample_target.txt"
    _prepare_example_file(sample_file)

    instructions = (
        "Please replace 'Original line.' with 'Updated line via edit_file() example.'."
        " Keep the header unchanged."
    )

    print("Starting edit_file example for:", sample_file)

    success, error_message, total_cost = await edit_file(
        file_path=str(sample_file),
        edit_instructions=instructions,
        verbose=True,
    )

    if success:
        print(f"Edit succeeded (cost=${total_cost:.6f}).")
    else:
        print(f"Edit failed: {error_message} (cost=${total_cost:.6f}).")


if __name__ == "__main__":
    asyncio.run(main())