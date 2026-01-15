"""
CLI entry point for the edit-file-tool.
Handles argument parsing, input validation, and reporting results from the core editing logic.
"""

import argparse
import asyncio
import sys
from pathlib import Path
from typing import List, Optional, Tuple, Union

# Import the module to allow for monkey-patching in tests/demos
from edit_file_tool import core


def build_parser() -> argparse.ArgumentParser:
    """
    Constructs the argument parser for the edit-file command.
    """
    parser = argparse.ArgumentParser(
        prog="edit-file",
        description="Edit a file using LLM-driven instructions.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )

    # Positional arguments
    parser.add_argument(
        "file_path",
        help="Path to the target file to be edited."
    )
    parser.add_argument(
        "edit_instructions",
        help="Natural language instructions describing the desired changes."
    )

    # Optional flags
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Enable diagnostic output and detailed logging."
    )
    parser.add_argument(
        "--model",
        default="claude-3-7-sonnet-20250219",
        help="The Anthropic model to use for editing."
    )
    parser.add_argument(
        "--cache",
        choices=["auto", "always", "never"],
        default="auto",
        help="Control Anthropic prompt caching behavior."
    )
    parser.add_argument(
        "--max-iterations",
        type=int,
        default=10,
        help="Maximum number of tool-use iterations allowed."
    )

    return parser


def _map_cache_mode(cache_flag: str) -> Union[str, bool]:
    """
    Maps CLI cache string choices to the core API's expected types.
    """
    if cache_flag == "always":
        return True
    if cache_flag == "never":
        return False
    return "auto"


async def _run_edit(args: argparse.Namespace) -> Tuple[bool, str, float]:
    """
    Invokes the core async edit_file function with parsed arguments.
    """
    cache_mode = _map_cache_mode(args.cache)
    
    # Access via core module to support monkey-patching
    return await core.edit_file(
        file_path=args.file_path,
        edit_instructions=args.edit_instructions,
        model=args.model,
        verbose=args.verbose,
        use_cache=cache_mode,
        max_iterations=args.max_iterations
    )


def main(argv: Optional[List[str]] = None) -> int:
    """
    Main entry point for the edit-file CLI.
    
    Returns:
        0 for success, non-zero for failure.
    """
    parser = build_parser()
    args = parser.parse_args(argv)

    # 1. Pre-flight validation
    path = Path(args.file_path)
    if not path.exists():
        print(f"Error: File not found: {args.file_path}", file=sys.stderr)
        return 1
    if not path.is_file():
        print(f"Error: Path is not a file: {args.file_path}", file=sys.stderr)
        return 1
    
    # Validate instructions are not just whitespace
    if not args.edit_instructions or not args.edit_instructions.strip():
        print("Error: Edit instructions cannot be empty", file=sys.stderr)
        return 1

    # 2. Verbose preamble
    if args.verbose:
        print(f"--- CLI Configuration ---")
        print(f"Target File: {args.file_path}")
        print(f"Model:       {args.model}")
        print(f"Cache Mode:  {args.cache}")
        print(f"-------------------------")

    # 3. Execution
    try:
        # asyncio.run handles event loop creation and cleanup
        success, message, cost = asyncio.run(_run_edit(args))
        
        # 4. Reporting
        # Ensure cost is treated as float for formatting
        display_cost = cost if cost is not None else 0.0
        print(f"LLM cost: ${display_cost:.4f}")

        if success:
            print("File edited successfully!")
            return 0
        else:
            print(f"Error: {message}", file=sys.stderr)
            return 1

    except KeyboardInterrupt:
        print("\nError: Interrupted", file=sys.stderr)
        return 130
    except Exception as e:
        # Catch-all for unexpected runtime errors (API keys, network, etc.)
        print(f"Error: {str(e)}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
