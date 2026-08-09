"""
Example demonstrating how to use the pdd.update_main module to:
1. Resolve a prompt and code file pair based on workspace conventions.
2. Run single-file prompt regeneration/updating.
3. Perform a mock repository-wide drift scan using `update_main`.

This example is non-interactive and runs to completion. All temporary files
and outputs are structured inside the './output' directory.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path
import click

# Ensure the parent directory is in sys.path to allow importing from the pdd package
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pdd.update_main import (
    resolve_prompt_code_pair,
    find_and_resolve_all_pairs,
    update_main,
)

# Output directory for all generated artifacts
OUTPUT_DIR = Path("./output").resolve()


def setup_mock_workspace() -> tuple[Path, Path]:
    """
    Creates a mock codebase structure under ./output.
    Returns the paths to the mock code file and its corresponding prompt file.
    """
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    # 1. Create a mock Python code file
    src_dir = OUTPUT_DIR / "src"
    src_dir.mkdir(exist_ok=True)
    code_file = src_dir / "calculator.py"
    code_file.write_text(
        "def add(a: int, b: int) -> int:\n"
        "    return a + b\n\n"
        "def multiply(a: int, b: int) -> int:\n"
        "    return a * b\n",
        encoding="utf-8",
    )

    # 2. Create a mock prompts directory
    prompts_dir = OUTPUT_DIR / "prompts"
    prompts_dir.mkdir(exist_ok=True)
    prompt_file = prompts_dir / "calculator_python.prompt"
    
    # Write a simple, mock prompt
    prompt_file.write_text(
        "% You are an expert Python engineer.\n"
        "% Requirements\n"
        "1. Create a function `add` that returns the sum of two integers.\n",
        encoding="utf-8",
    )

    # 3. Create a minimal .pddrc configuration file
    pddrc_file = OUTPUT_DIR / ".pddrc"
    pddrc_file.write_text(
        "contexts:\n"
        "  default:\n"
        "    prompts_dir: 'prompts'\n"
        "    generate_output_path: 'src'\n",
        encoding="utf-8",
    )

    return code_file, prompt_file


def main() -> None:
    # Set up the mock environment
    code_file, prompt_file = setup_mock_workspace()

    print("=== 1. Resolving Prompt and Code Pair ===")
    # Resolve where the corresponding prompt should live relative to the code file.
    # Inputs:
    #   - code_file_path (str): The absolute or relative path to the modified code file.
    #   - quiet (bool): Suppress informational console logs.
    #   - output_dir (Optional[str]): Custom target prompts directory.
    #   - create_missing (bool): Create the prompt file if it doesn't exist.
    resolved_prompt_path, resolved_code_path = resolve_prompt_code_pair(
        code_file_path=str(code_file),
        quiet=False,
        output_dir=str(OUTPUT_DIR / "prompts"),
        create_missing=True
    )
    print(f"  Code File:   {resolved_code_path}")
    print(f"  Prompt File: {resolved_prompt_path}\n")

    print("=== 2. Mocking CLI Click Context ===")
    # In practice, `update_main` is triggered by Click commands and extracts CLI configs
    # (like verbose, quiet, strength, and temperature) from Click's Context.
    ctx = click.Context(click.Command('update'))
    ctx.obj = {
        "verbose": False,
        "quiet": False,
        "strength": 0.5,
        "temperature": 0.2,
    }

    print("=== 3. Simulating Repo-Wide Drift Scan ===")
    # Perform a dry-run repository update to see which prompts have drifted
    # without making actual LLM billing calls.
    # Inputs:
    #   - ctx (click.Context): The Click CLI context dict.
    #   - input_prompt_file: Optional single target prompt.
    #   - modified_code_file: Optional single target code file.
    #   - repo (bool): Scan the entire repository directory.
    #   - directory (str): Target directory to scan.
    #   - dry_run (bool): Scan and print the drift report without executing updates.
    # Outputs:
    #   - Optional[Tuple[str, float, str]]: (Status/Result message, total cost in USD, models used).
    result = update_main(
        ctx=ctx,
        input_prompt_file=None,
        modified_code_file=None,
        input_code_file=None,
        output=None,
        repo=True,
        directory=str(OUTPUT_DIR),
        dry_run=True,
    )

    if result:
        message, total_cost_usd, model_used = result
        print("Dry Run Scan Result:")
        print(f"  Message:    {message}")
        print(f"  Est. Cost:  ${total_cost_usd:.6f}")
        print(f"  Model:      {model_used}")
    else:
        print("No out-of-sync code files detected in the scanned directory.")


if __name__ == "__main__":
    main()