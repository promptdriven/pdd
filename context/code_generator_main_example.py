"""
Example demonstrating how to use the code_generator_main module.

This script sets up a mock environment containing a prompt file and then calls
`code_generator_main` to generate code, simulating both full generation and 
architectural conformance checks.
"""

from __future__ import annotations

import json
import os
import sys
import pathlib
import click
from typing import Any, Dict

# Ensure absolute reference for pdd package
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))

from pdd.code_generator_main import (
    code_generator_main,
    ArchitectureConformanceError,
    PublicSurfaceRegressionError,
    TestChurnError,
)

# Define output directory relative to this script
OUTPUT_DIR = pathlib.Path(__file__).resolve().parent / "output"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

def setup_mock_files() -> tuple[pathlib.Path, pathlib.Path, pathlib.Path]:
    """
    Creates mock prompt, architecture.json, and existing code files inside the output directory
    to prepare for the code generator execution.
    """
    # 1. Create architecture.json describing a module and its exported functions
    arch_file = OUTPUT_DIR / "architecture.json"
    arch_content = {
        "modules": [
            {
                "filename": "math_helper_Python.prompt",
                "filepath": str(OUTPUT_DIR / "math_helper.py"),
                "reason": "Helper module for math operations",
                "dependencies": [],
                "tags": ["module", "python"],
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {
                                "name": "calculate_factorial",
                                "signature": "(n: int) -> int"
                            }
                        ]
                    }
                }
            }
        ]
    }
    arch_file.write_text(json.dumps(arch_content, indent=2), encoding="utf-8")

    # 2. Create math_helper_Python.prompt with pdd-interface tags
    prompt_file = OUTPUT_DIR / "math_helper_Python.prompt"
    prompt_content = """---
name: math_helper_Python
language: Python
---
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "calculate_factorial", "signature": "(n: int) -> int"}
    ]
  }
}
</pdd-interface>

Generate a python function called calculate_factorial that calculates the factorial of n.
"""
    prompt_file.write_text(prompt_content, encoding="utf-8")

    # 3. Create a sibling mock test file to bypass test churn gates if test files are modified
    test_file = OUTPUT_DIR / "test_math_helper.py"
    test_file.write_text("""def test_factorial():
    from math_helper import calculate_factorial
    assert calculate_factorial(5) == 120
""", encoding="utf-8")

    return prompt_file, arch_file, test_file

def main() -> None:
    print("=== PDD Code Generator Main Orchestrator Example ===\n")

    # Setup mock files for the generator to run against
    prompt_file, arch_file, test_file = setup_mock_files()
    output_code_path = OUTPUT_DIR / "math_helper.py"

    print(f"Mock environment setup:")
    print(f"  Prompt File: {prompt_file.name}")
    print(f"  Architecture Config: {arch_file.name}")
    print(f"  Output Code Destination: {output_code_path.name}\n")

    # Initialize a mock Click Context to carry cli parameters
    # code_generator_main expects this structure to parse cli configuration values
    ctx = click.Context(click.Command('generate'))
    ctx.obj = {
        "local": True,           # Instructs generator to run locally rather than querying the cloud
        "strength": 0.7,         # LLM reasoning strength (0.0 to 1.0)
        "temperature": 0.0,      # LLM sampling temperature
        "time": 0.25,            # LLM thinking budget / timeout scaling
        "verbose": True,         # Print internal logging and step status
        "force": True,           # Overwrite output files without prompting
        "quiet": False           # Do not suppress console panel updates
    }

    # We need to temporarily point architecture.json parsing to our mock location
    # code_generator_main defaults to looking at "architecture.json" in current working directory.
    # For this example, we mock the current working directory or ensure our env is clean.
    orig_cwd = os.getcwd()
    os.chdir(str(OUTPUT_DIR))

    print("Executing code_generator_main...")
    try:
        # Inputs:
        #   - ctx: Click Context holding CLI parameter overrides
        #   - prompt_file: Filepath of the source .prompt template
        #   - output: Overriding destination filepath (None defaults to front-matter/config paths)
        #   - original_prompt_file_path: Used for incremental diff comparisons
        #   - force_incremental_flag: Forces incremental diff update if True
        #   - env_vars: Optional environment variables to substitute into prompt template placeholders
        #
        # Outputs:
        #   - generated_code: The parsed, generated output string
        #   - was_incremental: Boolean indicating if a patch was applied instead of full overwrite
        #   - total_cost: Estimated monetary cost of the LLM generation (in USD)
        #   - model_name: Name of the LLM model that performed the generation
        generated_code, was_incremental, total_cost, model_name = code_generator_main(
            ctx=ctx,
            prompt_file=prompt_file.name,
            output=str(output_code_path),
            original_prompt_file_path=None,
            force_incremental_flag=False,
            env_vars={},
            language="python"
        )

        print("\n--- Generation Output ---")
        print(f"Model Used: {model_name}")
        print(f"Generation Cost: ${total_cost:.6f}")
        print(f"Incremental Patch Applied: {was_incremental}")
        print(f"Generated Code Content:\n{generated_code}")

    except ArchitectureConformanceError as e:
        print(f"\n[Conformance Error] Generated code violated the interface contract:")
        print(f"  Missing symbols: {e.missing_symbols}")
        print(f"  Repair Directive:")
        print(e.repair_directive)
    except PublicSurfaceRegressionError as e:
        print(f"\n[Regression Error] Public API surface was shrunk without BREAKING-CHANGE:")
        print(f"  Removed: {e.removed_symbols}")
        print(f"  Signatures Changed: {e.changed_signatures}")
    except TestChurnError as e:
        print(f"\n[Churn Error] Sibling test file was rewritten past the allowed threshold:")
        print(f"  Churn Ratio: {e.churn_ratio:.2f} (Threshold: {e.threshold:.2f})")
    finally:
        # Restore original working directory
        os.chdir(orig_cwd)

    print("\nExample execution completed successfully.")

if __name__ == "__main__":
    main()