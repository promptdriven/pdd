from __future__ import annotations

import os
import sys
import json
import pathlib
import click
from typing import Any, Dict

# Dynamic path resolution to ensure 'pdd' is in sys.path
SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
sys.path.append(str(PROJECT_ROOT))

# Import the main orchestration entry point and structured errors
from pdd.code_generator_main import (
    code_generator_main,
    ArchitectureConformanceError,
    PublicSurfaceRegressionError,
    TestChurnError,
)


def setup_mock_environment(output_dir: pathlib.Path) -> tuple[pathlib.Path, pathlib.Path]:
    """
    Creates a mock prompt file and architecture.json to demonstrate conformance checking.
    """
    output_dir.mkdir(parents=True, exist_ok=True)

    # 1. Create a mock architecture contract requiring 'calculate_area' function
    arch_file = output_dir / "architecture.json"
    arch_data = {
        "modules": [
            {
                "filename": "geometry_math_Python.prompt",
                "filepath": "output/geometry_math.py",
                "reason": "Orchestrates simple geometry math calculations.",
                "dependencies": [],
                "tags": ["geometry", "math"],
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": [
                            {
                                "name": "calculate_area",
                                "signature": "(width: float, height: float) -> float"
                            }
                        ]
                    }
                }
            }
        ]
    }
    arch_file.write_text(json.dumps(arch_data, indent=2), encoding="utf-8")

    # 2. Create a mock .prompt file containing our target pdd-interface contract
    prompt_file = output_dir / "geometry_math_Python.prompt"
    prompt_content = """---
language: Python
output: output/geometry_math.py
---
<pdd-reason>Provides area calculation routines.</pdd-reason>

<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {
        "name": "calculate_area",
        "signature": "(width: float, height: float) -> float"
      }
    ]
  }
}
</pdd-interface>

Generate a Python function called `calculate_area` that multiplies width by height.
"""
    prompt_file.write_text(prompt_content, encoding="utf-8")

    return prompt_file, arch_file


def main() -> None:
    """
    Demonstrates how to run code_generator_main programmatically within a click Context.
    """
    print("=== Starting PDD Code Generator Main Example ===")

    # Ensure we are not fully using remote cloud services if keys are missing
    # This forces local LLM execution / mock execution fallback in our test run
    os.environ["PDD_FORCE_LOCAL"] = "1"
    
    # Define the output directory relative to this script
    output_dir = SCRIPT_DIR / "output"
    prompt_file, arch_file = setup_mock_environment(output_dir)
    
    resolved_output_path = str(output_dir / "geometry_math.py")

    # Click commands require an active Context holding user flags
    # We create a dummy context mimicking: pdd generate prompts/geometry_math_Python.prompt --local
    ctx = click.Context(click.Command("generate"))
    ctx.obj = {
        "local": True,
        "strength": 0.7,      # Model capability mapping parameter (0.0 to 1.0)
        "temperature": 0.0,   # Determinism of output generation (0.0 to 2.0)
        "time": 0.25,         # Budget for model thinking effort (0.0 to 1.0)
        "verbose": True,
        "force": True,
        "quiet": False,
    }

    print(f"\nInput prompt file: {prompt_file.name}")
    print(f"Target output path: {resolved_output_path}")
    print("Invoking Code Generation Orchestrator...")

    try:
        # Invoke the generator main orchestration engine
        # Returns: (generated_code, was_incremental, total_cost, model_name)
        # Units:
        #   total_cost: USD ($) incurred during the generation session.
        generated_code, was_incremental, total_cost, model_name = code_generator_main(
            ctx=ctx,
            prompt_file=str(prompt_file),
            output=resolved_output_path,
            original_prompt_file_path=None,
            force_incremental_flag=False,
            env_vars={},
            unit_test_file=None,
            exclude_tests=True,
            language="python",
            output_from_config=False,
            compress=False,
            snapshot_context=False,
        )

        print("\n--- Generation Completed successfully ---")
        print(f"Was Incremental Patched: {was_incremental}")
        print(f"Incurred Cost: ${total_cost:.6f}")
        print(f"Model Used: {model_name}")
        print("\nGenerated Content preview:")
        print("-" * 40)
        print(generated_code.strip())
        print("-" * 40)

    except ArchitectureConformanceError as err:
        print("\n[FAIL] Code violates the declared architecture contract!")
        print(f"Error Message: {err}")
        print(f"Expected Symbols: {err.expected_symbols}")
        print(f"Missing Symbols: {err.missing_symbols}")
        print(f"Model face repair directive:\n{err.repair_directive}")

    except PublicSurfaceRegressionError as err:
        print("\n[FAIL] Public surface regression detected (Backward compatibility broken)!")
        print(f"Removed Symbols: {err.removed_symbols}")
        print(f"Pre-surface size: {err.pre_surface_size} -> Post-surface: {err.post_surface_size}")
        print(f"Repair instructions:\n{err.repair_directive}")

    except TestChurnError as err:
        print("\n[FAIL] Test modification limits exceeded!")
        print(f"Churn Ratio: {err.churn_ratio:.2%}")
        print(f"Line count pre: {err.pre_line_count} -> Post: {err.post_line_count}")

    finally:
        # Clean up mock workspace files
        if prompt_file.exists():
            prompt_file.unlink()
        if arch_file.exists():
            arch_file.unlink()
        output_file = output_dir / "geometry_math.py"
        if output_file.exists():
            output_file.unlink()
        if output_dir.exists():
            try:
                output_dir.rmdir()
            except OSError:
                pass
        print("\nTemporary mock directories cleaned up.")


if __name__ == "__main__":
    main()