"""
Example demonstrating how to use the ci_drift_heal module.

This module is designed to run in CI pipelines to detect and auto-heal
prompt and example drift in PDD modules.
"""

import os
from unittest.mock import patch

# Import the module so we can patch attributes by attribute access.
import pdd.ci_drift_heal as ci_drift_heal
from pdd.ci_drift_heal import DriftInfo, HealResult


def demonstrate_detect_drift() -> None:
    """
    Demonstrates how detect_drift returns two lists of DriftInfo records:
    one for modules whose prompts need updates, and one for modules whose
    examples (or new code) need to be regenerated.
    """
    print("--- Demonstrating detect_drift ---")

    mock_prompt_drifts = [
        DriftInfo(
            basename="example_module",
            language="python",
            operation="update",
            reason="Code changed without prompt changes",
            code_path="pdd/example_module.py",
            prompt_path="prompts/example_module_python.prompt",
        )
    ]
    mock_example_drifts = [
        DriftInfo(
            basename="another_module",
            language="python",
            operation="example",
            reason="Prompt changed, example needs refresh",
            code_path="pdd/another_module.py",
            prompt_path="prompts/another_module_python.prompt",
            example_path="context/another_module_example.py",
        )
    ]

    # Patch the module attribute and call through the module so the patch is honoured.
    with patch.object(
        ci_drift_heal, "detect_drift", return_value=(mock_prompt_drifts, mock_example_drifts)
    ):
        prompt_drifts, example_drifts = ci_drift_heal.detect_drift(
            modules=None, diff_base="main"
        )

        print(f"Detected {len(prompt_drifts)} modules needing prompt updates:")
        for drift in prompt_drifts:
            print(f"  - {drift.basename}: {drift.reason}")

        print(f"Detected {len(example_drifts)} modules needing example updates:")
        for drift in example_drifts:
            print(f"  - {drift.basename}: {drift.reason}")


def demonstrate_heal_result() -> None:
    """
    Demonstrates the HealResult dataclass returned by heal_module.
    """
    print("\n--- Demonstrating HealResult ---")
    result = HealResult(basename="example_module", success=True, cost=0.12)
    print(f"Result: basename={result.basename}, success={result.success}, "
          f"cost={result.cost}, error={result.error!r}")


def demonstrate_main() -> None:
    """
    Demonstrates the main entry point. We patch the module-level main so this
    example does not invoke real git or LLM operations.
    """
    print("\n--- Demonstrating main entry point ---")

    with patch.object(ci_drift_heal, "main", return_value=0) as mock_main:
        exit_code = ci_drift_heal.main(
            modules=["example_module"],
            budget_cap=5.0,
            skip_ci=True,
            diff_base="main",
        )

        print(f"Main function returned exit code: {exit_code}")
        print(f"Main was called with arguments: {mock_main.call_args}")


if __name__ == "__main__":
    # Ensure output directory exists for any file operations
    output_dir = os.path.join(os.path.dirname(__file__), "..", "output")
    os.makedirs(output_dir, exist_ok=True)

    print("PDD CI Drift Heal Example")
    print("=========================")

    demonstrate_detect_drift()
    demonstrate_heal_result()
    demonstrate_main()

    print("\nExample completed successfully.")
