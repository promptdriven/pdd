from __future__ import annotations

import os
import sys
from unittest.mock import patch

from rich.console import Console

# Import the functions and data structures from the module
from pdd.ci_drift_heal import (
    DriftInfo,
    commit_and_push,
    detect_drift,
    heal_module,
    main,
)

console = Console()


def demonstrate_drift_info() -> None:
    """Demonstrate how DriftInfo represents a drifted module.
    
    DriftInfo is a dataclass used throughout ci_drift_heal to track the
    state of a module that needs automated healing.
    """
    drift = DriftInfo(
        basename="demo_module",
        language="python",
        operation="update",
        reason="Prompt changed without code changes",
        prompt_path="prompts/demo_module_python.prompt",
        code_path="pdd/demo_module.py",
        estimated_cost=0.15
    )
    console.print("[bold green]Created DriftInfo:[/bold green]")
    console.print(f"  Basename: {drift.basename}")
    console.print(f"  Operation: {drift.operation}")
    console.print(f"  Reason: {drift.reason}")


def demonstrate_mocked_main() -> None:
    """Demonstrate the main entry point using mocked dependencies.
    
    Because ci_drift_heal orchestrates real git commands and subprocesses,
    we mock the core Git and PDD subprocess logic here to safely show 
    how the workflow executes.
    """
    console.print("\n[bold green]Running ci_drift_heal.main() with mocks...[/bold green]")
    
    # We mock detect_drift to return a dummy drift
    dummy_drift = DriftInfo(
        basename="mocked_module",
        language="python",
        operation="example",
        reason="Mocked drift for example demonstration",
        prompt_path="prompts/mocked_module_python.prompt",
        code_path="pdd/mocked_module.py"
    )
    
    # Patch out the heavy lifting functions so it runs safely in the example
    with patch("pdd.ci_drift_heal.detect_drift", return_value=([], [dummy_drift])), \
         patch("pdd.ci_drift_heal.heal_module", return_value=True), \
         patch("pdd.ci_drift_heal.commit_and_push", return_value=True), \
         patch("pdd.ci_drift_heal._repo_root", return_value=os.getcwd()):
         
         # Call the main entry point.
         # In a real environment, this is invoked via: python -m pdd.ci_drift_heal
         exit_code = main(
             modules=["mocked_module"],  # Restrict healing to specific modules
             budget_cap=5.0,             # Stop healing if LLM cost exceeds $5.00
             skip_ci=True                # Prepend [skip ci] to the git commit message
         )
         console.print(f"[cyan]main() completed with exit code: {exit_code}[/cyan]")


if __name__ == "__main__":
    console.print("[bold]ci_drift_heal Example[/bold]")
    console.print("=====================")
    demonstrate_drift_info()
    demonstrate_mocked_main()