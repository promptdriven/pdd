from __future__ import annotations

import os
import sys
from pathlib import Path
from rich.console import Console

# Add the project root to sys.path
project_root = Path(__file__).resolve().parent.parent
sys.path.append(str(project_root))

# Import the main function from the module
from pdd.agentic_split_orchestrator import run_agentic_split_orchestrator

# Initialize Rich console for output
console = Console()

def main() -> None:
    """
    Demonstrates usage of run_agentic_split_orchestrator from the agentic_split_orchestrator module.

    This example:
    1. Sets up a temporary working directory relative to this script.
    2. Creates a dummy target file for splitting.
    3. Calls the orchestrator with sample parameters.
    4. Prints the results.

    Input Parameters (as defined in run_agentic_split_orchestrator):
        target_file (str): The target file to split (e.g., a prompt file path).
        cwd (Path): The current working directory (Path object).
        verbose (bool, optional): Enable verbose output. Defaults to False.
        quiet (bool, optional): Enable quiet mode. Defaults to False.
        timeout_adder (float, optional): Additional timeout to add to steps. Defaults to 0.0.
        use_github_state (bool, optional): Whether to use GitHub state. Defaults to True.
        diagnose_only (bool, optional): Only perform diagnosis step. Defaults to False.
        propose_only (bool, optional): Only propose split options. Defaults to False.
        delete_dead (bool, optional): Delete dead code. Defaults to False.
        force_split (bool, optional): Force the split even if not recommended. Defaults to False.
        no_verify (bool, optional): Skip verification steps. Defaults to False.
        skip_regen_gate (bool, optional): Skip regeneration gate. Defaults to False.
        experimental_language (bool, optional): Enable experimental language support. Defaults to False.

    Output:
        A tuple: (success: bool, message: str, total_cost: float, model_used: str, changed_files: List[str])
    """
    # Get the directory of this script for relative path resolution
    script_dir: Path = Path(os.path.dirname(__file__))

    # Set up a temporary working directory relative to the script
    temp_cwd: Path = script_dir / "temp_split_dir"
    temp_cwd.mkdir(exist_ok=True)

    # Create a dummy target file (e.g., a prompt file) in the temp directory
    target_file_path: Path = temp_cwd / "example_module_python.prompt"
    target_file_path.write_text("Dummy prompt content for splitting.", encoding="utf-8")
    target_file: str = str(target_file_path.relative_to(temp_cwd))  # Relative path for input

    try:
        # Call the orchestrator with sample parameters
        result = run_agentic_split_orchestrator(
            target_file=target_file,
            cwd=temp_cwd,
            verbose=True,
            quiet=False,
            timeout_adder=10.0,
            use_github_state=False,
            diagnose_only=False,
            propose_only=False,
            delete_dead=True,
            force_split=True,
            no_verify=False,
            skip_regen_gate=False,
            experimental_language=True,
            intent=None,  # v2.2: let step 0 infer
            no_phase_extraction=False,  # v2.2: enable phase helpers
        )
        success: bool
        message: str
        total_cost: float
        model_used: str
        changed_files: list[str]
        success, message, total_cost, model_used, changed_files = result

        # Print results using Rich console
        console.print("[bold blue]Orchestrator Results:[/bold blue]")
        console.print(f"Success: {success}")
        console.print(f"Message: {message}")
        console.print(f"Total Cost: ${total_cost:.4f}")
        console.print(f"Model Used: {model_used}")
        console.print(f"Changed Files: {changed_files}")
    except Exception as e:
        console.print(f"[bold red]Error occurred: {e}[/bold red]")
    finally:
        # Clean up temporary directory so we don't leave artifacts.
        import shutil
        shutil.rmtree(temp_cwd, ignore_errors=True)

if __name__ == "__main__":
    main()