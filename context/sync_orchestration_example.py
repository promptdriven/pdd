import os
import sys
import tempfile
from pathlib import Path

# Add the parent directory to sys.path to ensure 'pdd' is importable
# context/sync_orchestration_example.py -> parent is public-pdd
project_root = Path(__file__).resolve().parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from pdd.sync_orchestration import sync_orchestration

def main():
    # The example owns this workspace exclusively. TemporaryDirectory removes it
    # on normal return and on exceptions without touching a user's ./output tree.
    with tempfile.TemporaryDirectory(
        prefix="pdd-sync-orchestration-example-"
    ) as workspace:
        workspace_dir = Path(workspace)
        _run_example(workspace_dir)


def _run_example(workspace_dir: Path):
    """Write temporary setup files, then read historical state in dry-run mode."""
    # These files are example setup only. sync_orchestration(dry_run=True) reads
    # historical state and does not create or modify project artifacts.
    output_dir = workspace_dir

    prompts_dir = output_dir / "prompts"
    prompts_dir.mkdir(exist_ok=True)
    code_dir = output_dir / "src"
    code_dir.mkdir(exist_ok=True)
    examples_dir = output_dir / "examples"
    examples_dir.mkdir(exist_ok=True)
    tests_dir = output_dir / "tests"
    tests_dir.mkdir(exist_ok=True)

    # Create a mock prompt file representing our design specifications
    basename = "basic_adder"
    language = "python"
    prompt_file = prompts_dir / f"{basename}_{language}.prompt"
    prompt_file.write_text(
        "% You are an expert Python engineer.\n"
        "<pdd-interface>\n"
        "{\n"
        "  \"type\": \"module\",\n"
        "  \"module\": {\n"
        "    \"functions\": [\n"
        "      {\"name\": \"add\", \"signature\": \"(a: int, b: int) -> int\"}\n"
        "    ]\n"
        "  }\n"
        "}\n"
        "</pdd-interface>\n"
        "Create a simple utility function `add` that returns the sum of two integers.",
        encoding="utf-8"
    )

    print("--- 1. Running Sync Orchestration (Dry-Run Mode) ---")
    # Inputs:
    #   - basename (str): The unique base name of our module
    #   - target_coverage (float): Code coverage goal (defaults to 90.0%)
    #   - prompts_dir / code_dir / examples_dir / tests_dir (str): Paths relative to workspace
    #   - dry_run (bool): Set to True to analyze state and print the historical log without modifying disk files
    #   - budget (float): Maximum dollar budget (USD) allowed for LLM calls
    #   - quiet (bool): Suppresses parallel TUI progress animations
    #
    # Outputs:
    #   - Dict[str, Any]: Returns status flags, completed operations list, and full history when dry_run=True
    result = sync_orchestration(
        basename=basename,
        target_coverage=90.0,
        language=language,
        prompts_dir=str(prompts_dir),
        code_dir=str(code_dir),
        examples_dir=str(examples_dir),
        tests_dir=str(tests_dir),
        budget=10.0,
        dry_run=True,
        quiet=True
    )

    print(f"Sync Analysis Finished:")
    print(f"  • Execution Success : {result.get('success')}")
    
    # If historical logs exist, display how many events are tracked
    if "log_entries" in result:
        print(f"  • Tracked History   : {len(result['log_entries'])} operations executed previously")

if __name__ == "__main__":
    main()
