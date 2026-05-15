import json
import os
import sys
from pathlib import Path

# Ensure pdd is importable from the project root
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from pdd.metadata_sync import run_metadata_sync


def main() -> None:
    """
    Example demonstrating how to use run_metadata_sync to orchestrate
    metadata finalization (tags, architecture, run report, fingerprint).
    """
    # 1. Setup mock environment in ./output
    output_dir = Path("./output")
    prompts_dir = output_dir / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)

    # Create a dummy prompt file
    prompt_path = prompts_dir / "example_python.prompt"
    prompt_path.write_text(
        "<pdd-reason>Demonstrate metadata sync</pdd-reason>\n\n"
        "Write a Python script that prints 'Hello, World!'.",
        encoding="utf-8"
    )

    # Create a dummy architecture.json
    arch_path = output_dir / "architecture.json"
    arch_path.write_text(
        json.dumps([
            {
                "filename": "example_python.prompt",
                "reason": "Demonstrate metadata sync",
                "dependencies": []
            }
        ]),
        encoding="utf-8"
    )

    print("Running metadata sync (dry run)...")
    
    # 2. Run the synchronizer
    # We use dry_run=True to preview changes without modifying files.
    result = run_metadata_sync(
        prompt_path=prompt_path,
        code_path=None,
        dry_run=True,
        repo_root=output_dir,
        architecture_path=arch_path,
    )

    # 3. Inspect the results
    print(f"\nSync result OK: {result.ok}")
    if result.failing_stage:
        print(f"Failed at stage: {result.failing_stage}")

    print("\nStage Statuses:")
    for stage_name, status in result.stages.items():
        print(f" - {stage_name}: {status.status} (Detail: {status.detail})")


if __name__ == "__main__":
    main()