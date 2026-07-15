import os
import sys
import json
from pathlib import Path

# Add the workspace root to sys.path so the pdd package can be resolved
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pdd.sync_orchestration import sync_orchestration


def main():
    # 1. Setup a clean sandbox output directory
    output_dir = Path("./output")
    prompts_dir = output_dir / "prompts"
    code_dir = output_dir / "src"
    examples_dir = output_dir / "examples"
    tests_dir = output_dir / "tests"

    prompts_dir.mkdir(parents=True, exist_ok=True)
    code_dir.mkdir(parents=True, exist_ok=True)
    examples_dir.mkdir(parents=True, exist_ok=True)
    tests_dir.mkdir(parents=True, exist_ok=True)

    # 2. Write a mock development prompt file defining the target interface
    basename = "calculator"
    language = "python"
    prompt_file = prompts_dir / f"{basename}_{language}.prompt"
    prompt_file.write_text(
        "<pdd-interface>\n"
        "{\n"
        "  \"type\": \"module\",\n"
        "  \"module\": {\n"
        "    \"functions\": [\n"
        "      {\"name\": \"add\", \"signature\": \"(a: int, b: int) -> int\"},\n"
        "      {\"name\": \"subtract\", \"signature\": \"(a: int, b: int) -> int\"}\n"
        "    ]\n"
        "  }\n"
        "}\n"
        "</pdd-interface>\n\n"
        "Generate a simple math calculator module.",
        encoding="utf-8"
    )

    print("=== 1. Performing Dry-Run Sync Analysis ===")
    # A dry-run analyzes current files and tells us what sync expects to run
    # (no LLM billing keys required for dry-run mode).
    dry_run_result = sync_orchestration(
        basename=basename,
        language=language,
        prompts_dir=str(prompts_dir),
        code_dir=str(code_dir),
        examples_dir=str(examples_dir),
        tests_dir=str(tests_dir),
        dry_run=True,
        quiet=True
    )
    print(f"Dry Run Result Success: {dry_run_result.get('success')}")
    print(f"Logged Entries Found: {len(dry_run_result.get('log_entries', []))}")


    print("\n=== 2. Initiating a Headless Sync Operation ===")
    # Headless runs run to completion without displaying the visual Textual TUI.
    # To perform a live generation/sync, we check for an active API key first.
    api_key = os.environ.get("OPENAI_API_KEY") or os.environ.get("GEMINI_API_KEY") or os.environ.get("ANTHROPIC_API_KEY")
    if not api_key:
        print("Skipping live sync execution: No API key (OPENAI/GEMINI/ANTHROPIC_API_KEY) detected in environment.")
        sys.exit(0)

    # Execute the live sync workflow
    sync_result = sync_orchestration(
        basename=basename,
        language=language,
        prompts_dir=str(prompts_dir),
        code_dir=str(code_dir),
        examples_dir=str(examples_dir),
        tests_dir=str(tests_dir),
        target_coverage=90.0,
        budget=5.0,  # Cap total token cost at $5.00
        quiet=True,  # Headless mode
        dry_run=False
    )

    print(f"Sync Success: {sync_result.get('success')}")
    print(f"Summary:      {sync_result.get('summary')}")
    print(f"Completed Ops: {', '.join(sync_result.get('operations_completed', []))}")
    print(f"Total Cost:   ${sync_result.get('total_cost', 0.0):.4f}")


if __name__ == "__main__":
    main()