from __future__ import annotations

import os
import sys
from pathlib import Path
from typing import Any, Dict

# Ensure pdd package is discoverable relative to the workspace root
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pdd.construct_paths import construct_paths


def main() -> None:
    # All created files should be placed in the './output' directory
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)

    # 1. Create a mock prompt file needed for the path construction.
    # Note: construct_paths strictly resolves input files, so they must exist on disk.
    prompt_file = output_dir / "render_button_python.prompt"
    prompt_file.write_text(
        "Generate a simple button component in Python.", encoding="utf-8"
    )

    # Create an empty error file (construct_paths can generate this automatically if configured)
    error_file = output_dir / "generation_errors.log"
    if error_file.exists():
        error_file.unlink()

    # 2. Define the input files dict
    input_file_paths = {
        "prompt_file": str(prompt_file),
        "error_file": str(error_file),
    }

    # 3. Define command-specific options (CLI options)
    # This matches the schema and keys parsed by PDD.
    command_options: Dict[str, Any] = {
        "language": "python",
        "temperature": 0.2,
        "max_attempts": 3,
        # We can also supply explicit output overrides if wanted, e.g.:
        # "output_code": str(output_dir / "button.py")
    }

    print("--- Executing construct_paths ---")

    # 4. Call the orchestrator
    # We pass force=True to ensure it runs completely non-interactively
    resolved_config, input_strings, output_file_paths, language = construct_paths(
        input_file_paths=input_file_paths,
        force=True,  # Bypass overwrite confirmation prompt
        quiet=False,  # Let it print standard diagnostic summaries
        command="generate",
        command_options=command_options,
        create_error_file=True,
        context_override=None,
        confirm_callback=None,
        path_resolution_mode="config_base",
    )

    print("\n--- Results Summary ---")
    print(f"Detected Language: {language}")
    print(f"Resolved Basename: {resolved_config.get('basename', 'N/A')}")
    print(f"Prompt Content Loaded: '{input_strings.get('prompt_file', '').strip()}'")
    print("\nResolved Output File Paths:")
    for key, path in output_file_paths.items():
        print(f"  • {key}: {path}")

    print("\nResolved Directory Configurations:")
    print(f"  • Code Dir: {resolved_config.get('code_dir')}")
    print(f"  • Tests Dir: {resolved_config.get('tests_dir')}")
    print(f"  • Examples Dir: {resolved_config.get('examples_dir')}")


if __name__ == "__main__":
    main()