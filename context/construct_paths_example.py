from __future__ import annotations

import os
import sys
from pathlib import Path
from pdd.construct_paths import construct_paths

def main() -> None:
    # Define the output directory for temporary files
    output_dir = Path("./output")
    output_dir.mkdir(parents=True, exist_ok=True)

    # 1. Create a dummy prompt file to satisfy the input resolution requirement
    # The filename ends with '_python.prompt' so that the language discovery 
    # can automatically infer "python" from the suffix.
    prompt_file = output_dir / "get_user_data_python.prompt"
    prompt_file.write_text(
        "Generate a python function that retrieves user profiles.", 
        encoding="utf-8"
    )

    # 2. Define the input file dictionary mapping keys to their paths
    input_file_paths = {
        "prompt_file": str(prompt_file)
    }

    # 3. Define command-specific options
    # We do not explicitly pass a language here to show how construct_paths
    # dynamically infers it from the filename suffix we created above.
    command_options = {
        "basename": None,
        "language": None,
    }

    print(f"Created mock prompt file at: {prompt_file.resolve()}")
    print("Running construct_paths for the 'generate' command...")

    # 4. Call construct_paths
    # - force=True prevents interactive prompts (critical for non-interactive environments)
    # - quiet=False prints internal rich logs explaining how configurations are applied
    resolved_config, input_strings, output_file_paths, language = construct_paths(
        input_file_paths=input_file_paths,
        force=True,
        quiet=False,
        command="generate",
        command_options=command_options,
        create_error_file=True
    )

    # 5. Output and examine the resolved values
    print("\n--- Path Construction Results ---")
    print(f"Detected Language: {language}")
    print(f"Resolved Basename: {resolved_config.get('basename', 'Unknown')}")
    print(f"Code Output Path:  {output_file_paths.get('output')}")
    print(f"Prompts Directory: {resolved_config.get('prompts_dir')}")
    print(f"Code Directory:    {resolved_config.get('code_dir')}")
    print(f"Loaded Prompt Context:\n\"\"\"\n{input_strings.get('prompt_file', '').strip()}\n\"\"\"")

if __name__ == "__main__":
    main()