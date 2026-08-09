from __future__ import annotations

import json
import os
from pathlib import Path
from pdd.architecture_sync import (
    update_architecture_from_prompt,
    register_untracked_prompts,
    parse_prompt_tags,
    validate_architecture_modules,
)

def run_example() -> None:
    """
    A complete, runnable example demonstrating how to use the architecture_sync module
    to extract PDD metadata tags from prompt files and sync them into architecture.json.

    Inputs:
        None (creates mock directories and files in './output' for illustration)

    Outputs:
        Prints sync actions, extracted metadata, and validation results to the console.
    """
    # 1. Setup mock workspace inside './output'
    base_dir = Path("./output").resolve()
    prompts_dir = base_dir / "prompts"
    architecture_path = base_dir / "architecture.json"

    prompts_dir.mkdir(parents=True, exist_ok=True)

    print(f"[Setup] Creating mock environment in: {base_dir}")

    # Create a mock architecture.json containing one registered module
    mock_arch = {
        "modules": [
            {
                "filename": "llm_invoke_python.prompt",
                "filepath": "pdd/llm_invoke.py",
                "reason": "Old description to be updated",
                "dependencies": [],
                "tags": ["module", "python"],
                "interface": {
                    "type": "module",
                    "module": {
                        "functions": []
                    }
                }
            }
        ]
    }
    architecture_path.write_text(json.dumps(mock_arch, indent=2), encoding="utf-8")

    # Create a mock prompt file with explicit PDD metadata tags
    mock_prompt_content = """---
author: Developer
type: prompt
---
<pdd-reason>Provides unified LLM invocation across all PDD operations.</pdd-reason>

<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {
        "name": "invoke_llm",
        "signature": "(prompt_text: str) -> str"
      }
    ]
  }
}
</pdd-interface>

<pdd-dependency>config_helper_python.prompt</pdd-dependency>

% Content Section starts here
This is the actual prompt text instructions for the LLM...
"""
    prompt_file = prompts_dir / "llm_invoke_python.prompt"
    prompt_file.write_text(mock_prompt_content, encoding="utf-8")

    # 2. Extract PDD tags directly from prompt content
    print("\n--- Step 1: Parsing PDD metadata tags directly from prompt content ---")
    parsed_tags = parse_prompt_tags(mock_prompt_content)
    print(f"Parsed Reason: {parsed_tags['reason']}")
    print(f"Parsed Dependencies: {parsed_tags['dependencies']}")
    print(f"Parsed Interface: {json.dumps(parsed_tags['interface'], indent=2)}")

    # 3. Synchronize prompt file changes back to architecture.json
    print("\n--- Step 2: Syncing specific prompt file to architecture.json ---")
    sync_result = update_architecture_from_prompt(
        prompt_filename="llm_invoke_python.prompt",
        prompts_dir=prompts_dir,
        architecture_path=architecture_path,
        dry_run=False
    )

    print(f"Sync Success: {sync_result['success']}")
    print(f"Fields Updated: {list(sync_result['changes'].keys())}")
    if 'reason' in sync_result['changes']:
        print(f"  Reason change: '{sync_result['changes']['reason']['old']}' -> '{sync_result['changes']['reason']['new']}'")

    # 4. Auto-register any untracked prompt files that contain PDD tags
    print("\n--- Step 3: Registering untracked prompts with PDD tags ---")
    # Let's create an untracked prompt file
    untracked_prompt = prompts_dir / "config_helper_python.prompt"
    untracked_prompt.write_text("""<pdd-reason>Helper for parsing config files.</pdd-reason>
<pdd-interface>{\"type\": \"module\"}</pdd-interface>\n""", encoding="utf-8")

    reg_result = register_untracked_prompts(
        prompts_dir=prompts_dir,
        architecture_path=architecture_path,
        dry_run=False
    )
    print(f"Auto-registered prompts: {reg_result['registered']}")
    print(f"Skipped prompts: {reg_result['skipped']}")

    # 5. Validate the resulting architecture
    print("\n--- Step 4: Validating updated architecture.json ---")
    updated_arch = json.loads(architecture_path.read_text(encoding="utf-8"))
    modules = updated_arch.get("modules", [])
    validation_result = validate_architecture_modules(modules)
    print(f"Architecture valid: {validation_result['valid']}")
    print(f"Validation Errors: {validation_result['errors']}")
    print(f"Validation Warnings: {validation_result['warnings']}")

if __name__ == "__main__":
    run_example()