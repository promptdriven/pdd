#!/usr/bin/env python3
"""Example demonstrating bidirectional architecture synchronization using PDD tags.

This script demonstrates how to:
1. Parse PDD tags (<pdd-reason>, <pdd-interface>, <pdd-dependency>) from prompt content.
2. Update an architecture.json file using metadata extracted from a prompt file.
3. Generate prompt tags from an architecture entry (reverse sync direction).
"""

from __future__ import annotations

import json
import os
from pathlib import Path
from rich.console import Console

# Import the architecture_sync module
from pdd.architecture_sync import (
    generate_tags_from_architecture,
    parse_prompt_tags,
    update_architecture_from_prompt,
)

console = Console()


def setup_temporary_workspace() -> tuple[Path, Path]:
    """Sets up a mock workspace in `./output` with a prompt file and architecture.json."""
    output_dir = Path("./output").resolve()
    prompts_dir = output_dir / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)

    architecture_path = output_dir / "architecture.json"

    # 1. Create a mock prompt file with PDD tags
    prompt_content = """---
title: LLM Invocation Module
---
% This is a system preamble line
<pdd-reason>Provides unified LLM invocation and token tracking.</pdd-reason>
<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {
        "name": "invoke_llm",
        "signature": "(prompt: str, model: str = 'gpt-4') -> str"
      }
    ]
  }
}
</pdd-interface>
<pdd-dependency>token_counter_python.prompt</pdd-dependency>

Here starts the actual prompt prose instructions...
"""
    prompt_file = prompts_dir / "llm_invoke_python.prompt"
    prompt_file.write_text(prompt_content, encoding="utf-8")

    # 2. Create a base architecture.json file containing an entry for the prompt
    base_architecture = {
        "modules": [
            {
                "filename": "llm_invoke_python.prompt",
                "filepath": "pdd/llm_invoke.py",
                "reason": "Old outdated description",
                "dependencies": [],
                "interface": {"type": "module", "module": {"functions": []}},
            }
        ]
    }
    architecture_path.write_text(
        json.dumps(base_architecture, indent=2), encoding="utf-8"
    )

    return prompts_dir, architecture_path


def main() -> None:
    # 1. Initialize our workspace
    prompts_dir, architecture_path = setup_temporary_workspace()
    console.print(
        f"[bold green]Workspace initialized under:[/bold green] {prompts_dir.parent}\n"
    )

    # 2. Parse tags directly from prompt content
    prompt_file = prompts_dir / "llm_invoke_python.prompt"
    prompt_content = prompt_file.read_text(encoding="utf-8")

    console.print("[bold blue]1. Parsing PDD Metadata Tags from Prompt File...[/bold blue]")
    parsed_metadata = parse_prompt_tags(prompt_content)
    console.print(f"Parsed Reason: [yellow]'{parsed_metadata['reason']}'[/yellow]")
    console.print(f"Parsed Dependencies: [yellow]{parsed_metadata['dependencies']}[/yellow]")
    console.print("Parsed Interface Struct:")
    console.print(parsed_metadata["interface"])
    console.print()

    # 3. Synchronize prompt metadata to architecture.json
    console.print("[bold blue]2. Syncing Prompt Tags -> architecture.json...[/bold blue]")
    sync_result = update_architecture_from_prompt(
        prompt_filename="llm_invoke_python.prompt",
        prompts_dir=prompts_dir,
        architecture_path=architecture_path,
        dry_run=False,
    )

    console.print(f"Sync success: [green]{sync_result['success']}[/green]")
    console.print(f"Updated fields: [yellow]{list(sync_result['changes'].keys())}[/yellow]")
    console.print()

    # Read updated architecture.json to verify
    updated_arch = json.loads(architecture_path.read_text(encoding="utf-8"))
    console.print("[bold green]Updated architecture.json Entry:[/bold green]")
    console.print(updated_arch["modules"][0])
    console.print()

    # 4. Generate XML PDD Tags from Architecture Entry (Reverse Direction)
    console.print("[bold blue]3. Generating PDD Tags from Architecture Entry...[/bold blue]")
    mock_arch_entry = {
        "reason": "Database migration helper",
        "dependencies": ["db_connection_python.prompt"],
        "interface": {
            "type": "module",
            "module": {
                "functions": [
                    {
                        "name": "run_migrations",
                        "signature": "() -> None"
                    }
                ]
            }
        }
    }
    generated_xml = generate_tags_from_architecture(mock_arch_entry)
    console.print("[yellow]Generated XML Output to Prepend to a New Prompt:[/yellow]")
    console.print(generated_xml)


if __name__ == "__main__":
    main()