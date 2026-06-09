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
    get_architecture_entry_for_prompt,
    has_pdd_tags,
    parse_prompt_tags,
    sync_all_prompts_to_architecture,
    update_architecture_from_prompt,
    validate_dependencies,
    validate_interface_structure,
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


def example_parse_tags():
    """Parse PDD metadata tags from prompt content."""
    prompt_content = """
<pdd-reason>Handles user authentication and session management</pdd-reason>

<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "authenticate", "signature": "(username: str, password: str) -> Optional[User]", "returns": "Optional[User]"},
      {"name": "create_session", "signature": "(user: User) -> str", "returns": "str"}
    ]
  }
}
</pdd-interface>

<pdd-dependency>database_python.prompt</pdd-dependency>
<pdd-dependency>config_python.prompt</pdd-dependency>

% Role & Scope
Your goal is to implement user authentication...
"""

    tags = parse_prompt_tags(prompt_content)

    print(f"Reason: {tags['reason']}")
    print(f"Interface type: {tags['interface']['type']}")
    print(f"Dependencies: {tags['dependencies']}")
    print(f"Has dependency tags: {tags['has_dependency_tags']}")

    return tags


def example_update_single_prompt():
    """Update architecture.json from a single prompt file's PDD tags."""
    result = update_architecture_from_prompt(
        prompt_filename="user_service_python.prompt",
        prompts_dir=Path("prompts"),
        architecture_path=Path("architecture.json"),
        dry_run=True,
    )

    if result["success"]:
        if result["updated"]:
            print("Changes detected:")
            for field, change in result["changes"].items():
                print(f"  {field}: {change['old']} -> {change['new']}")
        else:
            print("No changes needed")
    else:
        print(f"Error: {result['error']}")

    return result


def example_sync_all():
    """Sync all prompt files to architecture.json."""
    result = sync_all_prompts_to_architecture(
        prompts_dir=Path("prompts"),
        architecture_path=Path("architecture.json"),
        dry_run=True,
    )

    print(f"Success: {result['success']}")
    print(f"Updated: {result['updated_count']} modules")
    print(f"Skipped: {result['skipped_count']} modules")

    if result["errors"]:
        print("Errors:")
        for error in result["errors"]:
            print(f"  - {error}")

    return result


def example_validate_dependencies():
    """Validate that all dependencies exist and are unique."""
    dependencies = [
        "database_python.prompt",
        "config_python.prompt",
        "missing_file.prompt",
        "database_python.prompt",
    ]

    result = validate_dependencies(dependencies, prompts_dir=Path("prompts"))

    print(f"Valid: {result['valid']}")
    print(f"Missing files: {result['missing']}")
    print(f"Duplicates: {result['duplicates']}")

    return result


def example_validate_interface():
    """Validate interface JSON structure."""
    valid_interface = {
        "type": "module",
        "module": {
            "functions": [
                {
                    "name": "process",
                    "signature": "(data: Dict) -> Dict",
                    "returns": "Dict",
                }
            ]
        },
    }

    result = validate_interface_structure(valid_interface)
    print(f"Valid interface: {result['valid']}")

    invalid_interface = {
        "type": "module"
    }

    result = validate_interface_structure(invalid_interface)
    print(f"Invalid interface errors: {result['errors']}")

    return result


def example_generate_tags():
    """Generate PDD tags from an architecture.json entry."""
    arch_entry = {
        "filename": "user_service_python.prompt",
        "filepath": "pdd/user_service.py",
        "reason": "Handles user authentication and profile management",
        "interface": {
            "type": "module",
            "module": {
                "functions": [
                    {
                        "name": "authenticate",
                        "signature": "(username, password)",
                        "returns": "User",
                    }
                ]
            },
        },
        "dependencies": ["database_python.prompt", "config_python.prompt"],
    }

    tags = generate_tags_from_architecture(arch_entry)
    print("Generated tags:")
    print(tags)

    return tags


def example_check_existing_tags():
    """Check if a prompt already has PDD tags before injecting derived metadata."""
    prompt_with_tags = """
<pdd-reason>Existing reason</pdd-reason>

% Role & Scope
...
"""

    prompt_without_tags = """
% Role & Scope
Your goal is to implement...
"""

    print(f"Prompt with tags: {has_pdd_tags(prompt_with_tags)}")
    print(f"Prompt without tags: {has_pdd_tags(prompt_without_tags)}")

    return has_pdd_tags(prompt_with_tags), has_pdd_tags(prompt_without_tags)


def example_get_entry():
    """Look up architecture entry by prompt filename."""
    entry = get_architecture_entry_for_prompt(
        "llm_invoke_python.prompt",
        architecture_path=Path("architecture.json"),
    )

    if entry:
        print(f"Found entry for: {entry['filename']}")
        print(f"Reason: {entry.get('reason', 'N/A')}")
    else:
        print("No entry found")

    return entry


def example_inject_tags_workflow():
    """Generate and inject PDD tags into a prompt that does not have them yet."""
    prompt_filename = "my_module_python.prompt"
    prompt_content = """
% Role & Scope
Your goal is to implement a data processor...

% Requirements
1. Process input data
2. Return results
"""

    if has_pdd_tags(prompt_content):
        print("Prompt already has PDD tags, skipping injection")
        return prompt_content

    arch_entry = get_architecture_entry_for_prompt(prompt_filename)

    if not arch_entry:
        print(f"No architecture entry found for {prompt_filename}")
        return prompt_content

    tags = generate_tags_from_architecture(arch_entry)

    if tags:
        final_content = tags + "\n\n" + prompt_content
        print("Tags injected successfully!")
        return final_content

    return prompt_content


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
