"""
Example usage of the architecture_sync module for bidirectional sync
between architecture.json and prompt files using PDD metadata tags.
"""

from pathlib import Path
from pdd.architecture_sync import (
    parse_prompt_tags,
    update_architecture_from_prompt,
    sync_all_prompts_to_architecture,
    validate_dependencies,
    validate_interface_structure,
    get_architecture_entry_for_prompt,
    has_pdd_tags,
    generate_tags_from_architecture,
)


# --- Example 1: Parse PDD tags from prompt content ---
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


# --- Example 2: Update architecture.json from a single prompt ---
def example_update_single_prompt():
    """Update architecture.json from a single prompt file's PDD tags."""
    result = update_architecture_from_prompt(
        prompt_filename="user_service_python.prompt",
        prompts_dir=Path("prompts"),
        architecture_path=Path("architecture.json"),
        dry_run=True  # Preview changes without writing
    )

    if result['success']:
        if result['updated']:
            print("Changes detected:")
            for field, change in result['changes'].items():
                print(f"  {field}: {change['old']} -> {change['new']}")
        else:
            print("No changes needed")
    else:
        print(f"Error: {result['error']}")

    return result


# --- Example 3: Sync all prompts to architecture.json ---
def example_sync_all():
    """Sync all prompt files to architecture.json."""
    result = sync_all_prompts_to_architecture(
        prompts_dir=Path("prompts"),
        architecture_path=Path("architecture.json"),
        dry_run=True  # Preview changes
    )

    print(f"Success: {result['success']}")
    print(f"Updated: {result['updated_count']} modules")
    print(f"Skipped: {result['skipped_count']} modules")

    if result['errors']:
        print("Errors:")
        for error in result['errors']:
            print(f"  - {error}")

    return result


# --- Example 4: Validate dependencies ---
def example_validate_dependencies():
    """Validate that all dependencies exist and are unique."""
    dependencies = [
        "database_python.prompt",
        "config_python.prompt",
        "missing_file.prompt",  # This will fail
        "database_python.prompt",  # This is a duplicate
    ]

    result = validate_dependencies(dependencies, prompts_dir=Path("prompts"))

    print(f"Valid: {result['valid']}")
    print(f"Missing files: {result['missing']}")
    print(f"Duplicates: {result['duplicates']}")

    return result


# --- Example 5: Validate interface structure ---
def example_validate_interface():
    """Validate interface JSON structure."""
    # Valid module interface
    valid_interface = {
        "type": "module",
        "module": {
            "functions": [
                {"name": "process", "signature": "(data: Dict) -> Dict", "returns": "Dict"}
            ]
        }
    }

    result = validate_interface_structure(valid_interface)
    print(f"Valid interface: {result['valid']}")

    # Invalid interface (missing nested key)
    invalid_interface = {
        "type": "module"
        # Missing "module" key
    }

    result = validate_interface_structure(invalid_interface)
    print(f"Invalid interface errors: {result['errors']}")

    return result


# --- Example 6: Generate tags from architecture entry (reverse direction) ---
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
                    {"name": "authenticate", "signature": "(username, password)", "returns": "User"}
                ]
            }
        },
        "dependencies": ["database_python.prompt", "config_python.prompt"]
    }

    tags = generate_tags_from_architecture(arch_entry)
    print("Generated tags:")
    print(tags)

    return tags


# --- Example 7: Check if prompt already has PDD tags ---
def example_check_existing_tags():
    """Check if a prompt already has PDD tags (to avoid overwriting)."""
    prompt_with_tags = """
<pdd-reason>Existing reason</pdd-reason>

% Role & Scope
...
"""

    prompt_without_tags = """
% Role & Scope
Your goal is to implement...
"""

    print(f"Prompt with tags: {has_pdd_tags(prompt_with_tags)}")  # True
    print(f"Prompt without tags: {has_pdd_tags(prompt_without_tags)}")  # False

    return has_pdd_tags(prompt_with_tags), has_pdd_tags(prompt_without_tags)


# --- Example 8: Get architecture entry for a prompt ---
def example_get_entry():
    """Look up architecture entry by prompt filename."""
    entry = get_architecture_entry_for_prompt(
        "llm_invoke_python.prompt",
        architecture_path=Path("architecture.json")
    )

    if entry:
        print(f"Found entry for: {entry['filename']}")
        print(f"Reason: {entry.get('reason', 'N/A')}")
    else:
        print("No entry found")

    return entry


# --- Example 9: Full workflow - inject tags into new prompt ---
def example_inject_tags_workflow():
    """
    Complete workflow: Check if prompt needs tags, generate and inject them.
    This is what preprocess_main does with --pdd-tags flag.
    """
    prompt_filename = "my_module_python.prompt"
    prompt_content = """
% Role & Scope
Your goal is to implement a data processor...

% Requirements
1. Process input data
2. Return results
"""

    # Step 1: Check if prompt already has tags
    if has_pdd_tags(prompt_content):
        print("Prompt already has PDD tags, skipping injection")
        return prompt_content

    # Step 2: Get architecture entry
    arch_entry = get_architecture_entry_for_prompt(prompt_filename)

    if not arch_entry:
        print(f"No architecture entry found for {prompt_filename}")
        return prompt_content

    # Step 3: Generate and inject tags
    tags = generate_tags_from_architecture(arch_entry)

    if tags:
        final_content = tags + '\n\n' + prompt_content
        print("Tags injected successfully!")
        return final_content

    return prompt_content


if __name__ == "__main__":
    print("=== Architecture Sync Examples ===\n")

    print("1. Parse PDD tags:")
    example_parse_tags()
    print()

    print("5. Validate interface:")
    example_validate_interface()
    print()

    print("6. Generate tags from architecture:")
    example_generate_tags()
    print()

    print("7. Check existing tags:")
    example_check_existing_tags()
    print()
