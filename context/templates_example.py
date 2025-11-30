#!/usr/bin/env python3
"""
Example usage of the pdd.commands.templates module.

This module provides CLI commands for managing PDD templates:
- `templates list`: List available templates with optional filtering
- `templates show`: Display detailed information about a specific template
- `templates copy`: Copy a template to a destination directory

The templates command group is designed to be used with Click CLI framework
and integrates with the pdd template_registry for template discovery and management.

Note: This example demonstrates programmatic invocation of the Click commands.
In normal usage, these commands are invoked via the `pdd` CLI:
    pdd templates list
    pdd templates show <name>
    pdd templates copy <name> --to <destination>
"""

import os
import sys
from pathlib import Path
from click.testing import CliRunner

# Import the templates command group from the pdd.commands.templates module
from pdd.commands.templates import templates_group


def example_list_templates():
    """
    Example: List all available templates.
    
    This invokes `pdd templates list` which displays all registered templates
    with their names, versions, descriptions, and tags.
    
    CLI equivalent:
        pdd templates list
        pdd templates list --json
        pdd templates list --filter frontend
    
    Returns:
        None - Output is printed to console
    """
    runner = CliRunner()
    
    print("=" * 60)
    print("Example 1: List all templates (text format)")
    print("=" * 60)
    result = runner.invoke(templates_group, ["list"])
    print(result.output)
    
    print("\n" + "=" * 60)
    print("Example 2: List templates as JSON")
    print("=" * 60)
    result = runner.invoke(templates_group, ["list", "--json"])
    print(result.output)
    
    print("\n" + "=" * 60)
    print("Example 3: List templates filtered by tag 'architecture'")
    print("=" * 60)
    result = runner.invoke(templates_group, ["list", "--filter", "architecture"])
    print(result.output)


def example_show_template():
    """
    Example: Show detailed information about a specific template.
    
    This invokes `pdd templates show <name>` which displays:
    - Template summary (name, description, version, tags, language, output, path)
    - Variables with their types, requirements, defaults, and examples
    - Usage examples with copyable commands
    - Discovery settings (if configured)
    - Output schema (if defined)
    - Notes (if any)
    
    Parameters:
        name (str): The template name to show details for
                   (e.g., "architecture/architecture_json")
    
    CLI equivalent:
        pdd templates show architecture/architecture_json
    
    Returns:
        None - Output is printed to console as Rich-formatted tables
    """
    runner = CliRunner()
    
    print("=" * 60)
    print("Example: Show template details")
    print("=" * 60)
    # Show the built-in architecture template
    result = runner.invoke(templates_group, ["show", "architecture/architecture_json"])
    print(result.output)


def example_copy_template():
    """
    Example: Copy a template to a destination directory.
    
    This invokes `pdd templates copy <name> --to <destination>` which copies
    the specified template file to the target directory for customization.
    
    Parameters:
        name (str): The template name to copy
                   (e.g., "architecture/architecture_json")
        dest_dir (str): Destination directory path where the template
                       will be copied. Directory will be created if needed.
    
    CLI equivalent:
        pdd templates copy architecture/architecture_json --to ./output/prompts/
    
    Returns:
        None - Prints success message with the destination path
    """
    runner = CliRunner()
    
    # Create output directory for the example
    output_dir = Path("./output/prompts")
    output_dir.mkdir(parents=True, exist_ok=True)
    
    print("=" * 60)
    print("Example: Copy template to local directory")
    print("=" * 60)
    result = runner.invoke(
        templates_group, 
        ["copy", "architecture/architecture_json", "--to", str(output_dir)]
    )
    print(result.output)
    
    # Show what was copied
    if result.exit_code == 0:
        print("\nCopied template files:")
        for f in output_dir.glob("*.prompt"):
            print(f"  - {f.name}")


def main():
    """
    Main function demonstrating all templates command examples.
    
    The templates command group provides three subcommands:
    
    1. `list` - List available templates
       Options:
         --json: Output as JSON instead of formatted text
         --filter TAG: Filter templates by tag (e.g., "frontend", "architecture")
    
    2. `show` - Show detailed template information
       Arguments:
         NAME: Template name (e.g., "architecture/architecture_json")
       
       Displays rich-formatted tables with:
         - Template Summary: name, description, version, tags, language, output, path
         - Variables: name, required (Yes/No), type, description, default/examples
         - Usage: grouped command examples
         - Discover: file discovery settings
         - Output Schema: JSON schema for template output
         - Notes: additional template notes
    
    3. `copy` - Copy template to destination
       Arguments:
         NAME: Template name to copy
       Options:
         --to DEST_DIR: Required. Destination directory path
    """
    print("PDD Templates Command Examples")
    print("=" * 60)
    print("\nThis module manages packaged and project templates.")
    print("Templates are reusable prompt files with YAML front matter")
    print("containing metadata, variables, and usage examples.\n")
    
    # Run examples
    example_list_templates()
    print("\n")
    
    example_show_template()
    print("\n")
    
    example_copy_template()
    
    print("\n" + "=" * 60)
    print("Examples completed successfully!")
    print("=" * 60)


if __name__ == "__main__":
    main()
