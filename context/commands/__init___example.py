#!/usr/bin/env python3
"""Example demonstrating how to use the command registration module.

This module shows how to use `register_commands` to set up a Click CLI
with all PDD subcommands properly registered.

The `register_commands` function:
    - Input: cli (click.Group) - The main Click group to register commands with
    - Output: None - Commands are registered in-place on the cli group

Registered command categories:
    - Generation: generate, test, example
    - Fixing: fix
    - Modification: split, change, update
    - Maintenance: sync, auto_deps, setup
    - Analysis: detect_change, conflicts, bug, crash, trace
    - Miscellaneous: preprocess
    - Utility: install_completion, verify
    - Templates: templates (command group)
"""

import click
from pdd.commands import register_commands


# Example 1: Basic CLI setup with all commands registered
@click.group()
@click.version_option(version="1.0.0", prog_name="pdd")
def cli():
    """PDD - Python Development Driver CLI.
    
    A comprehensive CLI tool for code generation, analysis, and maintenance.
    """
    pass


# Register all subcommands with the main CLI group
register_commands(cli)


# Example 2: Inspecting registered commands
def list_registered_commands():
    """List all commands that were registered with the CLI.
    
    Returns:
        dict: Dictionary mapping command names to their Click command objects.
    """
    return cli.commands


# Example 3: Creating a custom CLI with subset of commands
@click.group()
def custom_cli():
    """Custom CLI with all PDD commands."""
    pass


def setup_custom_cli():
    """Demonstrate setting up a custom CLI with registered commands.
    
    This shows how register_commands adds all subcommands to any Click group.
    """
    register_commands(custom_cli)
    return custom_cli


if __name__ == "__main__":
    # Display registered commands
    print("PDD CLI - Registered Commands")
    print("=" * 40)
    
    commands = list_registered_commands()
    
    # Group commands by category for display
    categories = {
        "Generation": ["generate", "test", "example"],
        "Fixing": ["fix"],
        "Modification": ["split", "change", "update"],
        "Maintenance": ["sync", "auto-deps", "setup"],
        "Analysis": ["detect-change", "conflicts", "bug", "crash", "trace"],
        "Miscellaneous": ["preprocess"],
        "Utility": ["install-completion", "verify"],
        "Templates": ["templates"],
    }
    
    for category, cmd_names in categories.items():
        print(f"\n{category}:")
        for name in cmd_names:
            # Handle both hyphenated and underscored names
            lookup_name = name.replace("-", "_") if name.replace("-", "_") in commands else name
            if lookup_name not in commands:
                lookup_name = name.replace("_", "-")
            
            if lookup_name in commands:
                cmd = commands[lookup_name]
                help_text = cmd.help or "No description"
                # Truncate long help text
                if len(help_text) > 50:
                    help_text = help_text[:47] + "..."
                print(f"  - {name}: {help_text}")
            else:
                print(f"  - {name}: (not found)")
    
    print("\n" + "=" * 40)
    print(f"Total commands registered: {len(commands)}")
    
    # Show how to invoke the CLI
    print("\nUsage Examples:")
    print("  pdd generate --help      # Show generate command options")
    print("  pdd fix --help           # Show fix command options")
    print("  pdd templates --help     # Show templates group options")
    print("  pdd verify --help        # Show verify command options")
    
    # Uncomment to actually run the CLI:
    # cli()
