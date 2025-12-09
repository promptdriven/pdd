"""
Command registration module.
"""
import click

from .generate import generate, test, example
from .fix import fix
from .modify import split, change, update
from .maintenance import sync, auto_deps, setup
from .analysis import detect_change, conflicts, bug, crash, trace
from .misc import preprocess
from .report import report_core
from .templates import templates_group
from .utility import install_completion_cmd, verify

def register_commands(cli: click.Group) -> None:
    """Register all subcommands with the main CLI group."""
    cli.add_command(generate)
    cli.add_command(test)
    cli.add_command(example)
    cli.add_command(fix)
    cli.add_command(split)
    cli.add_command(change)
    cli.add_command(update)
    cli.add_command(sync)
    cli.add_command(auto_deps)
    cli.add_command(setup)
    cli.add_command(detect_change)
    cli.add_command(conflicts)
    cli.add_command(bug)
    cli.add_command(crash)
    cli.add_command(trace)
    cli.add_command(preprocess)
    cli.add_command(report_core)
    cli.add_command(install_completion_cmd, name="install_completion")
    cli.add_command(verify)
    
    # Register templates group directly to commands dict to handle nesting if needed,
    # or just add_command works for groups too.
    # The original code did: cli.commands["templates"] = templates_group
    # Using add_command is cleaner if it works for the structure.
    cli.add_command(templates_group)
