# pdd/cli.py
"""
Command Line Interface (CLI) for the PDD (Prompt-Driven Development) tool.

This module provides the main CLI functionality for PDD, including commands for
generating code, tests, fixing issues, and managing prompts.
"""
from __future__ import annotations

from .core.cli import cli
from .commands import register_commands

# Register all commands
register_commands(cli)

# Re-export commonly used items for backward compatibility
from .commands.templates import templates_group
from .auto_update import auto_update
from .code_generator_main import code_generator_main
from .context_generator_main import context_generator_main
from .cmd_test_main import cmd_test_main
from .fix_main import fix_main
from .split_main import split_main
from .change_main import change_main
from .update_main import update_main
from .sync_main import sync_main
from .auto_deps_main import auto_deps_main
from .detect_change_main import detect_change_main
from .conflicts_main import conflicts_main
from .bug_main import bug_main
from .crash_main import crash_main
from .trace_main import trace_main
from .preprocess_main import preprocess_main
from .construct_paths import construct_paths
from .fix_verification_main import fix_verification_main
from .core.errors import console
from .install_completion import install_completion
from .core.utils import _should_show_onboarding_reminder
from .core.cli import process_commands
import subprocess

if __name__ == "__main__":
    cli()
