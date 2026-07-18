# pdd/cli.py
"""
Command Line Interface (CLI) for the PDD (Prompt-Driven Development) tool.

This module provides the main CLI functionality for PDD, including commands for
generating code, tests, fixing issues, and managing prompts.
"""
from __future__ import annotations

from importlib import import_module as _import_module

# Pre-parse --quiet flag from sys.argv BEFORE importing modules that configure
# logging at module level (e.g. llm_invoke.py). This ensures module-level
# logger.info() calls are suppressed when the user passes --quiet.
import os as _os
import sys

# Leaf module (stdlib-only) so this pre-parse stays cheap and shares one
# definition with pdd/core/cli.py instead of drifting out of sync.
from .json_invocation import is_machine_json_invocation as _is_structured_json_invocation


if '--quiet' in sys.argv or _is_structured_json_invocation(sys.argv):
    _os.environ.setdefault('PDD_QUIET', '1')

_DEFAULTS = {
    "__version__": "unknown",
    "EXTRACTION_STRENGTH": 0.5,
    "DEFAULT_STRENGTH": 1.0,
    "DEFAULT_TEMPERATURE": 0.0,
    "DEFAULT_TIME": 0.25,
}


def _bootstrap_package_defaults() -> None:
    """Populate package-level defaults when `pdd` is loaded as a namespace package.

    Some subprocess contexts set `PYTHONPATH` to a parent directory that causes
    `pdd` to resolve as a namespace package. In that mode, `pdd.__init__` is not
    executed, so imports like `from . import DEFAULT_STRENGTH` fail. Seed
    missing attributes here before importing command modules.
    """
    pkg = sys.modules.get(__package__)
    if pkg is None:
        return
    for key, value in _DEFAULTS.items():
        if not hasattr(pkg, key):
            setattr(pkg, key, value)


_bootstrap_package_defaults()

from .core.cli import cli
from .commands import register_commands

# Register all commands
register_commands(cli)

# Re-export commonly used items for backward compatibility, but do not pay for
# command implementations that the current invocation never uses.
_LAZY_EXPORTS = {
    "templates_group": ("commands.templates", "templates_group"),
    "auto_update": ("auto_update", "auto_update"),
    "code_generator_main": ("code_generator_main", "code_generator_main"),
    "context_generator_main": ("context_generator_main", "context_generator_main"),
    "cmd_test_main": ("cmd_test_main", "cmd_test_main"),
    "fix_main": ("fix_main", "fix_main"),
    "split_main": ("split_main", "split_main"),
    "change_main": ("change_main", "change_main"),
    "update_main": ("update_main", "update_main"),
    "sync_main": ("sync_main", "sync_main"),
    "auto_deps_main": ("auto_deps_main", "auto_deps_main"),
    "detect_change_main": ("detect_change_main", "detect_change_main"),
    "conflicts_main": ("conflicts_main", "conflicts_main"),
    "bug_main": ("bug_main", "bug_main"),
    "crash_main": ("crash_main", "crash_main"),
    "trace_main": ("trace_main", "trace_main"),
    "agentic_test_main": ("agentic_test", "agentic_test_main"),
    "preprocess_main": ("preprocess_main", "preprocess_main"),
    "construct_paths": ("construct_paths", "construct_paths"),
    "fix_verification_main": ("fix_verification_main", "fix_verification_main"),
    "install_completion": ("install_completion", "install_completion"),
}

__all__ = [
    "sys", "cli", "register_commands", *sorted(_LAZY_EXPORTS), "console",
    "process_commands",
]


def __getattr__(name: str):
    """Resolve legacy CLI exports on first access."""
    target = _LAZY_EXPORTS.get(name)
    if target is None:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
    module_name, attribute = target
    value = getattr(_import_module(f".{module_name}", __package__), attribute)
    globals()[name] = value
    if name == "templates_group":
        cli.add_command(value, name="templates")
    return value


def __dir__() -> list[str]:
    """Include lazy compatibility exports in interactive discovery."""
    return sorted(set(globals()) | set(_LAZY_EXPORTS))


from .core.errors import console
from .core.utils import _should_show_onboarding_reminder
from .core.cli import process_commands

if __name__ == "__main__":
    cli()
