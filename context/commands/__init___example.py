#!/usr/bin/env python3
"""Example demonstrating how to use the command registration module.

This module shows how to use ``register_commands`` to set up a Click CLI
with all PDD subcommands properly registered.

The ``register_commands`` function:
    - Input:  cli (click.Group) — the main Click group to register commands with.
    - Output: None — commands are registered in-place on the ``cli`` group.

Registered command categories (per the spec):
    - Generation:     generate, test, example          (.generate)
    - Fixing:         fix                              (.fix)
    - Modification:   split, change, update            (.modify)
    - Maintenance:    sync, auto-deps, setup,
                      sync_code, metadata              (.maintenance)
    - Checkup:        checkup                          (.checkup)
    - Analysis:       detect_change, conflicts, bug,
                      crash, trace                     (.analysis)
    - Connect:        connect                          (.connect)
    - Auth:           auth                             (.auth)
    - Misc:           preprocess                       (.misc)
    - Sessions:       sessions                         (.sessions)
    - Report:         report-core                      (.report)
    - Templates:      templates                        (.templates)
    - Utility:        install_completion, verify       (.utility)
    - Which:          which                            (.which)
    - Firecrawl:      firecrawl-cache                  (.firecrawl)
"""
from __future__ import annotations

import os
import sys

# Make this script runnable regardless of working directory by inserting
# the project root onto sys.path so ``from pdd.commands import ...`` resolves
# to the local source tree rather than any globally-installed copy.
_PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if _PROJECT_ROOT not in sys.path:
    sys.path.insert(0, _PROJECT_ROOT)

# Drop any pre-imported pdd modules so we pick up the local sources.
for _name in list(sys.modules):
    if _name == "pdd" or _name.startswith("pdd."):
        del sys.modules[_name]

import click  # noqa: E402

from pdd.commands import register_commands  # noqa: E402


def build_cli() -> click.Group:
    """Return a fresh Click group with every PDD subcommand registered."""

    @click.group()
    @click.version_option(version="1.0.0", prog_name="pdd")
    def cli() -> None:
        """PDD — Prompt-Driven Development CLI."""

    register_commands(cli)
    return cli


def main() -> int:
    cli = build_cli()
    print("PDD CLI — Registered Commands")
    print("=" * 40)
    print()

    registered = sorted(cli.commands.keys())
    for name in registered:
        cmd = cli.commands[name]
        help_text = (cmd.help or "").strip().splitlines()[0] if cmd.help else "(no help)"
        if len(help_text) > 60:
            help_text = help_text[:57] + "..."
        print(f"  - {name}: {help_text}")

    print()
    print("=" * 40)
    print(f"Total commands registered: {len(registered)}")

    expected_names = {
        "generate", "test", "example",
        "fix",
        "split", "change", "update",
        "sync", "auto-deps", "setup", "metadata",
        "checkup",
        "conflicts", "bug", "crash", "trace",
        "connect",
        "auth",
        "preprocess",
        "sessions",
        "report-core",
        "templates",
        "install_completion", "verify",
        "which",
        "firecrawl-cache",
    }
    missing = sorted(expected_names - set(registered))
    print()
    if missing:
        print(f"Missing expected names: {missing}")
    else:
        print("All expected names are registered.")

    print()
    print("Sample usage:")
    print("  pdd generate --help     # show generate command options")
    print("  pdd metadata tags PROMPT  # synthesize PDD metadata tags")
    print("  pdd templates --help    # show templates group options")

    return 0


if __name__ == "__main__":
    sys.exit(main())
