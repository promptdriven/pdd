"""Detect CLI invocations that must keep stdout machine-parseable (JSON only).

This is a dependency-light leaf module so both the early ``--quiet`` pre-parse in
``pdd/cli.py`` (which runs before heavy imports) and ``pdd/core/cli.py`` can share
one definition. Keeping a single source of truth avoids the two call sites drifting
out of sync on which ``--json`` invocations need clean stdout.
"""
from __future__ import annotations

from typing import List

# ``pdd checkup <subcommand> --json`` and ``pdd contracts check --json`` emit
# structured JSON on stdout.
_CHECKUP_JSON_SUBCOMMANDS = (
    "lint",
    "contract",
    "contracts",
    "coverage",
    "gate",
    "drift",
)

# Subcommands that are NOT a unified source-set prompt target; used to keep
# ``pdd checkup lint --json`` etc. from being treated as a prompt-target run.
_CHECKUP_NON_SOURCE_SET_SUBCOMMANDS = frozenset(
    {
        "lint",
        "contract",
        "contracts",
        "coverage",
        "gate",
        "drift",
        "snapshot",
        "simplify",
    }
)


def is_checkup_subcommand_json_invocation(arguments: List[str]) -> bool:
    """Return True for ``pdd checkup <subcommand> --json`` machine output."""
    if "--json" not in arguments:
        return False
    pairs = set(zip(arguments, arguments[1:]))
    if any(("checkup", sub) in pairs for sub in _CHECKUP_JSON_SUBCOMMANDS):
        return True
    return ("contracts", "check") in pairs


def is_checkup_source_set_json_invocation(arguments: List[str]) -> bool:
    """Return True for ``pdd checkup <prompt-target> --json`` machine output."""
    if "--json" not in arguments:
        return False
    try:
        checkup_idx = arguments.index("checkup")
    except ValueError:
        return False
    if checkup_idx + 1 >= len(arguments):
        return False
    next_arg = arguments[checkup_idx + 1]
    if next_arg.startswith("-"):
        return False
    if next_arg in _CHECKUP_NON_SOURCE_SET_SUBCOMMANDS:
        return False
    return True


def is_context_json_invocation(arguments: List[str]) -> bool:
    """Return True for ``pdd context <prompt> --json`` machine output.

    ``pdd context --json`` emits a JSON context-usage audit that dashboards
    parse, so its stdout must stay payload-only. Exclude the case where
    ``context`` is the value of the global ``--context`` option (e.g.
    ``pdd --context context generate --json``) rather than the subcommand.
    """
    if "--json" not in arguments:
        return False
    for index, arg in enumerate(arguments):
        if arg == "context" and (index == 0 or arguments[index - 1] != "--context"):
            return True
    return False


def is_machine_json_invocation(arguments: List[str]) -> bool:
    """Return whether stdout must remain machine-parseable JSON only."""
    return (
        is_checkup_subcommand_json_invocation(arguments)
        or is_checkup_source_set_json_invocation(arguments)
        or is_context_json_invocation(arguments)
    )
