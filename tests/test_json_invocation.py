"""Parity tests for machine-JSON invocation detection across CLI entry points."""
from __future__ import annotations

import pytest

from pdd.json_invocation import is_machine_json_invocation


@pytest.mark.parametrize(
    "arguments,expected",
    [
        (["pdd", "checkup", "lint", "foo.prompt", "--json"], True),
        (["pdd", "checkup", "contract", "foo.prompt", "--json"], True),
        (["pdd", "checkup", "coverage", "foo.prompt", "--json"], True),
        (["pdd", "checkup", "gate", "devunit", "--json"], True),
        (["pdd", "checkup", "drift", "devunit", "--json"], True),
        (["pdd", "contracts", "check", "foo.prompt", "--json"], True),
        # Unified source-set prompt target.
        (["pdd", "checkup", "prompts/foo_python.prompt", "--json"], True),
        (["pdd", "checkup", "refund_payment", "--json"], True),
        # No --json => not machine output.
        (["pdd", "checkup", "prompts/foo_python.prompt"], False),
        (["pdd", "generate", "foo.prompt", "--json"], False),
        # checkup with no target.
        (["pdd", "checkup", "--json"], False),
    ],
)
def test_is_machine_json_invocation(arguments: list[str], expected: bool) -> None:
    assert is_machine_json_invocation(arguments) is expected


def test_cli_entry_points_share_one_definition() -> None:
    """pdd/cli.py pre-parse and core/cli.py must use the same detector."""
    from pdd.cli import _is_structured_json_invocation
    from pdd.core.cli import _is_machine_json_invocation

    assert _is_structured_json_invocation is is_machine_json_invocation
    assert _is_machine_json_invocation is is_machine_json_invocation

    # Regression: drift and unified source-set were previously missing from the
    # pdd/cli.py pre-parse, causing inconsistent quiet behavior by import path.
    for args in (
        ["pdd", "checkup", "drift", "devunit", "--json"],
        ["pdd", "checkup", "prompts/foo_python.prompt", "--json"],
    ):
        assert _is_structured_json_invocation(args) == _is_machine_json_invocation(args)
        assert _is_structured_json_invocation(args) is True
