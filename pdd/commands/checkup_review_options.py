"""Shared ``--review`` option for local ``pdd checkup`` subcommands."""
from __future__ import annotations

from typing import Callable

import click


def review_option(func: Callable) -> Callable:
    """Attach ``--review off|explain`` to a checkup subcommand."""
    return click.option(
        "--review",
        type=click.Choice(["off", "explain"], case_sensitive=False),
        default="off",
        show_default=True,
        help=(
            "Advisory LLM pass after deterministic checks (read-only; "
            "does not change exit code). Use 'explain' for coaching hints."
        ),
    )(func)


def reject_review_on_snapshot(review: str) -> None:
    """Reject ``--review`` on ``pdd checkup snapshot`` (deterministic-only)."""
    if review != "off":
        raise click.UsageError(
            "--review is not supported on pdd checkup snapshot (deterministic policy only)."
        )


