# Curated usage example for PDD prompts that include cli_status.
# Shows the canonical pattern for from_context + StatusReporter primitives.
# This file is manually maintained — do not regenerate via pdd sync.

import asyncio
import click

from pdd.cli_status import from_context


@click.command("example")
@click.pass_context
def example_command(ctx):
    """Illustrates the five StatusReporter primitives in a realistic flow."""
    status = from_context(ctx, command="pdd example")

    # START — first line of output, names the operation beginning.
    status.start("launching example operation")

    # STEP — a human-readable sub-step within the operation.
    status.step("checking prerequisites")

    # WAITING — blocks on slow IO/network/LLM; shows a spinner on TTYs.
    try:
        with status.waiting("fetching remote data", on="network"):
            result = asyncio.run(_fetch())
    except Exception as exc:
        # FAILURE — names what failed, why, and what to try next.
        status.failure(
            "fetching remote data",
            reason=str(exc),
            suggestions=[
                "check network connectivity",
                "run with --local-only to skip remote calls",
            ],
        )
        raise

    # SUCCESS — operation finished; optional next_step guides the user forward.
    status.success(
        f"fetched {len(result)} items",
        next_step="review the output, then run `pdd sync`",
    )


async def _fetch():
    """Placeholder for an async network call."""
    await asyncio.sleep(0)
    return []
