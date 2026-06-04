"""``pdd checkup prompt`` — unified prompt-space source-set health."""
from __future__ import annotations

import sys
from typing import Optional, Tuple

import click

from ..checkup_prompt_main import run_checkup_prompt
from ..core.errors import handle_error
from ..core.utils import echo_model_line
from ..track_cost import track_cost


@click.command("checkup-prompt")
@click.argument("target", required=True)
@click.option(
    "--explain",
    is_flag=True,
    default=False,
    help="Read-only LLM advisory on deterministic finding IDs; non-fatal.",
)
@click.option(
    "--interactive",
    is_flag=True,
    default=False,
    help="Enable interactive human-approval flow (required with --apply).",
)
@click.option(
    "--apply",
    "apply_patches",
    is_flag=True,
    default=False,
    help="Suggest patches and apply only after per-patch human approval.",
)
@click.option(
    "--strict",
    is_flag=True,
    default=False,
    help="Treat lint/contract warnings as errors in the deterministic report.",
)
@click.pass_context
@track_cost
def checkup_prompt_cmd(  # pylint: disable=too-many-arguments
    ctx: click.Context,
    target: str,
    explain: bool,
    interactive: bool,
    apply_patches: bool,
    strict: bool,
) -> Optional[Tuple[str, float, str]]:
    """
    Unified prompt-space source-set health (Check → Explain → Apply).

    Deterministic engines decide pass/fail. ``--explain`` is optional and
    does not change the exit code. ``--interactive --apply`` is the only
    write path; the LLM never writes files directly.
    """
    if apply_patches and not interactive:
        raise click.UsageError("--apply requires --interactive.")
    if interactive and not sys.stdin.isatty():
        raise click.UsageError("--interactive requires a TTY.")

    obj = ctx.ensure_object(dict)
    quiet = bool(obj.get("quiet", False))
    verbose = bool(obj.get("verbose", False))
    use_cloud = not bool(obj.get("local", False))

    try:
        success, message, cost, model = run_checkup_prompt(
            target,
            explain=explain,
            interactive=interactive,
            apply=apply_patches,
            quiet=quiet,
            verbose=verbose,
            strict=strict,
            strength=float(obj.get("strength", 0.5)),
            temperature=float(obj.get("temperature", 0.0)),
            time=obj.get("time"),
            use_cloud=use_cloud,
        )
    except click.Abort:
        raise
    except click.exceptions.Exit:
        raise
    except click.UsageError:
        raise
    except Exception as exc:  # pylint: disable=broad-exception-caught
        handle_error(exc, "checkup prompt", quiet)
        return None

    if not quiet:
        status = "Success" if success else "Failed"
        click.echo(f"Status: {status}")
        click.echo(f"Message: {message}")
        click.echo(f"Cost: ${cost:.4f}")
        echo_model_line(model)

    if not success:
        raise click.exceptions.Exit(1)
    return message, cost, model
