"""
Checkup command — GitHub issue-driven project health check.
"""
import click
from typing import Optional, Tuple

from ..agentic_checkup import run_agentic_checkup
from ..agentic_sync import _is_github_issue_url
from ..track_cost import track_cost
from ..core.errors import handle_error


@click.command("checkup")
@click.argument("target", required=True)
@click.option(
    "--no-fix",
    is_flag=True,
    default=False,
    help="Report only, don't apply fixes.",
)
@click.option(
    "--timeout-adder",
    type=float,
    default=0.0,
    help="Additional seconds to add to each step's timeout.",
)
@click.option(
    "--no-github-state",
    is_flag=True,
    default=False,
    help="Disable GitHub state persistence.",
)
@click.pass_context
@track_cost
def checkup(
    ctx: click.Context,
    target: str,
    no_fix: bool,
    timeout_adder: float,
    no_github_state: bool,
) -> Optional[Tuple[str, float, str]]:
    """
    Run agentic health checkup on a PDD project from a GitHub issue.

    TARGET is a GitHub issue URL describing what to check.
    """
    if not _is_github_issue_url(target):
        raise click.BadParameter(
            "TARGET must be a GitHub issue URL "
            "(e.g., https://github.com/org/repo/issues/123)",
            param_hint="'TARGET'",
        )

    ctx.ensure_object(dict)
    quiet = ctx.obj.get("quiet", False)
    verbose = ctx.obj.get("verbose", False)

    try:
        success, message, cost, model = run_agentic_checkup(
            issue_url=target,
            verbose=verbose,
            quiet=quiet,
            no_fix=no_fix,
            timeout_adder=timeout_adder,
            use_github_state=not no_github_state,
        )

        if not quiet:
            status = "Success" if success else "Failed"
            click.echo(f"Status: {status}")
            click.echo(f"Message: {message}")
            click.echo(f"Cost: ${cost:.4f}")
            click.echo(f"Model: {model}")

        if not success:
            raise click.exceptions.Exit(1)

        return message, cost, model

    except (click.Abort, click.exceptions.Exit):
        raise
    except Exception as exception:
        handle_error(exception, "checkup", ctx.obj.get("quiet", False))
        return None
