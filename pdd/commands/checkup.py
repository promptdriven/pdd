"""
Checkup command — GitHub issue-driven project health check, or local diagnostics.
"""
import click
from pathlib import Path
from typing import Optional, Tuple

from ..agentic_checkup import run_agentic_checkup
from ..agentic_sync import _is_github_issue_url
from ..track_cost import track_cost
from ..core.errors import handle_error


@click.command("checkup")
@click.argument("target", required=False, default=None)
@click.option(
    "--validate-arch-includes",
    "validate_arch_includes",
    is_flag=True,
    default=False,
    help="Cross-check architecture.json against module <include> tags (no GitHub issue).",
)
@click.option(
    "--project-root",
    "project_root",
    type=click.Path(exists=True, path_type=Path, file_okay=False),
    default=None,
    help="With --validate-arch-includes: directory to scan (default: current directory).",
)
@click.option(
    "--strict",
    is_flag=True,
    default=False,
    help="With --validate-arch-includes: also validate bundled sample trees (examples/, …).",
)
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
    target: Optional[str],
    validate_arch_includes: bool,
    project_root: Optional[Path],
    strict: bool,
    no_fix: bool,
    timeout_adder: float,
    no_github_state: bool,
) -> Optional[Tuple[str, float, str]]:
    """
    Run agentic health checkup from a GitHub issue, or local diagnostics.

    \b
    GitHub mode (default): TARGET is an issue URL.
    Local mode: pass --validate-arch-includes (no TARGET) to cross-validate
    architecture.json entries against module prompt <include> tags — same check
    as ``pdd validate-arch-includes``.
    """
    ctx.ensure_object(dict)

    if validate_arch_includes:
        if target is not None:
            raise click.BadParameter(
                "Do not pass TARGET when using --validate-arch-includes.",
                param_hint="'TARGET'",
            )
        root = project_root if project_root is not None else Path.cwd()
        from ..architecture_include_validation import run_validate_arch_includes_cli

        run_validate_arch_includes_cli(root, strict=strict, quiet=ctx.obj.get("quiet", False))
        return "validate-arch-includes: ok", 0.0, ""

    if not target:
        raise click.UsageError(
            "Missing argument 'TARGET'. For local checks use "
            "`pdd checkup --validate-arch-includes`."
        )

    if not _is_github_issue_url(target):
        raise click.BadParameter(
            "TARGET must be a GitHub issue URL "
            "(e.g., https://github.com/org/repo/issues/123), "
            "or use --validate-arch-includes for architecture / include validation.",
            param_hint="'TARGET'",
        )

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
