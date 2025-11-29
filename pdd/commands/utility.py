"""
Utility commands (install_completion, verify/fix-verification).
"""
import click
from typing import Optional, Tuple

from .. import cli as cli_module  # Import parent module for proper patching
from ..fix_verification_main import fix_verification_main
from ..track_cost import track_cost
from ..core.errors import handle_error

@click.command("install_completion")
@click.pass_context
def install_completion_cmd(ctx: click.Context):
    """Install shell completion for the PDD CLI."""
    try:
        quiet = ctx.obj.get("quiet", False)
        # Call through cli_module so patches to pdd.cli.install_completion work
        cli_module.install_completion(quiet=quiet)
    except Exception as e:
        handle_error(e, "install_completion", ctx.obj.get("quiet", False))


@click.command("verify")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("verification_program", type=click.Path(exists=True, dir_okay=False))
@click.option(
    "--output-code",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the verified code file (file or directory).",
)
@click.option(
    "--output-program",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the verified program file (file or directory).",
)
@click.option(
    "--output-results",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the results log (file or directory).",
)
@click.option(
    "--max-attempts",
    type=int,
    default=3,
    show_default=True,
    help="Maximum number of verification attempts.",
)
@click.option(
    "--budget",
    type=float,
    default=5.0,
    show_default=True,
    help="Maximum cost allowed for the verification process.",
)
@click.pass_context
@track_cost
def verify(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    verification_program: str,
    output_code: Optional[str],
    output_program: Optional[str],
    output_results: Optional[str],
    max_attempts: int,
    budget: float,
) -> Optional[Tuple]:
    """Verify code using a verification program."""
    try:
        success, prog_code,  code_content, attempts, total_cost, model_name = fix_verification_main(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            verification_program=verification_program,
            output_code=output_code,
            output_program=output_program,
            output_results=output_results,
            max_attempts=max_attempts,
            budget=budget,
        )
        result = {
            "success": success,
            "program_code": prog_code,
            "code_content": code_content,
            "attempts": attempts,
        }
        return result, total_cost, model_name
    except Exception as exception:
        handle_error(exception, "verify", ctx.obj.get("quiet", False))
        return None
