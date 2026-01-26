"""
Utility commands (install_completion, verify/fix-verification).
"""
from __future__ import annotations
import click
from typing import Optional, Tuple, Dict, Any

from ..fix_verification_main import fix_verification_main
from ..track_cost import track_cost
from ..core.errors import handle_error
from ..operation_log import log_operation

@click.command("install_completion")
@click.pass_context
def install_completion_cmd(ctx: click.Context) -> None:
    """Install shell completion for the PDD CLI."""
    # Safely retrieve quiet flag, defaulting to False if ctx.obj is None
    quiet = (ctx.obj or {}).get("quiet", False)
    try:
        from .. import cli as cli_module  # Import parent module for proper patching
        # Call through cli_module so patches to pdd.cli.install_completion work
        cli_module.install_completion(quiet=quiet)
    except Exception as e:
        handle_error(e, "install_completion", quiet)


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
@click.option(
    "--agentic-fallback/--no-agentic-fallback",
    is_flag=True,
    default=True,
    help="Enable agentic fallback if the primary fix mechanism fails.",
)
@click.pass_context
@log_operation(operation="verify", clears_run_report=True, updates_run_report=True)
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
    agentic_fallback: bool,
) -> Optional[Tuple[Dict[str, Any], float, str]]:
    """Verify code using a verification program."""
    try:
        # verify command implies a loop if max_attempts > 1, but let's enable loop by default
        # as it's the more powerful mode and matches the CLI args provided (max_attempts).
        # verification_program positional arg acts as both program_file (to run) and verification_program (reference)
        success, prog_code,  code_content, attempts, total_cost, model_name = fix_verification_main(
            ctx=ctx,
            prompt_file=prompt_file,
            code_file=code_file,
            program_file=verification_program,
            output_code=output_code,
            output_program=output_program,
            output_results=output_results,
            loop=True,
            verification_program=verification_program,
            max_attempts=max_attempts,
            budget=budget,
            agentic_fallback=agentic_fallback,
        )
        result = {
            "success": success,
            "program_code": prog_code,
            "code_content": code_content,
            "attempts": attempts,
        }
        return result, total_cost, model_name
    except click.Abort:
        raise
    except Exception as exception:
        quiet = (ctx.obj or {}).get("quiet", False)
        handle_error(exception, "verify", quiet)
        return None