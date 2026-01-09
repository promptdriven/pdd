"""
Fix command.
"""
from __future__ import annotations
import os
import click
from typing import Dict, List, Optional, Tuple, Any

from ..fix_main import fix_main
from ..track_cost import track_cost
from ..core.errors import handle_error

@click.command("fix")
@click.argument("prompt_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("code_file", type=click.Path(exists=True, dir_okay=False))
@click.argument("args", nargs=-1, type=click.Path(dir_okay=False))
@click.option(
    "--output-test",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the fixed unit test file (file or directory).",
)
@click.option(
    "--output-code",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the fixed code file (file or directory).",
)
@click.option(
    "--output-results",
    type=click.Path(writable=True),
    default=None,
    help="Specify where to save the results log (file or directory).",
)
@click.option(
    "--loop",
    is_flag=True,
    default=False,
    help="Enable iterative fixing process."
)
@click.option(
    "--verification-program",
    type=click.Path(exists=True, dir_okay=False),
    default=None,
    help="Path to a Python program that verifies the fix.",
)
@click.option(
    "--max-attempts",
    type=int,
    default=3,
    show_default=True,
    help="Maximum number of fix attempts.",
)
@click.option(
    "--budget",
    type=float,
    default=5.0,
    show_default=True,
    help="Maximum cost allowed for the fixing process.",
)
@click.option(
    "--auto-submit",
    is_flag=True,
    default=False,
    help="Automatically submit the example if all unit tests pass.",
)
@click.option(
    "--agentic-fallback/--no-agentic-fallback",
    is_flag=True,
    default=True,
    help="Enable agentic fallback if the primary fix mechanism fails.",
)
@click.pass_context
@track_cost
def fix(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    args: Tuple[str, ...],
    output_test: Optional[str],
    output_code: Optional[str],
    output_results: Optional[str],
    loop: bool,
    verification_program: Optional[str],
    max_attempts: int,
    budget: float,
    auto_submit: bool,
    agentic_fallback: bool,
) -> Optional[Tuple[Dict[str, Any], float, str]]:
    """Fix code based on a prompt and unit test errors.

    Accepts one or more UNIT_TEST_FILES.
    In non-loop mode, the last argument must be the ERROR_FILE.
    In loop mode, all arguments after CODE_FILE are treated as UNIT_TEST_FILES.
    """
    try:
        # Parse args into unit_test_files and error_file based on loop mode
        unit_test_files: List[str] = []
        error_file: Optional[str] = None

        if not args:
            raise click.BadArgumentUsage("Missing argument 'UNIT_TEST_FILES'.")

        if loop:
            # In loop mode, all args are test files, error file is optional/generated
            unit_test_files = list(args)
            error_file = None
        else:
            # In non-loop mode, the last arg is the error file
            if len(args) < 2:
                raise click.BadArgumentUsage(
                    "Missing argument 'ERROR_FILE'. In non-loop mode, you must provide at "
                    "least one UNIT_TEST_FILE followed by ERROR_FILE (minimum 2 arguments required)."
                )
            unit_test_files = list(args[:-1])
            error_file = args[-1]

        # Validate existence of unit test files manually since we removed exists=True from the args argument definition
        for f in unit_test_files:
            if not os.path.exists(f):
                raise click.BadParameter(f"Path '{f}' does not exist.", param_hint='unit_test_files')

        all_results: List[Dict[str, Any]] = []
        total_cost = 0.0
        model_name = ""

        # Process each unit test file separately
        for unit_test_file in unit_test_files:
            success, fixed_unit_test, fixed_code, attempts, cost, model = fix_main(
                ctx=ctx,
                prompt_file=prompt_file,
                code_file=code_file,
                unit_test_file=unit_test_file,
                error_file=error_file,
                output_test=output_test,
                output_code=output_code,
                output_results=output_results,
                loop=loop,
                verification_program=verification_program,
                max_attempts=max_attempts,
                budget=budget,
                auto_submit=auto_submit,
                agentic_fallback=agentic_fallback,
            )
            all_results.append({
                "success": success,
                "fixed_unit_test": fixed_unit_test,
                "fixed_code": fixed_code,
                "attempts": attempts,
                "unit_test_file": unit_test_file,
            })
            total_cost += cost
            model_name = model

        # Aggregate results
        overall_success = all(r["success"] for r in all_results)
        result = {
            "success": overall_success,
            "results": all_results,
            "total_attempts": sum(r["attempts"] for r in all_results),
        }
        return result, total_cost, model_name
    except click.Abort:
        raise
    except Exception as exception:
        handle_error(exception, "fix", ctx.obj.get("quiet", False))
        ctx.exit(1)
