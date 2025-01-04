import sys
from typing import Tuple, Optional
import click
from rich import print as rprint

from .construct_paths import construct_paths
from .fix_errors_from_unit_tests import fix_errors_from_unit_tests
from .fix_error_loop import fix_error_loop

def fix_main(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    unit_test_file: str,
    error_file: str,
    output_test: Optional[str],
    output_code: Optional[str],
    output_results: Optional[str],
    loop: bool,
    verification_program: Optional[str],
    max_attempts: int,
    budget: float,
    auto_submit: bool
) -> Tuple[bool, str, str, int, float, str]:
    """
    Main function to fix errors in code and unit tests.

    Args:
        ctx: Click context containing command-line parameters
        prompt_file: Path to the prompt file that generated the code
        code_file: Path to the code file to be fixed
        unit_test_file: Path to the unit test file
        error_file: Path to the error log file
        output_test: Path to save the fixed unit test file
        output_code: Path to save the fixed code file
        output_results: Path to save the fix results
        loop: Whether to use iterative fixing process
        verification_program: Path to program that verifies code correctness
        max_attempts: Maximum number of fix attempts
        budget: Maximum cost allowed for fixing
        auto_submit: Whether to auto-submit example if tests pass

    Returns:
        Tuple containing:
        - Success status (bool)
        - Fixed unit test code (str)
        - Fixed source code (str)
        - Total number of fix attempts (int)
        - Total cost of operation (float)
        - Name of model used (str)
    """
    # Check verification program requirement before any file operations
    if loop and not verification_program:
        raise click.UsageError("--verification-program is required when using --loop")

    try:
        # Construct file paths
        input_file_paths = {
            "prompt_file": prompt_file,
            "code_file": code_file,
            "unit_test_file": unit_test_file
        }
        if not loop:
            input_file_paths["error_file"] = error_file

        command_options = {
            "output_test": output_test,
            "output_code": output_code,
            "output_results": output_results
        }

        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=ctx.obj.get('quiet', False),
            command="fix",
            command_options=command_options
        )

        # Get parameters from context
        strength = ctx.obj.get('strength', 0.9)
        temperature = ctx.obj.get('temperature', 0)

        if loop:
            # Use fix_error_loop for iterative fixing
            success, fixed_unit_test, fixed_code, attempts, total_cost, model_name = fix_error_loop(
                unit_test_file=unit_test_file,
                code_file=code_file,
                prompt=input_strings["prompt_file"],
                verification_program=verification_program,
                strength=strength,
                temperature=temperature,
                max_attempts=max_attempts,
                budget=budget,
                error_log_file=output_file_paths.get("output_results")
            )
        else:
            # Use fix_errors_from_unit_tests for single-pass fixing
            update_unit_test, update_code, fixed_unit_test, fixed_code, total_cost, model_name = fix_errors_from_unit_tests(
                unit_test=input_strings["unit_test_file"],
                code=input_strings["code_file"],
                prompt=input_strings["prompt_file"],
                error=input_strings["error_file"],
                error_file=output_file_paths.get("output_results"),
                strength=strength,
                temperature=temperature
            )
            success = update_unit_test or update_code
            attempts = 1

        # Save fixed files
        if fixed_unit_test:
            with open(output_file_paths["output_test"], 'w') as f:
                f.write(fixed_unit_test)

        if fixed_code:
            with open(output_file_paths["output_code"], 'w') as f:
                f.write(fixed_code)

        # Provide user feedback
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold]{'Success' if success else 'Failed'} to fix errors[/bold]")
            rprint(f"[bold]Total attempts:[/bold] {attempts}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            if success:
                rprint("[bold green]Fixed files saved:[/bold green]")
                rprint(f"  Test file: {output_file_paths['output_test']}")
                rprint(f"  Code file: {output_file_paths['output_code']}")
                if output_file_paths.get("output_results"):
                    rprint(f"  Results file: {output_file_paths['output_results']}")

        return success, fixed_unit_test, fixed_code, attempts, total_cost, model_name

    except Exception as e:
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        sys.exit(1)