import sys
from typing import Tuple, Optional, Dict, Any
import click
from rich import print as rprint
from . import DEFAULT_STRENGTH, DEFAULT_TIME
from pathlib import Path

from .construct_paths import construct_paths
from .fix_code_loop import fix_code_loop
# Import fix_code_module_errors conditionally or ensure it's always available
try:
    from .fix_code_module_errors import fix_code_module_errors
except ImportError:
    # Handle case where fix_code_module_errors might not be available if not needed
    fix_code_module_errors = None

def crash_main(
    ctx: click.Context,
    prompt_file: str,
    code_file: str,
    program_file: str,
    error_file: str,
    output: Optional[str] = None,
    output_program: Optional[str] = None,
    loop: bool = False,
    max_attempts: Optional[int] = None,
    budget: Optional[float] = None
) -> Tuple[bool, str, str, int, float, str]:
    """
    Main function to fix errors in a code module and its calling program that caused a crash.

    :param ctx: Click context containing command-line parameters.
    :param prompt_file: Path to the prompt file that generated the code module.
    :param code_file: Path to the code module that caused the crash.
    :param program_file: Path to the program that was running the code module.
    :param error_file: Path to the file containing the error messages.
    :param output: Optional path to save the fixed code file.
    :param output_program: Optional path to save the fixed program file.
    :param loop: Enable iterative fixing process.
    :param max_attempts: Maximum number of fix attempts before giving up.
    :param budget: Maximum cost allowed for the fixing process.
    :return: A tuple containing:
        - bool: Success status
        - str: The final fixed code module
        - str: The final fixed program
        - int: Total number of fix attempts made
        - float: Total cost of all fix attempts
        - str: The name of the model used
    """
    # Ensure ctx.obj and ctx.params exist and are dictionaries
    ctx.obj = ctx.obj if isinstance(ctx.obj, dict) else {}
    ctx.params = ctx.params if isinstance(ctx.params, dict) else {}

    quiet = ctx.params.get("quiet", ctx.obj.get("quiet", False))
    verbose = ctx.params.get("verbose", ctx.obj.get("verbose", False))

    strength = ctx.obj.get("strength", DEFAULT_STRENGTH)
    temperature = ctx.obj.get("temperature", 0)
    time_param = ctx.obj.get("time", DEFAULT_TIME)

    try:
        input_file_paths = {
            "prompt_file": prompt_file,
            "code_file": code_file,
            "program_file": program_file,
            "error_file": error_file
        }
        command_options: Dict[str, Any] = {
            "output": output,
            "output_program": output_program
        }

        force = ctx.params.get("force", ctx.obj.get("force", False))

        resolved_config, input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=force,
            quiet=quiet,
            command="crash",
            command_options=command_options,
            context_override=ctx.obj.get('context')
        )

        prompt_content = input_strings["prompt_file"]
        code_content = input_strings["code_file"]
        program_content = input_strings["program_file"]
        error_content = input_strings["error_file"]

        original_code_content = code_content
        original_program_content = program_content

        code_updated: bool = False
        program_updated: bool = False

        if loop:
            success, final_program, final_code, attempts, cost, model = fix_code_loop(
                code_file, prompt_content, program_file, strength, temperature,
                max_attempts or 3, budget or 5.0, error_file, verbose, time_param
            )
            # Always set final_code/final_program to something non-empty
            if not final_code:
                final_code = original_code_content
            if not final_program:
                final_program = original_program_content
            code_updated = final_code != original_code_content
            program_updated = final_program != original_program_content
        else:
            if fix_code_module_errors is None:
                raise ImportError("fix_code_module_errors is required but not available.")

            update_program, update_code, fixed_program, fixed_code, _, cost, model = fix_code_module_errors(
                program_content, prompt_content, code_content, error_content,
                strength, temperature, verbose, time_param
            )
            success = True
            attempts = 1

            # Fallback if fixed_program is empty but update_program is True
            if update_program and not fixed_program.strip():
                fixed_program = program_content
            if update_code and not fixed_code.strip():
                fixed_code = code_content

            final_code = fixed_code if update_code else code_content
            final_program = fixed_program if update_program else program_content

            # Always set final_code/final_program to something non-empty
            if not final_code:
                final_code = original_code_content
            if not final_program:
                final_program = original_program_content

            code_updated = final_code != original_code_content
            program_updated = final_program != original_program_content

        output_code_path_str = output_file_paths.get("output")
        output_program_path_str = output_file_paths.get("output_program")

        # Always write output files if output paths are specified
        if output_code_path_str:
            output_code_path = Path(output_code_path_str)
            output_code_path.parent.mkdir(parents=True, exist_ok=True)
            with open(output_code_path, "w") as f:
                f.write(final_code)

        if output_program_path_str:
            output_program_path = Path(output_program_path_str)
            output_program_path.parent.mkdir(parents=True, exist_ok=True)
            with open(output_program_path, "w") as f:
                f.write(final_program)

        if not quiet:
            if success:
                rprint("[bold green]Crash fix attempt completed.[/bold green]")
            else:
                rprint("[bold yellow]Crash fix attempt completed with issues.[/bold yellow]")
            rprint(f"[bold]Model used:[/bold] {model}")
            rprint(f"[bold]Total attempts:[/bold] {attempts}")
            rprint(f"[bold]Total cost:[/bold] ${cost:.2f}")

            if output_code_path_str:
                if code_updated:
                    rprint(f"[bold]Fixed code saved to:[/bold] {output_code_path_str}")
                else:
                    rprint(f"[info]Code file '{Path(code_file).name}' was not modified (but output file was written).[/info]")
            if output_program_path_str:
                if program_updated:
                    rprint(f"[bold]Fixed program saved to:[/bold] {output_program_path_str}")
                else:
                    rprint(f"[info]Program file '{Path(program_file).name}' was not modified (but output file was written).[/info]")

        return success, final_code, final_program, attempts, cost, model

    except FileNotFoundError as e:
        if not quiet:
            rprint(f"[bold red]Error:[/bold red] Input file not found: {e}")
        sys.exit(1)
    except Exception as e:
        if not quiet:
            rprint(f"[bold red]An unexpected error occurred:[/bold red] {str(e)}")
        sys.exit(1)
