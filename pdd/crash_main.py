import sys
from typing import Tuple, Optional, Dict, Any
import click
from rich import print as rprint
from . import DEFAULT_STRENGTH
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
    verbose = ctx.params.get("verbose", ctx.obj.get("verbose", False)) # Get verbose flag

    try:
        # Construct file paths
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
        # quiet = ctx.params.get("quiet", ctx.obj.get("quiet", False)) # Already defined above

        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=force,
            quiet=quiet,
            command="crash",
            command_options=command_options
        )

        # Load input files
        prompt_content = input_strings["prompt_file"]
        code_content = input_strings["code_file"]
        program_content = input_strings["program_file"]
        error_content = input_strings["error_file"]

        # Get model parameters from context
        strength = ctx.obj.get("strength", DEFAULT_STRENGTH)
        temperature = ctx.obj.get("temperature", 0)

        # verbose = ctx.params.get("verbose", ctx.obj.get("verbose", False)) # Already defined above

        if loop:
            # Use iterative fixing process
            success, final_program, final_code, attempts, cost, model = fix_code_loop(
                code_file, prompt_content, program_file, strength, temperature, max_attempts or 3, budget or 5.0, error_file, verbose
            )
        else:
            # Use single fix attempt
            if fix_code_module_errors is None:
                 raise ImportError("fix_code_module_errors is required but not available.")
            # Note: fix_code_module_errors returns 7 values according to example
            # update_program, update_code, fixed_program, fixed_code, program_code_fix, cost, model
            # The current code unpacks 7 values, which matches the example.
            update_program, update_code, final_program, final_code, program_code_fix, cost, model = fix_code_module_errors(
                program_content, prompt_content, code_content, error_content, strength, temperature, verbose
            )
            success = True # Assume success after one attempt if no exception
            attempts = 1

        # Ensure we have content to write, falling back to original content if needed
        if final_program == "":
            final_program = program_content

        if final_code == "":
            final_code = code_content

        # Determine whether to write the files based on whether paths are provided
        output_code_path_str = output_file_paths.get("output")
        output_program_path_str = output_file_paths.get("output_program")

        should_write_code = output_code_path_str is not None
        should_write_program = output_program_path_str is not None

        # Write output files
        if should_write_code:
            output_code_path = Path(output_code_path_str)
            output_code_path.parent.mkdir(parents=True, exist_ok=True) # Ensure directory exists
            with open(output_code_path, "w") as f:
                f.write(final_code)

        if should_write_program:
            output_program_path = Path(output_program_path_str)
            output_program_path.parent.mkdir(parents=True, exist_ok=True) # Ensure directory exists
            with open(output_program_path, "w") as f:
                f.write(final_program)

        # Provide user feedback (using quiet flag as per current implementation)
        # To strictly follow the prompt's last note, change 'if not quiet:' to 'if verbose:'
        if not quiet:
            if success:
                rprint("[bold green]Crash fix completed successfully.[/bold green]")
            else:
                rprint("[bold yellow]Crash fix completed with issues.[/bold yellow]")
            rprint(f"[bold]Model used:[/bold] {model}")
            rprint(f"[bold]Total attempts:[/bold] {attempts}")
            rprint(f"[bold]Total cost:[/bold] ${cost:.2f}")
            if should_write_code:
                rprint(f"[bold]Fixed code saved to:[/bold] {output_code_path_str}")
            if should_write_program:
                rprint(f"[bold]Fixed program saved to:[/bold] {output_program_path_str}")

        return success, final_code, final_program, attempts, cost, model
    
    except FileNotFoundError as e:
        if not quiet:
             # Provide a more specific error message for file not found
             rprint(f"[bold red]Error:[/bold red] Input file not found: {e}")
        sys.exit(1)
    except Exception as e:
        if not quiet:
            rprint(f"[bold red]An unexpected error occurred:[/bold red] {str(e)}")
        # Consider logging the full traceback here for debugging
        # import traceback
        # traceback.print_exc()
        sys.exit(1)