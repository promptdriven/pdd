import sys
from typing import Tuple, Optional
import click
from rich import print as rprint

from .construct_paths import construct_paths
from .fix_code_loop import fix_code_loop

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
    try:
        # Construct file paths
        input_file_paths = {
            "prompt_file": prompt_file,
            "code_file": code_file,
            "program_file": program_file,
            "error_file": error_file
        }
        command_options = {
            "output": output,
            "output_program": output_program
        }

        force = ctx.params.get("force", ctx.obj.get("force", False))
        quiet = ctx.params.get("quiet", ctx.obj.get("quiet", False))

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
        strength = ctx.obj.get("strength", 0.97)
        temperature = ctx.obj.get("temperature", 0)

        verbose = ctx.params.get("verbose", ctx.obj.get("verbose", False))

        if loop:
            # Use iterative fixing process
            success, final_code, final_program, attempts, cost, model = fix_code_loop(
                code_file, prompt_content, program_file, strength, temperature, max_attempts or 3, budget or 5.0, error_file, verbose
            )
        else:
            # Use single fix attempt
            from .fix_code_module_errors import fix_code_module_errors
            update_program, update_code, final_program, final_code, cost, model = fix_code_module_errors(
                program_content, prompt_content, code_content, error_content, strength, temperature, verbose
            )
            success = True
            attempts = 1

        # Ensure we have content to write, falling back to original content if needed
        if final_code == "":
            final_code = code_content
        
        if final_program == "":
            final_program = program_content

        # Determine whether to write the files based on whether paths are provided
        should_write_code = output_file_paths.get("output") is not None
        should_write_program = output_file_paths.get("output_program") is not None

        # Write output files
        if should_write_code:
            with open(output_file_paths["output"], "w") as f:
                f.write(final_code)

        if should_write_program:
            with open(output_file_paths["output_program"], "w") as f:
                f.write(final_program)

        # Provide user feedback
        if not quiet:
            if success:
                rprint("[bold green]Crash fix completed successfully.[/bold green]")
            else:
                rprint("[bold yellow]Crash fix completed with issues.[/bold yellow]")
            rprint(f"[bold]Model used:[/bold] {model}")
            rprint(f"[bold]Total attempts:[/bold] {attempts}")
            rprint(f"[bold]Total cost:[/bold] ${cost:.2f}")
            if should_write_code:
                rprint(f"[bold]Fixed code saved to:[/bold] {output_file_paths['output']}")
            if should_write_program:
                rprint(f"[bold]Fixed program saved to:[/bold] {output_file_paths['output_program']}")

        return success, final_code, final_program, attempts, cost, model
    
    except Exception as e:
        if not quiet:
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        sys.exit(1)