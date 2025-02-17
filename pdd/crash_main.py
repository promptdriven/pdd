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
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=ctx.obj.get('quiet', False),
            command="crash",
            command_options=command_options
        )

        # Load input files
        prompt_content = input_strings["prompt_file"]
        code_content = input_strings["code_file"]
        program_content = input_strings["program_file"]
        error_content = input_strings["error_file"]

        # Get model parameters from context
        strength = ctx.obj.get('strength', 0.97)
        temperature = ctx.obj.get('temperature', 0)

        if loop:
            # Use iterative fixing process
            success, final_code, final_program, attempts, cost, model = fix_code_loop(
                code_file=code_file,
                prompt=prompt_content,
                verification_program=program_file,
                strength=strength,
                temperature=temperature,
                max_attempts=max_attempts or 3,
                budget=budget or 5.0,
                error_log_file=error_file,
                verbose=not ctx.obj.get('verbose', False)
            )
        else:
            # Use single fix attempt
            from .fix_code_module_errors import fix_code_module_errors
            update_program, update_code, final_program, final_code, cost, model = fix_code_module_errors(
                program=program_content,
                prompt=prompt_content,
                code=code_content,
                errors=error_content,
                strength=strength,
                temperature=temperature,
                verbose=not ctx.obj.get('verbose', False)
            )
            success = True
            attempts = 1

        # Determine if contents were actually updated
        if final_code != "":
            update_code = final_code != code_content
        else:
            update_code = False
        if final_program != "":
            update_program = final_program != program_content
        else:
            update_program = False
            
        # Save results if contents changed
        if update_code and output_file_paths.get("output"):
            with open(output_file_paths["output"], 'w') as f:
                f.write(final_code)
        if update_program and output_file_paths.get("output_program"):
            with open(output_file_paths["output_program"], 'w') as f:
                f.write(final_program)

        # Provide user feedback
        if not ctx.obj.get('quiet', False):
            if success:
                rprint("[bold green]Crash fix completed successfully.[/bold green]")
            else:
                rprint("[bold yellow]Crash fix completed with some issues.[/bold yellow]")
            rprint(f"[bold]Model used:[/bold] {model}")
            rprint(f"[bold]Total attempts:[/bold] {attempts}")
            rprint(f"[bold]Total cost:[/bold] ${cost:.6f}")
            if update_code and output:
                rprint(f"[bold]Fixed code saved to:[/bold] {output_file_paths['output']}")
            if update_program and output_program:
                rprint(f"[bold]Fixed program saved to:[/bold] {output_file_paths['output_program']}")

        return success, final_code, final_program, attempts, cost, model

    except Exception as e:
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        sys.exit(1)