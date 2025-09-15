import sys
from typing import Tuple, Optional
from pathlib import Path
import click
from rich import print as rprint

from .construct_paths import construct_paths
from .context_generator import context_generator

def context_generator_main(ctx: click.Context, prompt_file: str, code_file: str, output: Optional[str]) -> Tuple[str, float, str]:
    """
    Main function to generate example code from a prompt file and an existing code file.

    :param ctx: Click context containing command-line parameters.
    :param prompt_file: Path to the prompt file that generated the code.
    :param code_file: Path to the existing code file.
    :param output: Optional path to save the generated example code.
    :return: A tuple containing the generated example code, total cost, and model name used.
    """
    try:
        # Construct file paths
        input_file_paths = {
            "prompt_file": prompt_file,
            "code_file": code_file
        }
        command_options = {
            "output": output
        }
        resolved_config, input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=ctx.obj.get('quiet', False),
            command="example",
            command_options=command_options,
            context_override=ctx.obj.get('context')
        )

        # Load input files
        prompt_content = input_strings["prompt_file"]
        code_content = input_strings["code_file"]

        # Generate example code
        strength = ctx.obj.get('strength', 0.5)
        temperature = ctx.obj.get('temperature', 0)
        time = ctx.obj.get('time')
        example_code, total_cost, model_name = context_generator(
            language=language,
            code_module=code_content,
            prompt=prompt_content,
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=ctx.obj.get('verbose', False)
        )

        # Save results - if output is a directory, use resolved file path from construct_paths
        resolved_output = output_file_paths["output"]
        if output is None:
            final_output_path = resolved_output
        else:
            try:
                is_dir_hint = output.endswith('/')
            except Exception:
                is_dir_hint = False
            if is_dir_hint or (Path(output).exists() and Path(output).is_dir()):
                final_output_path = resolved_output
            else:
                final_output_path = output
        if final_output_path and example_code is not None:
            with open(final_output_path, 'w') as f:
                f.write(example_code)
        elif final_output_path and example_code is None:
            # Log the error but don't crash
            if not ctx.obj.get('quiet', False):
                rprint("[bold red]Warning:[/bold red] Example generation failed, skipping file write")

        # Provide user feedback
        if not ctx.obj.get('quiet', False):
            if example_code is not None:
                rprint("[bold green]Example code generated successfully.[/bold green]")
                rprint(f"[bold]Model used:[/bold] {model_name}")
                rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
                if final_output_path and example_code is not None:
                    rprint(f"[bold]Example code saved to:[/bold] {final_output_path}")
            else:
                rprint("[bold red]Example code generation failed.[/bold red]")
                rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")

        # Always print example code, even in quiet mode (if it exists)
        if example_code is not None:
            rprint("[bold]Generated Example Code:[/bold]")
            rprint(example_code)
        else:
            rprint("[bold red]No example code generated due to errors.[/bold red]")

        return example_code, total_cost, model_name

    except Exception as e:
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        sys.exit(1)
