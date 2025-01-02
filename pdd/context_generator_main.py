import sys
from typing import Tuple, Optional
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
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=ctx.obj.get('quiet', False),
            command="example",
            command_options=command_options
        )

        # Load input files
        prompt_content = input_strings["prompt_file"]
        code_content = input_strings["code_file"]

        # Generate example code
        strength = ctx.obj.get('strength', 0.5)
        temperature = ctx.obj.get('temperature', 0)
        example_code, total_cost, model_name = context_generator(
            code_module=code_content,
            prompt=prompt_content,
            strength=strength,
            temperature=temperature,
            verbose=ctx.obj.get('verbose', False)
        )

        # Save results
        if output_file_paths["output"]:
            with open(output_file_paths["output"], 'w') as f:
                f.write(example_code)

        # Provide user feedback
        if not ctx.obj.get('quiet', False):
            rprint("[bold green]Example code generated successfully.[/bold green]")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            if output:
                rprint(f"[bold]Example code saved to:[/bold] {output_file_paths['output']}")

        # Always print example code, even in quiet mode
        rprint("[bold]Generated Example Code:[/bold]")
        rprint(example_code)

        return example_code, total_cost, model_name

    except Exception as e:
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        sys.exit(1)