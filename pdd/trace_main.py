import click
from rich import print as rprint
from typing import Tuple, Optional
from .construct_paths import construct_paths
from .trace import trace

def trace_main(ctx: click.Context, prompt_file: str, code_file: str, code_line: int, output: Optional[str]) -> Tuple[str, float, str]:
    """
    Handle the core logic for the 'trace' command in the pdd CLI.

    Args:
        ctx (click.Context): The Click context object containing CLI options and parameters.
        prompt_file (str): Path to the prompt file.
        code_file (str): Path to the generated code file.
        code_line (int): Line number in the code file to trace back to the prompt.
        output (Optional[str]): Path to save the trace analysis results.

    Returns:
        Tuple[str, float, str]: A tuple containing the prompt line number, total cost, and model name.
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
            force=ctx.params.get('force', False),
            quiet=ctx.params.get('quiet', False),
            command="trace",
            command_options=command_options
        )

        # Load input files
        prompt_content = input_strings["prompt_file"]
        code_content = input_strings["code_file"]

        # Perform trace analysis
        strength = ctx.params.get('strength', 0.5)
        temperature = ctx.params.get('temperature', 0)
        prompt_line, total_cost, model_name = trace(
            code_content, code_line, prompt_content, strength, temperature
        )

        # Save results
        if output:
            with open(output_file_paths["output"], 'w') as f:
                f.write(f"Prompt Line: {prompt_line}\n")
                f.write(f"Total Cost: ${total_cost:.6f}\n")
                f.write(f"Model Used: {model_name}\n")

        # Provide user feedback
        if not ctx.params.get('quiet', False):
            rprint(f"[bold green]Trace Analysis Complete[/bold green]")
            rprint(f"Corresponding prompt line: [cyan]{prompt_line}[/cyan]")
            rprint(f"Total cost: [yellow]${total_cost:.6f}[/yellow]")
            rprint(f"Model used: [magenta]{model_name}[/magenta]")

        return prompt_line, total_cost, model_name

    except FileNotFoundError as e:
        rprint(f"[bold red]File not found: {e}[/bold red]")
        ctx.exit(1)
    except ValueError as e:
        rprint(f"[bold red]Invalid input: {e}[/bold red]")
        ctx.exit(1)
    except Exception as e:
        rprint(f"[bold red]An unexpected error occurred: {e}[/bold red]")
        ctx.exit(1)