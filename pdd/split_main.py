import sys
from typing import Tuple, Optional
import click
from rich import print as rprint

from .construct_paths import construct_paths
from .split import split

def split_main(
    ctx: click.Context,
    input_prompt_file: str,
    input_code_file: str,
    example_code_file: str,
    output_sub: Optional[str],
    output_modified: Optional[str]
) -> Tuple[str, str, str, float]:
    """
    CLI wrapper for splitting a prompt into a sub_prompt and modified_prompt.

    Args:
        ctx: Click context containing command-line parameters.
        input_prompt_file: Path to the input prompt file to be split.
        input_code_file: Path to the code file generated from the input prompt.
        example_code_file: Path to the example code file showing usage.
        output_sub: Optional path where to save the sub-prompt.
        output_modified: Optional path where to save the modified prompt.

    Returns:
        Tuple containing:
            - str: The sub-prompt content
            - str: The modified prompt content
            - float: The total cost of the operation
            - str: The model name used (second to last element)

    Raises:
        SystemExit: If any error occurs during execution.
    """
    try:
        # Construct file paths
        input_file_paths = {
            "input_prompt": input_prompt_file,
            "input_code": input_code_file,
            "example_code": example_code_file
        }
        command_options = {
            "output_sub": output_sub,
            "output_modified": output_modified
        }
        
        # Get input strings and output paths
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=ctx.obj.get('quiet', False),
            command="split",
            command_options=command_options
        )

        # Get parameters from context
        strength = ctx.obj.get('strength', 0.5)
        temperature = ctx.obj.get('temperature', 0)

        # Call the split function and unpack the new tuple signature
        sub_prompt, modified_prompt, model_name, total_cost = split(
            input_prompt=input_strings["input_prompt"],
            input_code=input_strings["input_code"],
            example_code=input_strings["example_code"],
            strength=strength,
            temperature=temperature,
            verbose=not ctx.obj.get('quiet', False)
        )

        # Save the output files
        try:
            with open(output_file_paths["output_sub"], 'w') as f:
                f.write(sub_prompt)
            with open(output_file_paths["output_modified"], 'w') as f:
                f.write(modified_prompt)
        except IOError as e:
            raise IOError(f"Failed to save output files: {str(e)}")

        # Provide user feedback if not in quiet mode
        if not ctx.obj.get('quiet', False):
            rprint("[bold green]Successfully split the prompt![/bold green]")
            rprint(f"[bold]Sub-prompt saved to:[/bold] {output_file_paths['output_sub']}")
            rprint(f"[bold]Modified prompt saved to:[/bold] {output_file_paths['output_modified']}")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")

        return sub_prompt, modified_prompt, total_cost, model_name

    except Exception as e:
        # Handle errors and provide appropriate feedback
        if not ctx.obj.get('quiet', False):
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
            
            # Provide more specific error messages based on the exception type
            if isinstance(e, FileNotFoundError):
                rprint("[yellow]Hint: Check if all input files exist and are accessible.[/yellow]")
            elif isinstance(e, IOError):
                rprint("[yellow]Hint: Check file permissions and disk space.[/yellow]")
            elif isinstance(e, ValueError):
                rprint("[yellow]Hint: Check if input files have valid content.[/yellow]")
        
        sys.exit(1)