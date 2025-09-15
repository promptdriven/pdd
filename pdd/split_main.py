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
) -> Tuple[str, str, float, str]:
    """
    CLI wrapper for splitting a prompt into extracted functionality and remaining prompt.

    Args:
        ctx: Click context containing command-line parameters.
        input_prompt_file: Path to the input prompt file to be split.
        input_code_file: Path to the code file generated from the input prompt.
        example_code_file: Path to the example code file showing usage.
        output_sub: Optional path where to save the extracted functionality.
        output_modified: Optional path where to save the remaining prompt.

    Returns:
        Tuple containing:
            - str: The extracted functionality content
            - str: The remaining prompt content
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
        resolved_config, input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get('force', False),
            quiet=ctx.obj.get('quiet', False),
            command="split",
            command_options=command_options,
            context_override=ctx.obj.get('context')
        )

        # Get parameters from context
        strength = ctx.obj.get('strength', 0.5)
        temperature = ctx.obj.get('temperature', 0)
        time = ctx.obj.get('time')

        # Call the split function with the standardized return pattern (result_data, cost, model_name)
        result_tuple, total_cost, model_name = split(
            input_prompt=input_strings["input_prompt"],
            input_code=input_strings["input_code"],
            example_code=input_strings["example_code"],
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=not ctx.obj.get('quiet', False)
        )
        
        # Unpack the result tuple
        extracted_functionality, remaining_prompt = result_tuple

        # Save the output files
        try:
            with open(output_file_paths["output_sub"], 'w') as f:
                f.write(extracted_functionality)  # The extracted functionality goes to output_sub
            with open(output_file_paths["output_modified"], 'w') as f:
                f.write(remaining_prompt)  # The remaining prompt goes to output_modified
        except IOError as e:
            raise IOError(f"Failed to save output files: {str(e)}")

        # Provide user feedback if not in quiet mode
        if not ctx.obj.get('quiet', False):
            rprint("[bold green]Successfully split the prompt![/bold green]")
            rprint(f"[bold]Extracted functionality saved to:[/bold] {output_file_paths['output_sub']}")
            rprint(f"[bold]Remaining prompt saved to:[/bold] {output_file_paths['output_modified']}")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")

        # Return with standardized order (result_data, cost, model_name)
        return {
            "sub_prompt_content": extracted_functionality,
            "modified_prompt_content": remaining_prompt,
            "output_sub": output_file_paths["output_sub"],
            "output_modified": output_file_paths["output_modified"]
        }, total_cost, model_name

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
