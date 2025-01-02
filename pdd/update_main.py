import sys
from typing import Tuple, Optional
import click
from rich import print as rprint

from .construct_paths import construct_paths
from .update_prompt import update_prompt
from .git_update import git_update

def update_main(
    ctx: click.Context,
    input_prompt_file: str,
    modified_code_file: str,
    input_code_file: Optional[str],
    output: Optional[str],
    git: bool = False,
) -> Tuple[str, float, str]:
    """
    CLI wrapper for updating prompts based on modified code.

    :param ctx: Click context object containing CLI options and parameters.
    :param input_prompt_file: Path to the original prompt file.
    :param modified_code_file: Path to the modified code file.
    :param input_code_file: Optional path to the original code file. If None, Git history is used if --git is True.
    :param output: Optional path to save the updated prompt.
    :param git: Use Git history to retrieve the original code if True.
    :return: Tuple containing the updated prompt, total cost, and model name.
    """
    try:
        # Construct file paths
        input_file_paths = {"input_prompt_file": input_prompt_file, "modified_code_file": modified_code_file}
        if input_code_file:
            input_file_paths["input_code_file"] = input_code_file

        # Validate input requirements
        if not git and input_code_file is None:
            raise ValueError("Must provide an input code file or use --git option.")

        command_options = {"output": output}
        input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get("force", False),
            quiet=ctx.obj.get("quiet", False),
            command="update",
            command_options=command_options,
        )

        # Extract input strings
        input_prompt = input_strings["input_prompt_file"]
        modified_code = input_strings["modified_code_file"]
        input_code = input_strings.get("input_code_file")

        # Update prompt using appropriate method
        if git:
            if input_code_file:
                raise ValueError("Cannot use both --git and provide an input code file.")
            modified_prompt, total_cost, model_name = git_update(
                input_prompt=input_prompt,
                modified_code_file=modified_code_file,
                strength=ctx.obj.get("strength", 0.5),
                temperature=ctx.obj.get("temperature", 0),
                verbose=ctx.obj.get("verbose", False)
            )
        else:
            if input_code is None:
                raise ValueError("Must provide an input code file or use --git option.")
            modified_prompt, total_cost, model_name = update_prompt(
                input_prompt=input_prompt,
                input_code=input_code,
                modified_code=modified_code,
                strength=ctx.obj.get("strength", 0.5),
                temperature=ctx.obj.get("temperature", 0),
                verbose=ctx.obj.get("verbose", False)
            )

        # Save the modified prompt
        with open(output_file_paths["output"], "w") as f:
            f.write(modified_prompt)

        # Provide user feedback
        if not ctx.obj.get("quiet", False):
            rprint("[bold green]Prompt updated successfully.[/bold green]")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            rprint(f"[bold]Updated prompt saved to:[/bold] {output_file_paths['output']}")

        return modified_prompt, total_cost, model_name

    except ValueError as e:
        if not ctx.obj.get("quiet", False):
            rprint(f"[bold red]Input error:[/bold red] {str(e)}")
        sys.exit(1)
    except Exception as e:
        if not ctx.obj.get("quiet", False):
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        sys.exit(1)