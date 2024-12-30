import os
from typing import Tuple, Optional
from rich import print
from rich.console import Console
from rich.panel import Panel
from .update_prompt import update_prompt
import git

console = Console()

def git_update(
    input_prompt: str,
    modified_code_file: str,
    strength: float,
    temperature: float,
    verbose: bool = False
) -> Tuple[Optional[str], float, str]:
    """
    Read in modified code, restore the prior checked-in version from GitHub,
    update the prompt, write back the modified code, and return outputs.

    Args:
        input_prompt (str): The prompt that generated the original code.
        modified_code_file (str): Filepath of the modified code.
        strength (float): Strength parameter for the LLM model.
        temperature (float): Temperature parameter for the LLM model.

    Returns:
        Tuple[Optional[str], float, str]: Modified prompt, total cost, and model name.
    """
    try:
        # Check if inputs are valid
        if not input_prompt or not modified_code_file:
            raise ValueError("Input prompt and modified code file path are required.")

        if not os.path.exists(modified_code_file):
            raise FileNotFoundError(f"Modified code file not found: {modified_code_file}")

        # Initialize git repository
        repo = git.Repo(search_parent_directories=True)

        # Get the file's relative path to the repo root
        repo_root = repo.git.rev_parse("--show-toplevel")
        relative_path = os.path.relpath(modified_code_file, repo_root)

        # Read the modified code
        with open(modified_code_file, 'r') as file:
            modified_code = file.read()

        # Restore the prior checked-in version
        repo.git.checkout('HEAD', '--', relative_path)

        # Read the original input code
        with open(modified_code_file, 'r') as file:
            original_input_code = file.read()

        # Call update_prompt function
        modified_prompt, total_cost, model_name = update_prompt(
            input_prompt=input_prompt,
            input_code=original_input_code,
            modified_code=modified_code,
            strength=strength,
            temperature=temperature,
            verbose=verbose
        )

        # Write back the modified code
        with open(modified_code_file, 'w') as file:
            file.write(modified_code)


        # Pretty print the results
        console.print(Panel.fit(
            f"[bold green]Success:[/bold green]\n"
            f"Modified prompt: {modified_prompt}\n"
            f"Total cost: ${total_cost:.6f}\n"
            f"Model name: {model_name}"
        ))

        return modified_prompt, total_cost, model_name

    except Exception as e:
        console.print(Panel(f"[bold red]Error:[/bold red] {str(e)}", title="Error", expand=False))
        return None, 0.0, ""
