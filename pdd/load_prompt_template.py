from pathlib import Path
import os
from rich import print
from typing import Optional
import sys

def load_prompt_template(prompt_name: str) -> Optional[str]:
    """
    Load a prompt template from a file.

    Args:
        prompt_name (str): Name of the prompt file to load (without extension)

    Returns:
        str: The prompt template text

    Raises:
        ValueError: If PDD_PATH environment variable is not set
        FileNotFoundError: If the prompt file doesn't exist
        IOError: If there's an error reading the file
    """
    try:
        # Step 1: Get project path from environment variable
        project_path = os.getenv('PDD_PATH')
        if not project_path:
            raise ValueError("[red]PDD_PATH environment variable is not set[/red]")

        # Construct the full path to the prompt file
        prompt_path = Path(project_path) / 'prompts' / f"{prompt_name}.prompt"

        # Step 2: Load and return the prompt template
        if not prompt_path.exists():
            raise FileNotFoundError(
                f"[red]Prompt file not found: {prompt_path}[/red]"
            )

        try:
            with open(prompt_path, 'r', encoding='utf-8') as file:
                prompt_template = file.read()
                print(f"[green]Successfully loaded prompt: {prompt_name}[/green]")
                return prompt_template

        except IOError as e:
            raise IOError(
                f"[red]Error reading prompt file {prompt_name}: {str(e)}[/red]"
            )

    except Exception as e:
        print(f"[red]Unexpected error loading prompt template: {str(e)}[/red]")
        return None

if __name__ == "__main__":
    # Example usage
    try:
        prompt = load_prompt_template("example_prompt")
        if prompt:
            print("[blue]Loaded prompt template:[/blue]")
            print(prompt)
    except Exception as e:
        print(f"[red]Error in main: {str(e)}[/red]")
        sys.exit(1)