from pathlib import Path
import os
from typing import Optional
import sys
from rich import print

def print_formatted(message: str) -> None:
    """Print message with raw formatting tags for testing compatibility."""
    print(message)

def load_prompt_template(prompt_name: str) -> Optional[str]:
    """
    Load a prompt template from a file.

    Args:
        prompt_name (str): Name of the prompt file to load (without extension)

    Returns:
        str: The prompt template text
    """
    # Type checking
    if not isinstance(prompt_name, str):
        print_formatted("[red]Unexpected error loading prompt template[/red]")
        return None

    # Step 1: Get project path from environment variable
    project_path = os.getenv('PDD_PATH')
    if not project_path:
        print_formatted("[red]PDD_PATH environment variable is not set[/red]")
        return None

    # Construct the full path to the prompt file
    prompt_path = Path(project_path) / 'prompts' / f"{prompt_name}.prompt"

    # Step 2: Load and return the prompt template
    if not prompt_path.exists():
        print_formatted(f"[red]Prompt file not found: {prompt_path}[/red]")
        return None

    try:
        with open(prompt_path, 'r', encoding='utf-8') as file:
            prompt_template = file.read()
            print_formatted(f"[green]Successfully loaded prompt: {prompt_name}[/green]")
            return prompt_template

    except IOError as e:
        print_formatted(f"[red]Error reading prompt file {prompt_name}: {str(e)}[/red]")
        return None

    except Exception as e:
        print_formatted(f"[red]Unexpected error loading prompt template: {str(e)}[/red]")
        return None

if __name__ == "__main__":
    # Example usage
    prompt = load_prompt_template("example_prompt")
    if prompt:
        print_formatted("[blue]Loaded prompt template:[/blue]")
        print_formatted(prompt)
