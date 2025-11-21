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

    # Step 1: Get project path from environment variable (preferred),
    # else fall back to auto-detect based on this module's location or CWD.
    project_path_env = os.getenv('PDD_PATH')
    candidate_paths = []
    if project_path_env:
        candidate_paths.append(Path(project_path_env))

    # Fallback 1: repository root inferred from this module (pdd/ => repo root)
    try:
        module_root = Path(__file__).resolve().parent  # pdd/
        repo_root = module_root.parent                 # repo root
        candidate_paths.append(repo_root)
    except Exception:
        pass

    # Fallback 2: current working directory
    candidate_paths.append(Path.cwd())

    # Build candidate prompt paths to try in order
    prompt_candidates = []
    for cp in candidate_paths:
        # Check both <path>/prompts/ and <path>/pdd/prompts/
        # The latter handles installed package case where prompts are in pdd/prompts/
        prompt_candidates.append(cp / 'prompts' / f"{prompt_name}.prompt")
        prompt_candidates.append(cp / 'pdd' / 'prompts' / f"{prompt_name}.prompt")

    # Step 2: Load and return the prompt template
    prompt_path: Optional[Path] = None
    for candidate in prompt_candidates:
        if candidate.exists():
            prompt_path = candidate
            break

    if prompt_path is None:
        tried = "\n".join(str(c) for c in prompt_candidates)
        print_formatted(
            f"[red]Prompt file not found in any candidate locations for '{prompt_name}'. Tried:\n{tried}[/red]"
        )
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