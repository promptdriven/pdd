from pathlib import Path
from typing import Optional
from rich import print
from pdd.path_resolution import get_default_resolver

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

    resolver = get_default_resolver()
    prompt_path = resolver.resolve_prompt_template(prompt_name)

    if prompt_path is None:
        candidate_roots = []
        if resolver.pdd_path_env is not None:
            candidate_roots.append(resolver.pdd_path_env)
        if resolver.repo_root is not None:
            candidate_roots.append(resolver.repo_root)
        candidate_roots.append(resolver.cwd)

        prompt_candidates = []
        for root in candidate_roots:
            prompt_candidates.append(root / 'prompts' / f"{prompt_name}.prompt")
            prompt_candidates.append(root / 'pdd' / 'prompts' / f"{prompt_name}.prompt")

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
