import os
from typing import Tuple, Optional
from rich import print
from rich.console import Console
from rich.panel import Panel
from .update_prompt import update_prompt
from .agentic_common import get_available_agents
from .agentic_update import run_agentic_update
import git
from . import DEFAULT_TIME
console = Console()

def git_update(
    input_prompt: str,
    modified_code_file: str,
    strength: float,
    temperature: float,
    verbose: bool = False,
    time: float = DEFAULT_TIME,
    simple: bool = False,
    quiet: bool = False,
    prompt_file: Optional[str] = None
) -> Tuple[Optional[str], float, str]:
    """
    Read in modified code, restore the prior checked-in version from Git,
    update the prompt (via agentic or legacy path), write back the modified code,
    and return outputs.

    Args:
        input_prompt (str): The prompt TEXT content (not a file path).
        modified_code_file (str): Filepath of the modified code.
        strength (float): Strength parameter for the LLM model.
        temperature (float): Temperature parameter for the LLM model.
        verbose (bool): Enable verbose logging.
        time (float): Time parameter for the LLM model.
        simple (bool): If True, skip agentic and use legacy update_prompt().
        quiet (bool): Suppress non-error logging.
        prompt_file (Optional[str]): Path to prompt file (required for agentic path).

    Returns:
        Tuple[Optional[str], float, str]: Updated prompt content, total cost, and model name.
    """
    modified_code: Optional[str] = None
    agentic_cost = 0.0

    try:
        # Check if inputs are valid
        if not input_prompt or not modified_code_file:
            raise ValueError("Input prompt and modified code file path are required.")

        if not os.path.exists(modified_code_file):
            raise FileNotFoundError(f"Modified code file not found: {modified_code_file}")

        # Initialize git repository object once
        repo = git.Repo(modified_code_file, search_parent_directories=True)
        repo_root = repo.working_tree_dir

        # Get the file's relative path to the repo root
        relative_path = os.path.relpath(modified_code_file, repo_root)

        # Read the modified code FIRST (before any git operations)
        with open(modified_code_file, 'r') as file:
            modified_code = file.read()

        # Restore the prior checked-in version using the relative path
        repo.git.checkout('HEAD', '--', relative_path)

        # Read the original input code
        with open(modified_code_file, 'r') as file:
            original_input_code = file.read()

        # Routing decision: agentic vs legacy
        use_agentic = (
            not simple
            and prompt_file is not None
            and get_available_agents()
        )

        if use_agentic:
            # Agentic path
            success, message, agentic_cost, provider, changed_files = run_agentic_update(
                prompt_file=prompt_file,
                code_file=modified_code_file,
                verbose=verbose,
                quiet=quiet
            )
            if success:
                # Read updated prompt content from file
                with open(prompt_file, 'r') as file:
                    updated_prompt = file.read()

                # Pretty print the results
                console.print(Panel.fit(
                    f"[bold green]Success (agentic):[/bold green]\n"
                    f"Provider: {provider}\n"
                    f"Total cost: ${agentic_cost:.6f}\n"
                    f"Changed files: {', '.join(changed_files)}"
                ))

                return updated_prompt, agentic_cost, provider
            # Fall through to legacy on agentic failure

        # Legacy path
        result_prompt, legacy_cost, model_name = update_prompt(
            input_prompt=input_prompt,
            input_code=original_input_code,
            modified_code=modified_code,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            time=time
        )

        total_cost = agentic_cost + legacy_cost

        # Pretty print the results
        console.print(Panel.fit(
            f"[bold green]Success:[/bold green]\n"
            f"Modified prompt: {result_prompt}\n"
            f"Total cost: ${total_cost:.6f}\n"
            f"Model name: {model_name}"
        ))

        return result_prompt, total_cost, model_name

    except Exception as e:
        console.print(Panel(f"[bold red]Error:[/bold red] {str(e)}", title="Error", expand=False))
        return None, agentic_cost, ""

    finally:
        # Always restore user's modified code to disk before returning
        if modified_code is not None and modified_code_file:
            try:
                with open(modified_code_file, 'w') as file:
                    file.write(modified_code)
            except Exception:
                pass  # Best effort restoration
