import sys
from typing import Tuple, Optional, List, Dict, Any
import click
from rich import print as rprint
import concurrent.futures
import os
from pathlib import Path
import git
from rich.console import Console
from rich.progress import Progress
from rich.table import Table
from rich.theme import Theme

from .construct_paths import construct_paths
from .get_language import get_language
from .update_prompt import update_prompt
from .git_update import git_update
from . import DEFAULT_TIME

custom_theme = Theme({
    "info": "cyan",
    "warning": "yellow",
    "error": "bold red",
    "success": "green",
    "path": "dim blue",
})
console = Console(theme=custom_theme)
def create_and_find_prompt_code_pairs(repo_root: str) -> List[Tuple[str, str]]:
    """
    Scans the repo, creates missing prompt files, and returns all prompt/code pairs.
    """
    pairs = []
    created_files_count = 0
    ignored_dirs = {'.git', '.idea', '.vscode', '__pycache__', 'node_modules', '.venv', 'venv', 'dist', 'build'}
    
    console.print(f"[info]Scanning repository and creating missing prompt files...[/info]")

    all_files = []
    for root, dirs, files in os.walk(repo_root, topdown=True):
        dirs[:] = [d for d in dirs if d not in ignored_dirs]
        for file in files:
            all_files.append(os.path.join(root, file))

    code_files = [f for f in all_files if get_language(f) is not None and not f.endswith('.prompt')]
    
    for file_path in code_files:
        language = get_language(os.path.splitext(file_path)[1])
        if language:
            language = language.lower()
        base_path, _ = os.path.splitext(file_path)
        prompt_path_str = f"{base_path}_{language}.prompt"
        prompt_path = Path(prompt_path_str)

        if not prompt_path.exists():
            try:
                prompt_path.touch()
                console.print(f"[success]Created missing prompt file:[/success] [path]{prompt_path_str}[/path]")
                created_files_count += 1
            except OSError as e:
                console.print(f"[error]Failed to create file {prompt_path_str}: {e}[/error]")
        
        pairs.append((str(prompt_path), file_path))

    if created_files_count > 0:
        console.print(f"\n[success]Created {created_files_count} new prompt file(s).[/success]")
    else:
        console.print("\n[info]No missing prompt files found.[/info]")
        
    return pairs

def update_file_pair(prompt_file: str, code_file: str, ctx: click.Context) -> Dict[str, Any]:
    """Wrapper to call git_update for a single file pair and return a result dict."""
    try:
        with open(prompt_file, 'r') as f:
            input_prompt = f.read()

        # Handle empty prompt for generation
        if not input_prompt.strip():
            input_prompt = "no prompt exists yet, create a new one"

        modified_prompt, total_cost, model_name = git_update(
            input_prompt=input_prompt,
            modified_code_file=code_file,
            strength=ctx.obj.get("strength", 0.5),
            temperature=ctx.obj.get("temperature", 0),
            verbose=ctx.obj.get("verbose", False),
            time=ctx.obj.get("time"),
        )
        
        if modified_prompt is not None:
            # Overwrite the original prompt file
            with open(prompt_file, "w") as f:
                f.write(modified_prompt)
            return {
                "prompt_file": prompt_file,
                "status": "✅ Success",
                "cost": total_cost,
                "model": model_name,
                "error": "",
            }
        else:
            return {
                "prompt_file": prompt_file,
                "status": "❌ Failed",
                "cost": 0.0,
                "model": "",
                "error": "Update process returned no result.",
            }
    except Exception as e:
        return {
            "prompt_file": prompt_file,
            "status": "❌ Failed",
            "cost": 0.0,
            "model": "",
            "error": str(e),
        }

def update_main(
    ctx: click.Context,
    input_prompt_file: Optional[str],
    modified_code_file: Optional[str],
    input_code_file: Optional[str],
    output: Optional[str],
    use_git: bool = False,
    repo: bool = False,
) -> Optional[Tuple[str, float, str]]:
    """
    CLI wrapper for updating prompts based on modified code.
    Can operate on a single file or an entire repository.

    :param ctx: Click context object containing CLI options and parameters.
    :param input_prompt_file: Path to the original prompt file.
    :param modified_code_file: Path to the modified code file.
    :param input_code_file: Optional path to the original code file. If None, Git history is used if --git is True.
    :param output: Optional path to save the updated prompt.
    :param use_git: Use Git history to retrieve the original code if True.
    :param repo: If True, run in repository-wide mode.
    :return: Tuple containing the updated prompt, total cost, and model name.
    """
    if repo:
        repo_root = os.getcwd()
        try:
            git.Repo(repo_root, search_parent_directories=True)
        except git.InvalidGitRepositoryError:
            rprint("[bold red]Error:[/bold red] The --repo flag requires the current directory to be a Git repository.")
            sys.exit(1)

        pairs = create_and_find_prompt_code_pairs(repo_root)
        
        if not pairs:
            rprint("[info]No scannable code files found in the repository.[/info]")
            return None

        rprint(f"[info]Found {len(pairs)} total prompt/code pairs to process.[/info]")

        results = []
        with Progress(console=console) as progress:
            task = progress.add_task("[cyan]Updating prompts...", total=len(pairs))
            
            for prompt_path, code_path in pairs:
                result = update_file_pair(prompt_path, code_path, ctx)
                results.append(result)
                progress.update(task, advance=1)

        table = Table(show_header=True, header_style="bold magenta")
        table.add_column("Prompt File", style="dim", width=50)
        table.add_column("Status")
        table.add_column("Cost", justify="right")
        table.add_column("Model")
        table.add_column("Error", style="error")

        total_repo_cost = 0.0
        for res in sorted(results, key=lambda x: x["prompt_file"]):
            table.add_row(
                os.path.relpath(res["prompt_file"], repo_root),
                res["status"],
                f"${res['cost']:.6f}",
                res["model"],
                res["error"],
            )
            total_repo_cost += res["cost"]

        console.print("\n[bold]Repository Update Summary[/bold]")
        console.print(table)
        console.print(f"\n[bold]Total Estimated Cost: ${total_repo_cost:.6f}[/bold]")
        return "Repository update complete.", total_repo_cost, "repo_mode"

    # --- Single file logic ---
    try:
        # This block remains for single-file updates
        input_file_paths = {"input_prompt_file": input_prompt_file, "modified_code_file": modified_code_file}
        if input_code_file:
            input_file_paths["input_code_file"] = input_code_file

        if not use_git and input_code_file is None:
            # Check if we are in generation mode (empty prompt)
            with open(input_prompt_file, 'r') as f:
                if f.read().strip():
                     raise ValueError("Must provide an input code file or use --git option when prompt is not empty.")

        if output is None:
            # Default to overwriting the original prompt file when no explicit output specified
            # This preserves the "prompts as source of truth" philosophy
            command_options = {"output": input_prompt_file}
        else:
            command_options = {"output": output}
            
        resolved_config, input_strings, output_file_paths, _ = construct_paths(
            input_file_paths=input_file_paths,
            force=ctx.obj.get("force", False),
            quiet=ctx.obj.get("quiet", False),
            command="update",
            command_options=command_options,
            context_override=ctx.obj.get('context')
        )

        input_prompt = input_strings["input_prompt_file"]
        modified_code = input_strings["modified_code_file"]
        input_code = input_strings.get("input_code_file")
        time = ctx.obj.get('time', DEFAULT_TIME)

        if not modified_code.strip():
            raise ValueError("Modified code file cannot be empty when updating or generating a prompt.")

        if not input_prompt.strip():
            input_prompt = "no prompt exists yet, create a new one"
            input_code = ""
            if not ctx.obj.get("quiet", False):
                rprint("[bold yellow]Empty prompt file detected. Generating a new prompt from the modified code.[/bold yellow]")

        if use_git:
            if input_code_file:
                raise ValueError("Cannot use both --git and provide an input code file.")
            modified_prompt, total_cost, model_name = git_update(
                input_prompt=input_prompt,
                modified_code_file=modified_code_file,
                strength=ctx.obj.get("strength", 0.5),
                temperature=ctx.obj.get("temperature", 0),
                verbose=ctx.obj.get("verbose", False),
                time=time
            )
        else:
            if input_code is None:
                input_code = "" # Should only happen in generation mode
            modified_prompt, total_cost, model_name = update_prompt(
                input_prompt=input_prompt,
                input_code=input_code,
                modified_code=modified_code,
                strength=ctx.obj.get("strength", 0.5),
                temperature=ctx.obj.get("temperature", 0),
                verbose=ctx.obj.get("verbose", False),
                time=time
            )

        with open(output_file_paths["output"], "w") as f:
            f.write(modified_prompt)

        if not ctx.obj.get("quiet", False):
            rprint("[bold green]Prompt updated successfully.[/bold green]")
            rprint(f"[bold]Model used:[/bold] {model_name}")
            rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
            rprint(f"[bold]Updated prompt saved to:[/bold] {output_file_paths['output']}")

        return modified_prompt, total_cost, model_name

    except (ValueError, git.InvalidGitRepositoryError) as e:
        if not ctx.obj.get("quiet", False):
            rprint(f"[bold red]Input error:[/bold red] {str(e)}")
        sys.exit(1)
    except Exception as e:
        if not ctx.obj.get("quiet", False):
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        sys.exit(1)
