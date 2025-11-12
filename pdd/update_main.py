import sys
from typing import Tuple, Optional, List, Dict, Any
import click
from rich import print as rprint
import os
from pathlib import Path
import git
from rich.console import Console
from rich.progress import (
    Progress,
    SpinnerColumn,
    TextColumn,
    BarColumn,
    TimeRemainingColumn,
)
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

def resolve_prompt_code_pair(code_file_path: str, quiet: bool = False) -> Tuple[str, str]:
    """
    Derives the corresponding prompt file path from a code file path.
    If the prompt file does not exist, it creates an empty one.
    """
    language = get_language(os.path.splitext(code_file_path)[1])
    language = language.lower() if language else "unknown"
    
    base_path, _ = os.path.splitext(code_file_path)
    prompt_path_str = f"{base_path}_{language}.prompt"
    prompt_path = Path(prompt_path_str)

    if not prompt_path.exists():
        try:
            prompt_path.touch()
            if not quiet:
                console.print(f"[success]Created missing prompt file:[/success] [path]{prompt_path_str}[/path]")
        except OSError as e:
            console.print(f"[error]Failed to create file {prompt_path_str}: {e}[/error]")
            # Even if creation fails, return the intended path
    
    return prompt_path_str, code_file_path

def find_and_resolve_all_pairs(repo_root: str, quiet: bool = False, extensions: Optional[str] = None) -> List[Tuple[str, str]]:
    """
    Scans the repo for code files, resolves their prompt pairs, and returns all pairs.
    """
    pairs = []
    ignored_dirs = {'.git', '.idea', '.vscode', '__pycache__', 'node_modules', '.venv', 'venv', 'dist', 'build'}
    
    if not quiet:
        console.print(f"[info]Scanning repository and resolving prompt/code pairs...[/info]")

    allowed_extensions: Optional[set] = None
    if extensions:
        ext_list = [e.strip().lower() for e in extensions.split(',')]
        allowed_extensions = {f'.{e}' if not e.startswith('.') else e for e in ext_list}
        if not quiet:
            console.print(f"[info]Filtering for extensions: {', '.join(allowed_extensions)}[/info]")

    all_files = []
    for root, dirs, files in os.walk(repo_root, topdown=True):
        dirs[:] = [d for d in dirs if d not in ignored_dirs]
        for file in files:
            all_files.append(os.path.join(root, file))

    code_files = [
        f for f in all_files
        if (
            get_language(f) is not None and
            not f.endswith('.prompt') and
            not os.path.splitext(os.path.basename(f))[0].startswith('test_') and
            not os.path.splitext(os.path.basename(f))[0].endswith('_example')
        )
    ]

    if allowed_extensions:
        code_files = [
            f for f in code_files
            if os.path.splitext(f)[1].lower() in allowed_extensions
        ]
    
    for file_path in code_files:
        prompt_path, code_path = resolve_prompt_code_pair(file_path, quiet)
        pairs.append((prompt_path, code_path))
        
    return pairs

def update_file_pair(prompt_file: str, code_file: str, ctx: click.Context, repo: git.Repo) -> Dict[str, Any]:
    """
    Wrapper to update a single file pair, choosing the correct method based on Git status and prompt content.
    """
    try:
        # Read the prompt first to decide the strategy.
        try:
            with open(prompt_file, 'r') as f:
                input_prompt = f.read()
        except FileNotFoundError:
            input_prompt = ""

        relative_code_path = os.path.relpath(code_file, repo.working_tree_dir)
        is_untracked = relative_code_path in repo.untracked_files

        # GENERATION MODE: Trigger if the file is new OR if the prompt is empty.
        if is_untracked or not input_prompt.strip():
            if not ctx.obj.get("quiet", False):
                if is_untracked:
                    console.print(f"[info]New untracked file detected, generating new prompt for:[/info] [path]{relative_code_path}[/path]")
                else:
                    console.print(f"[info]Empty prompt detected, generating new prompt for:[/info] [path]{relative_code_path}[/path]")

            with open(code_file, 'r') as f:
                modified_code = f.read()

            modified_prompt, total_cost, model_name = update_prompt(
                input_prompt="no prompt exists yet, create a new one",
                input_code="",  # No previous version for generation
                modified_code=modified_code,
                strength=ctx.obj.get("strength", 0.5),
                temperature=ctx.obj.get("temperature", 0),
                verbose=ctx.obj.get("verbose", False),
                time=ctx.obj.get('time', DEFAULT_TIME),
            )
        # UPDATE MODE: Only trigger if the file is tracked AND the prompt has content.
        else:
            modified_prompt, total_cost, model_name = git_update(
                input_prompt=input_prompt,
                modified_code_file=code_file,
                strength=ctx.obj.get("strength", 0.5),
                temperature=ctx.obj.get("temperature", 0),
                verbose=ctx.obj.get("verbose", False),
                time=ctx.obj.get('time', DEFAULT_TIME),
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
    extensions: Optional[str] = None,
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
    :param extensions: Comma-separated string of file extensions to filter by in repo mode.
    :return: Tuple containing the updated prompt, total cost, and model name.
    """
    quiet = ctx.obj.get("quiet", False)
    if repo:
        try:
            # Find the repo root by searching up from the current directory
            repo_obj = git.Repo(os.getcwd(), search_parent_directories=True)
            repo_root = repo_obj.working_tree_dir
        except git.InvalidGitRepositoryError:
            rprint("[bold red]Error:[/bold red] Repository-wide mode requires the current directory to be within a Git repository.")
            sys.exit(1)

        pairs = find_and_resolve_all_pairs(repo_root, quiet, extensions)
        
        if not pairs:
            rprint("[info]No scannable code files found in the repository.[/info]")
            return None

        rprint(f"[info]Found {len(pairs)} total prompt/code pairs to process.[/info]")

        results = []
        total_repo_cost = 0.0

        progress = Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}", justify="right"),
            BarColumn(bar_width=None),
            TextColumn("[progress.percentage]{task.percentage:>3.1f}%"),
            TextColumn("•"),
            TimeRemainingColumn(),
            TextColumn("•"),
            TextColumn("Total Cost: $[bold green]{task.fields[total_cost]:.6f}[/bold green]"),
            console=console,
            transient=True,
        )

        with progress:
            task = progress.add_task(
                "Updating prompts...", 
                total=len(pairs),
                total_cost=0.0
            )
            
            for prompt_path, code_path in pairs:
                relative_path = os.path.relpath(code_path, repo_root)
                progress.update(task, description=f"Processing [path]{relative_path}[/path]")
                
                result = update_file_pair(prompt_path, code_path, ctx, repo_obj)
                results.append(result)
                
                total_repo_cost += result.get("cost", 0.0)
                
                progress.update(task, advance=1, total_cost=total_repo_cost)

        table = Table(show_header=True, header_style="bold magenta")
        table.add_column("Prompt File", style="dim", width=50)
        table.add_column("Status")
        table.add_column("Cost", justify="right")
        table.add_column("Model")
        table.add_column("Error", style="error")

        models_used = set()
        for res in sorted(results, key=lambda x: x["prompt_file"]):
            table.add_row(
                os.path.relpath(res["prompt_file"], repo_root),
                res["status"],
                f"${res['cost']:.6f}",
                res["model"],
                res["error"],
            )
            if res["model"]:
                models_used.add(res["model"])

        console.print("\n[bold]Repository Update Summary[/bold]")
        console.print(table)
        console.print(f"\n[bold]Total Estimated Cost: ${total_repo_cost:.6f}[/bold]")
        
        final_model_str = ", ".join(sorted(models_used)) if models_used else "N/A"
        return "Repository update complete.", total_repo_cost, final_model_str

    # --- Single file logic ---
    try:
        # Case 1: Regeneration Mode.
        # Triggered when ONLY the modified_code_file is provided.
        # This creates a new prompt or overwrites an existing one from scratch.
        is_regeneration_mode = (input_prompt_file is None and input_code_file is None)

        if is_regeneration_mode:
            if not quiet:
                rprint("[bold yellow]Regeneration mode: Creating or overwriting prompt from code file.[/bold yellow]")
            
            # This will derive the path and create the file if it doesn't exist.
            prompt_path, _ = resolve_prompt_code_pair(modified_code_file, quiet)

            with open(modified_code_file, 'r') as f:
                modified_code_content = f.read()

            # Directly call update_prompt in generation mode.
            modified_prompt, total_cost, model_name = update_prompt(
                input_prompt="no prompt exists yet, create a new one",
                input_code="",
                modified_code=modified_code_content,
                strength=ctx.obj.get("strength", 0.5),
                temperature=ctx.obj.get("temperature", 0),
                verbose=ctx.obj.get("verbose", False),
                time=ctx.obj.get('time', DEFAULT_TIME)
            )
            
            # Write the result to the derived/correct prompt path.
            with open(prompt_path, "w") as f:
                f.write(modified_prompt)
            
            if not quiet:
                rprint("[bold green]Prompt generated successfully.[/bold green]")
                rprint(f"[bold]Model used:[/bold] {model_name}")
                rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
                rprint(f"[bold]Prompt saved to:[/bold] {prompt_path}")

            return modified_prompt, total_cost, model_name

        # Case 2: True Update Mode.
        # Triggered when the user provides the prompt file, indicating a desire to update it.
        else:
            actual_input_prompt_file = input_prompt_file

            # Prepare input_file_paths for construct_paths
            input_file_paths = {
                "input_prompt_file": actual_input_prompt_file,
                "modified_code_file": modified_code_file
            }
            if input_code_file:
                input_file_paths["input_code_file"] = input_code_file

            # Determine output path
            final_output_path = output or actual_input_prompt_file
            command_options = {"output": final_output_path}
                
            _, input_strings, output_file_paths, _ = construct_paths(
                input_file_paths=input_file_paths,
                force=ctx.obj.get("force", False),
                quiet=quiet,
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
                if not use_git and input_code is None:
                    input_code = ""
                if not quiet:
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
                    # This will now only be triggered if --git is not used and no input_code_file is provided,
                    # which is an error state for a true update.
                    raise ValueError("For a true update, you must either provide an original code file or use the --git flag.")
                
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

            if not quiet:
                rprint("[bold green]Prompt updated successfully.[/bold green]")
                rprint(f"[bold]Model used:[/bold] {model_name}")
                rprint(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
                rprint(f"[bold]Updated prompt saved to:[/bold] {output_file_paths['output']}")

            return modified_prompt, total_cost, model_name

    except (ValueError, git.InvalidGitRepositoryError) as e:
        if not quiet:
            rprint(f"[bold red]Input error:[/bold red] {str(e)}")
        sys.exit(1)
    except Exception as e:
        if not quiet:
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        sys.exit(1)
