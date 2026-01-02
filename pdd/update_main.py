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

from .construct_paths import construct_paths, get_tests_dir_from_config, detect_context_for_file
from .get_language import get_language
from .update_prompt import update_prompt
from .git_update import git_update
from .agentic_common import get_available_agents
from .agentic_update import run_agentic_update
from . import DEFAULT_TIME

custom_theme = Theme({
    "info": "cyan",
    "warning": "yellow",
    "error": "bold red",
    "success": "green",
    "path": "dim blue",
})
console = Console(theme=custom_theme)

def resolve_prompt_code_pair(code_file_path: str, quiet: bool = False, output_dir: Optional[str] = None) -> Tuple[str, str]:
    """
    Derives the corresponding prompt file path from a code file path.
    Searches for and creates prompts only in the specified output directory or 'prompts' directory.
    If the prompt file does not exist, it creates an empty one in the target directory.

    Args:
        code_file_path: Path to the code file
        quiet: Whether to suppress output messages
        output_dir: Custom output directory (overrides default 'prompts' directory)
    """
    language = get_language(os.path.splitext(code_file_path)[1])
    language = language.lower() if language else "unknown"

    # Extract the filename without extension and directory
    code_filename = os.path.basename(code_file_path)
    base_name, _ = os.path.splitext(code_filename)

    # Determine the output directory
    if output_dir:
        # Use the custom output directory (absolute path)
        prompts_dir = os.path.abspath(output_dir)
    else:
        # Find the repository root (where the code file is located)
        code_file_abs_path = os.path.abspath(code_file_path)
        code_dir = os.path.dirname(code_file_abs_path)

        # For repository mode, find the actual repo root
        repo_root = code_dir
        try:
            import git
            repo = git.Repo(code_dir, search_parent_directories=True)
            repo_root = repo.working_tree_dir
        except:
            # If not a git repo, use the directory containing the code file
            pass

        # Use context-aware prompts_dir from .pddrc if available
        context_name, context_config = detect_context_for_file(code_file_path, repo_root)
        prompts_dir_config = context_config.get("prompts_dir", "prompts")
        if os.path.isabs(prompts_dir_config):
            prompts_dir = prompts_dir_config
        else:
            prompts_dir = os.path.join(repo_root, prompts_dir_config)

    # Construct the prompt filename in the determined directory
    prompt_filename = f"{base_name}_{language}.prompt"
    prompt_path_str = os.path.join(prompts_dir, prompt_filename)
    prompt_path = Path(prompt_path_str)

    # Ensure prompts directory exists
    prompts_path = Path(prompts_dir)
    if not prompts_path.exists():
        try:
            prompts_path.mkdir(parents=True, exist_ok=True)
            if not quiet:
                console.print(f"[success]Created prompts directory:[/success] [path]{prompts_dir}[/path]")
        except OSError as e:
            console.print(f"[error]Failed to create prompts directory {prompts_dir}: {e}[/error]")

    if not prompt_path.exists():
        try:
            prompt_path.touch()
            if not quiet:
                console.print(f"[success]Created missing prompt file:[/success] [path]{prompt_path_str}[/path]")
        except OSError as e:
            console.print(f"[error]Failed to create file {prompt_path_str}: {e}[/error]")
            # Even if creation fails, return the intended path

    return prompt_path_str, code_file_path

def find_and_resolve_all_pairs(repo_root: str, quiet: bool = False, extensions: Optional[str] = None, output_dir: Optional[str] = None) -> List[Tuple[str, str]]:
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
            get_language(os.path.splitext(f)[1]) and  # Pass extension, not full path
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
        prompt_path, code_path = resolve_prompt_code_pair(file_path, quiet, output_dir)
        pairs.append((prompt_path, code_path))
        
    return pairs

def update_file_pair(prompt_file: str, code_file: str, ctx: click.Context, repo: git.Repo, simple: bool = False) -> Dict[str, Any]:
    """
    Wrapper to update a single file pair, choosing the correct method based on Git status and prompt content.
    """
    try:
        verbose = ctx.obj.get("verbose", False)
        quiet = ctx.obj.get("quiet", False)

        # Agentic routing - try first before legacy paths
        use_agentic = not simple and get_available_agents()

        if use_agentic:
            tests_dir = get_tests_dir_from_config()
            success, message, agentic_cost, provider, changed_files = run_agentic_update(
                prompt_file=prompt_file,
                code_file=code_file,
                test_files=None,
                tests_dir=tests_dir,
                verbose=verbose,
                quiet=quiet,
            )

            if success:
                with open(prompt_file, 'r') as f:
                    modified_prompt = f.read()
                return {
                    "prompt_file": prompt_file,
                    "status": "✅ Success (agentic)",
                    "cost": agentic_cost,
                    "model": provider,
                    "error": "",
                }
            # Agentic failed - fall through to legacy

        # Legacy path: Read the prompt first to decide the strategy.
        try:
            with open(prompt_file, 'r') as f:
                input_prompt = f.read()
        except FileNotFoundError:
            input_prompt = ""

        relative_code_path = os.path.relpath(code_file, repo.working_tree_dir)
        is_untracked = relative_code_path in repo.untracked_files

        # GENERATION MODE: Trigger if the file is new OR if the prompt is empty.
        if is_untracked or not input_prompt.strip():
            if not quiet:
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
                verbose=verbose,
                time=ctx.obj.get('time', DEFAULT_TIME),
            )
        # UPDATE MODE: Only trigger if the file is tracked AND the prompt has content.
        else:
            modified_prompt, total_cost, model_name = git_update(
                input_prompt=input_prompt,
                modified_code_file=code_file,
                strength=ctx.obj.get("strength", 0.5),
                temperature=ctx.obj.get("temperature", 0),
                verbose=verbose,
                time=ctx.obj.get('time', DEFAULT_TIME),
                simple=True,  # Force legacy since we already tried agentic
                quiet=quiet,
                prompt_file=prompt_file,
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
    except click.Abort:
        # User cancelled - re-raise to stop the sync loop
        raise
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
    directory: Optional[str] = None,
    strength: Optional[float] = None,
    temperature: Optional[float] = None,
    simple: bool = False,
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
    :param directory: Optional directory to scan in repo mode (defaults to repo root).
    :param strength: Optional strength parameter (overrides ctx.obj if provided).
    :param temperature: Optional temperature parameter (overrides ctx.obj if provided).
    :return: Tuple containing the updated prompt, total cost, and model name.
    """
    quiet = ctx.obj.get("quiet", False)
    # Resolve strength/temperature (prefer passed parameters over ctx.obj)
    resolved_strength = strength if strength is not None else ctx.obj.get("strength", 0.5)
    resolved_temperature = temperature if temperature is not None else ctx.obj.get("temperature", 0)
    # Update ctx.obj so internal calls use the resolved values
    ctx.obj["strength"] = resolved_strength
    ctx.obj["temperature"] = resolved_temperature
    if repo:
        try:
            # Find the repo root by searching up from the current directory
            repo_obj = git.Repo(os.getcwd(), search_parent_directories=True)
            repo_root = repo_obj.working_tree_dir
        except git.InvalidGitRepositoryError:
            rprint("[bold red]Error:[/bold red] Repository-wide mode requires the current directory to be within a Git repository.")
            # Return error result instead of sys.exit(1) to allow orchestrator to handle gracefully
            return None

        # Use specified directory if provided, otherwise scan from repo root
        if directory:
            scan_dir = os.path.abspath(directory)
        else:
            scan_dir = repo_root
        pairs = find_and_resolve_all_pairs(scan_dir, quiet, extensions, output)
        
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
                
                result = update_file_pair(prompt_path, code_path, ctx, repo_obj, simple=simple)
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

            # Determine output path based on --output flag
            if output:
                # Check if output is a directory or file path
                if os.path.isdir(output) or output.endswith('/'):
                    # Output is a directory, pass as output_dir to resolve_prompt_code_pair
                    prompt_path, _ = resolve_prompt_code_pair(modified_code_file, quiet, output)
                else:
                    # Output is a specific file path, use it directly
                    prompt_path = os.path.abspath(output)
                    # Ensure the directory exists
                    os.makedirs(os.path.dirname(prompt_path), exist_ok=True)
            else:
                # No output specified, use default behavior
                prompt_path, _ = resolve_prompt_code_pair(modified_code_file, quiet)

            # Agentic routing for regeneration mode
            use_agentic = not simple and get_available_agents()
            verbose = ctx.obj.get("verbose", False)

            if use_agentic:
                # Ensure prompt file exists for agentic
                Path(prompt_path).touch(exist_ok=True)

                tests_dir = get_tests_dir_from_config()
                success, message, agentic_cost, provider, changed_files = run_agentic_update(
                    prompt_file=prompt_path,
                    code_file=modified_code_file,
                    test_files=None,
                    tests_dir=tests_dir,
                    verbose=verbose,
                    quiet=quiet,
                )

                if success:
                    with open(prompt_path, 'r') as f:
                        generated_prompt = f.read()

                    if not quiet:
                        rprint("[bold green]Prompt generated successfully (agentic).[/bold green]")
                        rprint(f"[bold]Provider:[/bold] {provider}")
                        rprint(f"[bold]Total cost:[/bold] ${agentic_cost:.6f}")
                        rprint(f"[bold]Prompt saved to:[/bold] {prompt_path}")

                    return generated_prompt, agentic_cost, provider

                # Agentic failed - fall through to legacy
                if not quiet:
                    rprint(f"[warning]Agentic failed: {message}. Falling back to legacy.[/warning]")

            # Legacy path
            with open(modified_code_file, 'r') as f:
                modified_code_content = f.read()

            modified_prompt, total_cost, model_name = update_prompt(
                input_prompt="no prompt exists yet, create a new one",
                input_code="",
                modified_code=modified_code_content,
                strength=ctx.obj.get("strength", 0.5),
                temperature=ctx.obj.get("temperature", 0),
                verbose=verbose,
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
            final_output_path = output or actual_input_prompt_file
            verbose = ctx.obj.get("verbose", False)

            # Agentic routing for true update mode (try before construct_paths)
            use_agentic = not simple and get_available_agents()

            if use_agentic:
                tests_dir = get_tests_dir_from_config()
                success, message, agentic_cost, provider, changed_files = run_agentic_update(
                    prompt_file=actual_input_prompt_file,
                    code_file=modified_code_file,
                    test_files=None,
                    tests_dir=tests_dir,
                    verbose=verbose,
                    quiet=quiet,
                )

                if success:
                    with open(actual_input_prompt_file, 'r') as f:
                        updated_prompt = f.read()

                    # Handle output path if different from input
                    if final_output_path != actual_input_prompt_file:
                        with open(final_output_path, 'w') as f:
                            f.write(updated_prompt)

                    if not quiet:
                        rprint("[bold green]Prompt updated successfully (agentic).[/bold green]")
                        rprint(f"[bold]Provider:[/bold] {provider}")
                        rprint(f"[bold]Total cost:[/bold] ${agentic_cost:.6f}")
                        rprint(f"[bold]Updated prompt saved to:[/bold] {final_output_path}")

                    return updated_prompt, agentic_cost, provider

                # Agentic failed - fall through to legacy
                if not quiet:
                    rprint(f"[warning]Agentic failed: {message}. Falling back to legacy.[/warning]")

            # Legacy path: Prepare input_file_paths for construct_paths
            input_file_paths = {
                "input_prompt_file": actual_input_prompt_file,
                "modified_code_file": modified_code_file
            }
            if input_code_file:
                input_file_paths["input_code_file"] = input_code_file

            command_options = {"output": final_output_path}

            _, input_strings, output_file_paths, _ = construct_paths(
                input_file_paths=input_file_paths,
                force=ctx.obj.get("force", False),
                quiet=quiet,
                command="update",
                command_options=command_options,
                context_override=ctx.obj.get('context'),
                confirm_callback=ctx.obj.get('confirm_callback')
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
                    verbose=verbose,
                    time=time,
                    simple=True if use_agentic else simple,  # Force legacy if agentic was tried
                    quiet=quiet,
                    prompt_file=actual_input_prompt_file,
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
                    verbose=verbose,
                    time=time
                )

            # Defense-in-depth: validate prompt is not empty before writing
            if not modified_prompt or not modified_prompt.strip():
                raise ValueError(
                    "Update produced an empty prompt. The LLM may have failed to generate a valid response."
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
        # Return error result instead of sys.exit(1) to allow orchestrator to handle gracefully
        return None
    except click.Abort:
        # User cancelled - re-raise to stop the sync loop
        raise
    except Exception as e:
        if not quiet:
            rprint(f"[bold red]Error:[/bold red] {str(e)}")
        # Return error result instead of sys.exit(1) to allow orchestrator to handle gracefully
        return None
