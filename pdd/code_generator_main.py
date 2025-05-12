import asyncio
import json
import os
import shlex
import subprocess
from pathlib import Path
from typing import Optional, Tuple

import click
import requests
from rich.console import Console
from rich.markdown import Markdown
from rich.panel import Panel
from rich.syntax import Syntax

# Relative imports assuming this file is within the 'pdd' package directory
from .code_generator import code_generator
from .construct_paths import construct_paths
from .get_jwt_token import (AuthError, NetworkError, RateLimitError, TokenError,
                            UserCancelledError, get_jwt_token)
from .incremental_code_generator import incremental_code_generator
from .preprocess import preprocess
from . import DEFAULT_STRENGTH, EXTRACTION_STRENGTH # Imports from pdd/__init__.py

# Constants
CLOUD_FUNCTION_URL = "https://us-central1-prompt-driven-development.cloudfunctions.net/generateCode"
CLOUD_REQUEST_TIMEOUT = 60  # seconds for the actual request
# REACT_APP_FIREBASE_API_KEY and GITHUB_CLIENT_ID will be fetched from os.environ

console = Console()

def _run_git_command(command: str, cwd: Optional[str] = None) -> Tuple[bool, str]:
    """Helper to run a git command and return success status and output."""
    try:
        process = subprocess.run(shlex.split(command), capture_output=True, text=True, check=False, cwd=cwd, encoding='utf-8')
        if process.returncode == 0:
            return True, process.stdout.strip()
        return False, process.stderr.strip() if process.stderr else "Git command failed with no stderr."
    except FileNotFoundError:
        return False, "Git command not found. Ensure git is installed and in PATH."
    except Exception as e:
        return False, f"Error running git command '{command}': {e}"

def _get_git_root(start_path: Optional[str] = None) -> Optional[str]:
    """Gets the root directory of the git repository."""
    # If start_path is a file, use its parent directory
    cwd = None
    if start_path:
        p = Path(start_path)
        cwd = str(p.parent if p.is_file() else p)

    success, output = _run_git_command("git rev-parse --show-toplevel", cwd=cwd)
    return output if success else None

def _stage_file_if_needed(file_path_str: str, git_root: Optional[str], verbose: bool) -> None:
    """Stages a file in git if it's untracked or has unstaged modifications."""
    if not git_root:
        if verbose:
            console.print(f"[yellow]Not in a git repository. Skipping staging for {file_path_str}.[/yellow]")
        return

    file_path_obj = Path(file_path_str)
    if not file_path_obj.exists():
        # This can happen if output_code_path is for a new file, which is fine.
        # We only stage existing files that are being modified by incremental generation.
        if verbose:
            console.print(f"[yellow]File {file_path_str} does not exist. Skipping staging.[/yellow]")
        return

    abs_file_path = str(file_path_obj.resolve())
    try:
        rel_file_path = os.path.relpath(abs_file_path, git_root)
    except ValueError:
        if verbose:
            console.print(f"[yellow]File {file_path_str} is not under git root {git_root}. Skipping staging.[/yellow]")
        return

    quoted_rel_file_path = shlex.quote(rel_file_path)
    # Check git status
    # `git status --porcelain -- <file>` gives status like ' M file', '?? file'
    success, status_output = _run_git_command(f"git status --porcelain -- {quoted_rel_file_path}", cwd=git_root)

    if not success:
        # If file is not in git at all (e.g. in .gitignore but exists), status might fail or return empty.
        # If it's truly untracked, it will be '??'.
        # If `git status` command itself fails, print error.
        if "fatal: pathspec" in status_output and "did not match any files" in status_output :
             # This means the file is not known to git, effectively untracked for our purposes here.
             status_output = f"?? {rel_file_path}" # Mimic untracked status
        else:
            console.print(f"[red]Failed to get git status for {rel_file_path}: {status_output}[/red]")
            return


    status_line = status_output.strip()
    needs_staging = False

    if not status_line:  # Committed and unchanged
        if verbose:
            console.print(f"File {rel_file_path} is committed and unchanged.")
    elif status_line.startswith("??"):  # Untracked
        needs_staging = True
        if verbose:
            console.print(f"File {rel_file_path} is untracked.")
    # XY format: X=Index, Y=Worktree. We care if Worktree is Modified.
    elif len(status_line) >= 2 and status_line[1] == 'M':
        needs_staging = True
        if verbose:
            console.print(f"File {rel_file_path} has unstaged modifications (status: '{status_line}').")
    elif len(status_line) >=2 and status_line[0] == 'A' and status_line[1] == ' ': # Added to index, not modified since
        if verbose:
            console.print(f"File {rel_file_path} is staged for addition (status: '{status_line}').")
    else:
        if verbose:
            console.print(f"File {rel_file_path} status '{status_line}'. Assuming PDD does not need to stage it before modification.")

    if needs_staging:
        if verbose:
            console.print(f"Staging {rel_file_path} to capture current state before PDD modification...")
        add_success, add_output = _run_git_command(f"git add -- {quoted_rel_file_path}", cwd=git_root)
        if not add_success:
            console.print(f"[red]Failed to stage {rel_file_path}: {add_output}[/red]")
        elif verbose:
            console.print(f"[green]{rel_file_path} staged successfully.[/green]")


def code_generator_main(
    ctx: click.Context,
    prompt_file: str,
    output: Optional[str],
    original_prompt: Optional[str],
    incremental: bool, # This is the --incremental flag from CLI
    time: float,
) -> Tuple[str, bool, float, str]:
    """
    CLI wrapper for generating code from prompts.
    Reads a prompt file, generates code, and handles output location.
    Supports full and incremental generation, local and cloud execution.
    """
    verbose = ctx.obj.get("verbose", False)
    force_overwrite = ctx.obj.get("force", False)
    strength = ctx.obj.get("strength", DEFAULT_STRENGTH)
    temperature = ctx.obj.get("temperature", 0.0)
    run_local_mode = ctx.obj.get("local", False) # True if --local is passed

    generated_code_str: str = ""
    is_incremental_operation: bool = False
    total_cost_val: float = 0.0
    model_name_str: str = ""

    try:
        input_files_map = {"prompt_file": prompt_file}
        if original_prompt:
            input_files_map["original_prompt_file"] = original_prompt
        
        cli_command_options = {"output": output, "original_prompt": original_prompt, "incremental": incremental}

        input_strings_map, output_paths_map, lang = construct_paths(
            input_file_paths=input_files_map,
            force=force_overwrite,
            quiet=ctx.obj.get("quiet", False),
            command="generate",
            command_options=cli_command_options,
        )

        current_prompt_content = input_strings_map.get("prompt_file")
        if not current_prompt_content:
            console.print(f"[red]Error: Could not read prompt file '{prompt_file}'.[/red]")
            return "", False, 0.0, ""

        output_code_file_path_str = output_paths_map.get("output_code_file")
        output_code_file_path = Path(output_code_file_path_str) if output_code_file_path_str else None

        if not lang:
            console.print(f"[red]Error: Could not determine language from prompt file '{prompt_file}'.[/red]")
            return "", False, 0.0, ""
        
        if verbose:
            console.print(f"Language determined: [cyan]{lang}[/cyan]")
            if output_code_file_path:
                console.print(f"Output path: [cyan]{output_code_file_path}[/cyan]")
            else: # Should not happen if construct_paths provides a default
                console.print("[yellow]Warning: No output path determined by construct_paths.[/yellow]")

        # --- Determine Generation Mode (Incremental vs. Full) ---
        attempt_incremental_gen = False
        original_prompt_str_for_inc: Optional[str] = None
        existing_code_str_for_inc: Optional[str] = None
        
        # Get git root based on the prompt file's location to handle relative paths correctly
        git_repo_root = _get_git_root(prompt_file)

        if output_code_file_path and output_code_file_path.exists():
            # Condition 1: Output file exists. Now check for original prompt.
            if input_strings_map.get("original_prompt_file"): # --original-prompt was provided
                original_prompt_str_for_inc = input_strings_map["original_prompt_file"]
                attempt_incremental_gen = True
                if verbose:
                    console.print(f"[cyan]Using provided original prompt file: {original_prompt}[/cyan]")
            elif git_repo_root: # Try to get from git
                abs_prompt_file = Path(prompt_file).resolve()
                rel_prompt_to_git_root = os.path.relpath(abs_prompt_file, git_repo_root)
                
                git_success, git_orig_prompt = _run_git_command(
                    f"git show HEAD:{shlex.quote(rel_prompt_to_git_root)}",
                    cwd=git_repo_root
                )
                if git_success:
                    original_prompt_str_for_inc = git_orig_prompt
                    attempt_incremental_gen = True
                    if verbose:
                        console.print(f"[cyan]Using last committed version of '{prompt_file}' from git as original prompt.[/cyan]")
                elif verbose:
                    console.print(f"[yellow]Could not get last committed version of '{prompt_file}' from git: {git_orig_prompt}.[/yellow]")
            
            if attempt_incremental_gen:
                try:
                    existing_code_str_for_inc = output_code_file_path.read_text(encoding="utf-8")
                except Exception as e:
                    console.print(f"[red]Error reading existing code from '{output_code_file_path}': {e}[/red]")
                    attempt_incremental_gen = False # Cannot do incremental
            
            if incremental and not attempt_incremental_gen: # --incremental flag but couldn't set up
                 console.print(f"[yellow]Warning: --incremental flag was set, but failed to prepare for incremental generation (e.g., no original prompt). Performing full generation.[/yellow]")
            elif incremental and attempt_incremental_gen: # --incremental flag and we are ready
                if verbose: console.print("[cyan]--incremental flag is set, proceeding with incremental attempt.[/cyan]")
            elif not incremental and attempt_incremental_gen: # No --incremental flag, but we found changes and an original
                if verbose: console.print("[cyan]Changes detected and original prompt available. Attempting incremental generation automatically.[/cyan]")


        elif incremental: # --incremental flag but output file does not exist
             console.print(f"[yellow]Warning: --incremental flag was set, but output file '{output_code_file_path or output}' does not exist. Performing full generation.[/yellow]")
             attempt_incremental_gen = False


        # --- Perform Incremental Generation if conditions met ---
        if attempt_incremental_gen and original_prompt_str_for_inc and existing_code_str_for_inc:
            if verbose:
                console.print(Panel("[bold blue]Attempting Incremental Code Generation[/bold blue]", expand=False))

            if git_repo_root: # Stage files before modification if in git repo
                _stage_file_if_needed(prompt_file, git_repo_root, verbose)
                if output_code_file_path: # Must exist for incremental
                     _stage_file_if_needed(str(output_code_file_path), git_repo_root, verbose)
            
            try:
                # `incremental` (CLI flag) is passed as `force_incremental`
                updated_code, was_inc, cost, model_name = incremental_code_generator(
                    original_prompt=original_prompt_str_for_inc,
                    new_prompt=current_prompt_content,
                    existing_code=existing_code_str_for_inc,
                    language=lang,
                    strength=strength,
                    temperature=temperature,
                    time=time,
                    force_incremental=incremental, # Pass the CLI --incremental flag here
                    verbose=verbose,
                    preprocess_prompt=True 
                )
                if was_inc:
                    generated_code_str = updated_code
                    is_incremental_operation = True
                    total_cost_val = cost
                    model_name_str = model_name
                    if verbose:
                        console.print("[green]Incremental generation successful.[/green]")
                else: # Incremental generator decided full regeneration is better
                    if verbose:
                        console.print("[yellow]Incremental generator suggested full regeneration. Proceeding with full generation.[/yellow]")
            except Exception as e:
                console.print(f"[red]Error during incremental code generation: {e}[/red]")
                if verbose:
                    import traceback
                    console.print(f"Traceback: {traceback.format_exc()}")
                console.print("[yellow]Falling back to full code generation.[/yellow]")
        
        # --- Perform Full Generation if not incremental or if incremental failed/suggested fallback ---
        if not is_incremental_operation:
            if verbose:
                 title = "Proceeding with Full Code Generation" if attempt_incremental_gen else "Starting Full Code Generation"
                 console.print(Panel(f"[bold blue]{title}[/bold blue]", expand=False))
            
            effective_run_local = run_local_mode # Start with the flag's value
            
            if not run_local_mode: # Try cloud if --local is not set
                if verbose: console.print("Attempting cloud execution...")
                processed_prompt_for_cloud = preprocess(current_prompt_content, recursive=True, double_curly_brackets=True, exclude_keys=[])
                if verbose:
                    console.print(Panel(Markdown(f"```markdown\n{processed_prompt_for_cloud}\n```"), title="Processed Prompt for Cloud"))
                
                try:
                    firebase_api_key = os.environ.get("REACT_APP_FIREBASE_API_KEY")
                    github_client_id = os.environ.get("GITHUB_CLIENT_ID")

                    if not firebase_api_key:
                        console.print("[yellow]REACT_APP_FIREBASE_API_KEY not found in environment. Cannot use cloud execution.[/yellow]")
                        raise ValueError("Missing Firebase API Key for cloud execution.")
                    if not github_client_id:
                        console.print("[yellow]GITHUB_CLIENT_ID not found in environment. Cannot use cloud execution.[/yellow]")
                        raise ValueError("Missing GitHub Client ID for cloud execution.")

                    jwt_token = asyncio.run(get_jwt_token(
                        firebase_api_key=firebase_api_key,
                        github_client_id=github_client_id,
                        app_name="Prompt Driven Development CLI"
                    ))

                    payload = {
                        "promptContent": processed_prompt_for_cloud, "language": lang,
                        "strength": strength, "temperature": temperature,
                        "time": time, "verbose": verbose,
                    }
                    headers = {"Authorization": f"Bearer {jwt_token}", "Content-Type": "application/json"}
                    
                    response = requests.post(CLOUD_FUNCTION_URL, json=payload, headers=headers, timeout=CLOUD_REQUEST_TIMEOUT)
                    response.raise_for_status()
                    
                    result = response.json()
                    generated_code_str = result.get("code", "")
                    total_cost_val = float(result.get("cost", 0.0))
                    model_name_str = result.get("model_name", "cloud_model")
                    if verbose:
                        console.print(f"[green]Cloud code generation successful. Model: {model_name_str}, Cost: ${total_cost_val:.6f}[/green]")
                
                except (requests.RequestException, json.JSONDecodeError, ValueError, KeyError) as e: # Common operational errors
                    console.print(f"[yellow]Cloud execution failed: {e}.[/yellow]")
                    console.print("[yellow]Falling back to local execution.[/yellow]")
                    effective_run_local = True
                except (AuthError, NetworkError, TokenError, RateLimitError) as e: # Auth specific errors
                    console.print(f"[red]Cloud authentication/token error: {e}.[/red]")
                    console.print("[yellow]Falling back to local execution (if API keys are set).[/yellow]")
                    effective_run_local = True
                except UserCancelledError:
                    console.print("[red]Cloud authentication cancelled by user. Cannot proceed with cloud execution.[/red]")
                    console.print("[yellow]Falling back to local execution (if API keys are set).[/yellow]")
                    effective_run_local = True # Fallback, though local might also need keys
                except Exception as e: # Catch-all for other unexpected errors during cloud attempt
                    console.print(f"[red]An unexpected error occurred during cloud execution: {e}[/red]")
                    if verbose:
                        import traceback
                        console.print(f"Traceback: {traceback.format_exc()}")
                    console.print("[yellow]Falling back to local execution.[/yellow]")
                    effective_run_local = True

            if effective_run_local:
                if verbose: console.print("Performing local code generation...")
                try:
                    generated_code_str, total_cost_val, model_name_str = code_generator(
                        prompt=current_prompt_content, # Use original prompt for local
                        language=lang,
                        strength=strength,
                        temperature=temperature,
                        verbose=verbose,
                    )
                    if verbose:
                         console.print(f"[green]Local code generation successful. Model: {model_name_str}, Cost: ${total_cost_val:.6f}[/green]")
                except Exception as e:
                    console.print(f"[red]Error during local code generation: {e}[/red]")
                    if verbose:
                        import traceback
                        console.print(f"Traceback: {traceback.format_exc()}")
                    # Generation failed, return any partial cost/model info if available
                    return generated_code_str, is_incremental_operation, total_cost_val, model_name_str

        # --- Save the generated code ---
        if generated_code_str and output_code_file_path:
            try:
                output_code_file_path.parent.mkdir(parents=True, exist_ok=True)
                output_code_file_path.write_text(generated_code_str, encoding="utf-8")
                if verbose:
                    console.print(f"Generated code saved to: [link=file://{output_code_file_path.resolve()}]{output_code_file_path}[/link]")
                else:
                    console.print(f"Generated code saved to: {output_code_file_path}")
            except Exception as e:
                console.print(f"[red]Error saving generated code to '{output_code_file_path}': {e}[/red]")
        elif generated_code_str and not output_code_file_path:
            console.print("[yellow]No output file path determined. Displaying generated code:[/yellow]")
            console.print(Syntax(generated_code_str, lang, theme="monokai", line_numbers=True))
        
        if verbose and generated_code_str:
            console.print(Panel(Syntax(generated_code_str, lang, theme="monokai", line_numbers=True), title="Final Generated Code"))
        
        return generated_code_str, is_incremental_operation, total_cost_val, model_name_str

    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred in code_generator_main: {e}[/bold red]")
        if verbose:
            import traceback
            console.print(traceback.format_exc())
        return "", False, 0.0, ""
