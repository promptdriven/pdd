import os
import asyncio
import json
import pathlib
import shlex
import subprocess
import requests
from typing import Optional, Tuple, Dict, Any, List

import click
from rich.console import Console
from rich.panel import Panel
from rich.text import Text

# Relative imports for PDD package structure
from . import DEFAULT_STRENGTH, DEFAULT_TIME, EXTRACTION_STRENGTH # Assuming these are in __init__.py
from .construct_paths import construct_paths
from .preprocess import preprocess as pdd_preprocess
from .code_generator import code_generator as local_code_generator_func
from .incremental_code_generator import incremental_code_generator as incremental_code_generator_func
from .get_jwt_token import get_jwt_token, AuthError, NetworkError, TokenError, UserCancelledError, RateLimitError

# Environment variable names for Firebase/GitHub auth
FIREBASE_API_KEY_ENV_VAR = "NEXT_PUBLIC_FIREBASE_API_KEY" 
GITHUB_CLIENT_ID_ENV_VAR = "GITHUB_CLIENT_ID"
PDD_APP_NAME = "PDD Code Generator"

# Cloud function URL
CLOUD_GENERATE_URL = "https://us-central1-prompt-driven-development.cloudfunctions.net/generateCode"
CLOUD_REQUEST_TIMEOUT = 400  # seconds

console = Console()

# --- Git Helper Functions ---
def _run_git_command(command: List[str], cwd: Optional[str] = None) -> Tuple[int, str, str]:
    """Runs a git command and returns (return_code, stdout, stderr)."""
    try:
        process = subprocess.run(command, capture_output=True, text=True, check=False, cwd=cwd, encoding='utf-8')
        return process.returncode, process.stdout.strip(), process.stderr.strip()
    except FileNotFoundError:
        return -1, "", "Git command not found. Ensure git is installed and in your PATH."
    except Exception as e:
        return -2, "", f"Error running git command {' '.join(command)}: {e}"

def is_git_repository(path: Optional[str] = None) -> bool:
    """Checks if the given path (or current dir) is a git repository."""
    start_path = pathlib.Path(path).resolve() if path else pathlib.Path.cwd()
    # Check for .git in current or any parent directory
    current_path = start_path
    while True:
        if (current_path / ".git").is_dir():
            # Verify it's the root of the work tree or inside it
            returncode, stdout, _ = _run_git_command(["git", "rev-parse", "--is-inside-work-tree"], cwd=str(start_path))
            return returncode == 0 and stdout == "true"
        parent = current_path.parent
        if parent == current_path: # Reached root directory
            break
        current_path = parent
    return False


def get_git_content_at_ref(file_path: str, git_ref: str = "HEAD") -> Optional[str]:
    """Gets the content of the file as it was at the specified git_ref."""
    abs_file_path = pathlib.Path(file_path).resolve()
    if not is_git_repository(str(abs_file_path.parent)):
        return None
    
    returncode_rev, git_root_str, stderr_rev = _run_git_command(["git", "rev-parse", "--show-toplevel"], cwd=str(abs_file_path.parent))
    if returncode_rev != 0:
        # console.print(f"[yellow]Git (rev-parse) warning for {file_path}: {stderr_rev}[/yellow]")
        return None
    
    git_root = pathlib.Path(git_root_str)
    try:
        relative_path = abs_file_path.relative_to(git_root)
    except ValueError:
        # console.print(f"[yellow]File {file_path} is not under git root {git_root}.[/yellow]")
        return None

    returncode, stdout, stderr = _run_git_command(["git", "show", f"{git_ref}:{relative_path.as_posix()}"], cwd=str(git_root))
    if returncode == 0:
        return stdout
    else:
        # File might not exist at that ref, or other git error.
        # if "does not exist" not in stderr and "exists on disk, but not in" not in stderr and console.is_terminal: # Be less noisy for common cases
        #     console.print(f"[yellow]Git (show) warning for {file_path} at {git_ref}: {stderr}[/yellow]")
        return None

def get_file_git_status(file_path: str) -> str:
    """Gets the git status of a single file (e.g., ' M', '??', 'A '). Empty if clean."""
    abs_file_path = pathlib.Path(file_path).resolve()
    if not is_git_repository(str(abs_file_path.parent)) or not abs_file_path.exists():
        return ""
    returncode, stdout, _ = _run_git_command(["git", "status", "--porcelain", str(abs_file_path)], cwd=str(abs_file_path.parent))
    if returncode == 0:
        # stdout might be " M path/to/file" or "?? path/to/file"
        # We only want the status codes part
        status_part = stdout.split(str(abs_file_path.name))[0].strip() if str(abs_file_path.name) in stdout else stdout.strip()
        return status_part
    return ""

def git_add_files(file_paths: List[str], verbose: bool = False) -> bool:
    """Stages the given files using 'git add'."""
    if not file_paths:
        return True
    
    # Resolve paths and ensure they are absolute for git command
    abs_paths = [str(pathlib.Path(fp).resolve()) for fp in file_paths]
    
    # Determine common parent directory to run git command from, or git root
    # For simplicity, assume they are in the same repo and run from one of their parents
    if not is_git_repository(str(pathlib.Path(abs_paths[0]).parent)):
        if verbose:
            console.print(f"[yellow]Cannot stage files: {abs_paths[0]} is not in a git repository.[/yellow]")
        return False
        
    returncode, _, stderr = _run_git_command(["git", "add"] + abs_paths, cwd=str(pathlib.Path(abs_paths[0]).parent))
    if returncode == 0:
        if verbose:
            console.print(f"Successfully staged: [cyan]{', '.join(abs_paths)}[/cyan]")
        return True
    else:
        console.print(f"[red]Error staging files with git:[/red] {stderr}")
        return False
# --- End Git Helper Functions ---


def code_generator_main(
    ctx: click.Context,
    prompt_file: str,
    output: Optional[str],
    original_prompt_file_path: Optional[str],
    force_incremental_flag: bool,
) -> Tuple[str, bool, float, str]:
    """
    CLI wrapper for generating code from prompts. Handles full and incremental generation,
    local vs. cloud execution, and output.
    """
    cli_params = ctx.obj or {}
    is_local_execution_preferred = cli_params.get('local', False)
    strength = cli_params.get('strength', DEFAULT_STRENGTH)
    temperature = cli_params.get('temperature', 0.0)
    time_budget = cli_params.get('time', DEFAULT_TIME)
    verbose = cli_params.get('verbose', False)
    force_overwrite = cli_params.get('force', False)
    quiet = cli_params.get('quiet', False)

    generated_code_content: Optional[str] = None
    was_incremental_operation = False
    total_cost = 0.0
    model_name = "unknown"

    input_file_paths_dict: Dict[str, str] = {"prompt_file": prompt_file}
    if original_prompt_file_path:
        input_file_paths_dict["original_prompt_file"] = original_prompt_file_path
    
    command_options: Dict[str, Any] = {"output": output}

    try:
        input_strings, output_file_paths, language = construct_paths(
            input_file_paths=input_file_paths_dict,
            force=force_overwrite,
            quiet=quiet,
            command="generate",
            command_options=command_options,
        )
        prompt_content = input_strings["prompt_file"]
        output_path = output_file_paths.get("output")

    except FileNotFoundError as e:
        console.print(f"[red]Error: Input file not found: {e.filename}[/red]")
        return "", False, 0.0, "error"
    except Exception as e:
        console.print(f"[red]Error during path construction: {e}[/red]")
        return "", False, 0.0, "error"

    can_attempt_incremental = False
    existing_code_content: Optional[str] = None
    original_prompt_content_for_incremental: Optional[str] = None

    if output_path and pathlib.Path(output_path).exists():
        try:
            existing_code_content = pathlib.Path(output_path).read_text(encoding="utf-8")
        except Exception as e:
            console.print(f"[yellow]Warning: Could not read existing output file {output_path}: {e}[/yellow]")
            existing_code_content = None

        if existing_code_content is not None:
            if "original_prompt_file" in input_strings:
                original_prompt_content_for_incremental = input_strings["original_prompt_file"]
                can_attempt_incremental = True
                if verbose:
                    console.print(f"Using specified original prompt: [cyan]{original_prompt_file_path}[/cyan]")
            elif is_git_repository(str(pathlib.Path(prompt_file).parent)):
                # prompt_content is the current on-disk version
                head_prompt_content = get_git_content_at_ref(prompt_file, git_ref="HEAD")

                if head_prompt_content is not None:
                    # Compare on-disk content (prompt_content) with HEAD content
                    if prompt_content.strip() != head_prompt_content.strip():
                        # Uncommitted changes exist. Original is HEAD, new is on-disk.
                        original_prompt_content_for_incremental = head_prompt_content
                        can_attempt_incremental = True
                        if verbose:
                            console.print(f"On-disk [cyan]{prompt_file}[/cyan] has uncommitted changes. Using HEAD version as original prompt.")
                    else:
                        # On-disk is identical to HEAD. Search for a prior *different* version.
                        if verbose:
                            console.print(f"On-disk [cyan]{prompt_file}[/cyan] matches HEAD. Searching for a prior *different* version as original prompt.")

                        new_prompt_candidate = head_prompt_content # This is also prompt_content (on-disk)
                        found_different_prior = False
                        
                        git_root_path_obj: Optional[pathlib.Path] = None
                        prompt_file_rel_to_root_str: Optional[str] = None

                        try:
                            abs_prompt_file_path = pathlib.Path(prompt_file).resolve()
                            temp_git_root_rc, temp_git_root_str, temp_git_root_stderr = _run_git_command(
                                ["git", "rev-parse", "--show-toplevel"], 
                                cwd=str(abs_prompt_file_path.parent)
                            )
                            if temp_git_root_rc == 0:
                                git_root_path_obj = pathlib.Path(temp_git_root_str)
                                prompt_file_rel_to_root_str = abs_prompt_file_path.relative_to(git_root_path_obj).as_posix()
                            elif verbose:
                                console.print(f"[yellow]Git (rev-parse) failed for {prompt_file}: {temp_git_root_stderr}. Cannot search history for prior different version.[/yellow]")
                        
                        except ValueError: # If file is not under git root
                             if verbose:
                                console.print(f"[yellow]File {prompt_file} not under a detected git root. Cannot search history.[/yellow]")
                        except Exception as e_git_setup:
                            if verbose:
                                console.print(f"[yellow]Error setting up git info for {prompt_file}: {e_git_setup}. Cannot search history.[/yellow]")

                        if git_root_path_obj and prompt_file_rel_to_root_str:
                            MAX_COMMITS_TO_SEARCH = 10  # How far back to look
                            log_cmd = ["git", "log", f"--pretty=format:%H", f"-n{MAX_COMMITS_TO_SEARCH}", "--", prompt_file_rel_to_root_str]
                            
                            log_rc, log_stdout, log_stderr = _run_git_command(log_cmd, cwd=str(git_root_path_obj))

                            if log_rc == 0 and log_stdout.strip():
                                shas = log_stdout.strip().split('\\n')
                                if verbose:
                                     console.print(f"Found {len(shas)} commits for [cyan]{prompt_file_rel_to_root_str}[/cyan] in recent history (up to {MAX_COMMITS_TO_SEARCH}).")

                                if len(shas) > 1: # Need at least one commit before the one matching head_prompt_content
                                    for prior_sha in shas[1:]: # Iterate starting from the commit *before* HEAD's version of the file
                                        if verbose:
                                            console.print(f"  Checking commit {prior_sha[:7]} for content of [cyan]{prompt_file}[/cyan]...")
                                        
                                        # get_git_content_at_ref uses the original prompt_file path, 
                                        # which it resolves internally relative to the git root.
                                        prior_content = get_git_content_at_ref(prompt_file, prior_sha) 
                                        
                                        if prior_content is not None:
                                            if prior_content.strip() != new_prompt_candidate.strip():
                                                original_prompt_content_for_incremental = prior_content
                                                can_attempt_incremental = True
                                                found_different_prior = True
                                                if verbose:
                                                    console.print(f"    [green]Found prior different version at commit {prior_sha[:7]}. Using as original prompt.[/green]")
                                                break 
                                            elif verbose:
                                                 console.print(f"    Content at {prior_sha[:7]} is identical to current HEAD. Skipping.")
                                        elif verbose:
                                            console.print(f"    Could not retrieve content for [cyan]{prompt_file}[/cyan] at commit {prior_sha[:7]}.")
                                else: 
                                    if verbose:
                                        console.print(f"  File [cyan]{prompt_file_rel_to_root_str}[/cyan] has less than 2 versions in recent history at this path.")
                            elif verbose:
                                console.print(f"[yellow]Git (log) failed for {prompt_file_rel_to_root_str} or no history found: {log_stderr}[/yellow]")
                        
                        if not found_different_prior:
                            original_prompt_content_for_incremental = new_prompt_candidate 
                            can_attempt_incremental = True 
                            if verbose:
                                console.print(
                                    f"[yellow]Warning: Could not find a prior *different* version of {prompt_file} "
                                    f"within the last {MAX_COMMITS_TO_SEARCH if git_root_path_obj else 'N/A'} relevant commits. "
                                    f"Using current HEAD version as original (prompts will be identical).[/yellow]"
                                )
                else:
                    # File not in HEAD, cannot determine git-based original prompt.
                    if verbose:
                        console.print(f"[yellow]Warning: Could not find committed version of {prompt_file} in git (HEAD) for incremental generation.[/yellow]")
            
            if force_incremental_flag and existing_code_content:
                if not (original_prompt_content_for_incremental or "original_prompt_file" in input_strings): # Check if original prompt is actually available
                     console.print(
                        "[yellow]Warning: --incremental flag used, but original prompt could not be determined. "
                        "Falling back to full generation.[/yellow]"
                    )
                else:
                    can_attempt_incremental = True 
    
    if force_incremental_flag and (not output_path or not pathlib.Path(output_path).exists()):
        console.print(
            "[yellow]Warning: --incremental flag used, but output file does not exist or path not specified. "
            "Performing full generation.[/yellow]"
        )
        can_attempt_incremental = False

    try:
        if can_attempt_incremental and existing_code_content is not None and original_prompt_content_for_incremental is not None:
            if verbose:
                console.print(Panel("Attempting incremental code generation...", title="[blue]Mode[/blue]", expand=False))

            if is_git_repository(str(pathlib.Path(prompt_file).parent)):
                files_to_stage_for_rollback: List[str] = []
                paths_to_check = [pathlib.Path(prompt_file).resolve()]
                if output_path and pathlib.Path(output_path).exists():
                    paths_to_check.append(pathlib.Path(output_path).resolve())

                for p_to_check in paths_to_check:
                    if not p_to_check.exists(): continue
                    
                    is_untracked = get_file_git_status(str(p_to_check)).startswith("??")
                    # Check if different from HEAD or untracked
                    is_different_from_head_rc = 1 if is_untracked else _run_git_command(["git", "diff", "--quiet", "HEAD", "--", str(p_to_check)], cwd=str(p_to_check.parent))[0]
                    
                    if is_different_from_head_rc != 0: # Different from HEAD or untracked
                        files_to_stage_for_rollback.append(str(p_to_check))
                
                if files_to_stage_for_rollback:
                    git_add_files(files_to_stage_for_rollback, verbose=verbose)
            
            generated_code_content, was_incremental_operation, total_cost, model_name = incremental_code_generator_func(
                original_prompt=original_prompt_content_for_incremental,
                new_prompt=prompt_content,
                existing_code=existing_code_content,
                language=language,
                strength=strength,
                temperature=temperature,
                time=time_budget,
                force_incremental=force_incremental_flag,
                verbose=verbose,
                preprocess_prompt=True
            )

            if not was_incremental_operation:
                if verbose:
                    console.print(Panel("Incremental generator suggested full regeneration. Falling back.", title="[yellow]Fallback[/yellow]", expand=False))
            elif verbose:
                console.print(Panel(f"Incremental update successful. Model: {model_name}, Cost: ${total_cost:.6f}", title="[green]Incremental Success[/green]", expand=False))

        if not was_incremental_operation: # Full generation path
            if verbose:
                console.print(Panel("Performing full code generation...", title="[blue]Mode[/blue]", expand=False))
            
            current_execution_is_local = is_local_execution_preferred
            
            if not current_execution_is_local:
                if verbose: console.print("Attempting cloud code generation...")
                
                processed_prompt_for_cloud = pdd_preprocess(prompt_content, recursive=True, double_curly_brackets=True, exclude_keys=[])
                if verbose: console.print(Panel(Text(processed_prompt_for_cloud, overflow="fold"), title="[cyan]Preprocessed Prompt for Cloud[/cyan]", expand=False))
                
                jwt_token: Optional[str] = None
                try:
                    firebase_api_key_val = os.environ.get(FIREBASE_API_KEY_ENV_VAR)
                    github_client_id_val = os.environ.get(GITHUB_CLIENT_ID_ENV_VAR)

                    if not firebase_api_key_val: raise AuthError(f"{FIREBASE_API_KEY_ENV_VAR} not set.")
                    if not github_client_id_val: raise AuthError(f"{GITHUB_CLIENT_ID_ENV_VAR} not set.")

                    jwt_token = asyncio.run(get_jwt_token(
                        firebase_api_key=firebase_api_key_val,
                        github_client_id=github_client_id_val,
                        app_name=PDD_APP_NAME
                    ))
                except (AuthError, NetworkError, TokenError, UserCancelledError, RateLimitError) as e:
                    console.print(f"[yellow]Cloud authentication/token error: {e}. Falling back to local execution.[/yellow]")
                    current_execution_is_local = True
                except Exception as e:
                    console.print(f"[yellow]Unexpected error during cloud authentication: {e}. Falling back to local execution.[/yellow]")
                    current_execution_is_local = True

                if jwt_token and not current_execution_is_local:
                    payload = {"promptContent": processed_prompt_for_cloud, "language": language, "strength": strength, "temperature": temperature, "verbose": verbose}
                    headers = {"Authorization": f"Bearer {jwt_token}", "Content-Type": "application/json"}
                    try:
                        response = requests.post(CLOUD_GENERATE_URL, json=payload, headers=headers, timeout=CLOUD_REQUEST_TIMEOUT)
                        response.raise_for_status()
                        
                        response_data = response.json()
                        generated_code_content = response_data.get("generatedCode")
                        total_cost = float(response_data.get("totalCost", 0.0))
                        model_name = response_data.get("modelName", "cloud_model")

                        if generated_code_content is None:
                            console.print("[yellow]Cloud execution returned no code. Falling back to local.[/yellow]")
                            current_execution_is_local = True
                        elif verbose:
                             console.print(Panel(f"Cloud generation successful. Model: {model_name}, Cost: ${total_cost:.6f}", title="[green]Cloud Success[/green]", expand=False))
                    except requests.exceptions.Timeout:
                        console.print(f"[yellow]Cloud execution timed out ({CLOUD_REQUEST_TIMEOUT}s). Falling back to local.[/yellow]")
                        current_execution_is_local = True
                    except requests.exceptions.HTTPError as e:
                        err_content = e.response.text[:200] if e.response else "No response content"
                        console.print(f"[yellow]Cloud HTTP error ({e.response.status_code}): {err_content}. Falling back to local.[/yellow]")
                        current_execution_is_local = True
                    except requests.exceptions.RequestException as e:
                        console.print(f"[yellow]Cloud network error: {e}. Falling back to local.[/yellow]")
                        current_execution_is_local = True
                    except json.JSONDecodeError:
                        console.print("[yellow]Cloud returned invalid JSON. Falling back to local.[/yellow]")
                        current_execution_is_local = True
            
            if current_execution_is_local:
                if verbose: console.print("Executing code generator locally...")
                generated_code_content, total_cost, model_name = local_code_generator_func(
                    prompt=prompt_content, language=language, strength=strength,
                    temperature=temperature, verbose=verbose
                )
                if verbose:
                    console.print(Panel(f"Local generation successful. Model: {model_name}, Cost: ${total_cost:.6f}", title="[green]Local Success[/green]", expand=False))
        
        if generated_code_content is not None:
            if output_path:
                p_output = pathlib.Path(output_path)
                p_output.parent.mkdir(parents=True, exist_ok=True)
                p_output.write_text(generated_code_content, encoding="utf-8")
                if verbose or not quiet:
                    console.print(f"Generated code saved to: [green]{p_output.resolve()}[/green]")
            elif not quiet: # No output path, print to console if not quiet
                console.print(Panel(Text(generated_code_content, overflow="fold"), title="[cyan]Generated Code[/cyan]", expand=True))
        else:
            console.print("[red]Error: Code generation failed. No code was produced.[/red]")
            return "", was_incremental_operation, total_cost, model_name or "error"

    except Exception as e:
        console.print(f"[red]An unexpected error occurred: {e}[/red]")
        import traceback
        if verbose: console.print(traceback.format_exc())
        return "", was_incremental_operation, total_cost, "error"
        
    return generated_code_content or "", was_incremental_operation, total_cost, model_name