import os
import sys
import importlib.resources
from typing import Optional

import click
from rich import print as rprint

# ----------------------------------------------------------------------
# Dynamically determine PDD_PATH at runtime.
# ----------------------------------------------------------------------
def get_local_pdd_path() -> str:
    """
    Return the PDD_PATH directory.
    First check the environment variable. If not set, attempt to
    deduce it via importlib.resources. If that fails, abort.
    """
    if "PDD_PATH" in os.environ:
        return os.environ["PDD_PATH"]
    else:
        try:
            p = importlib.resources.files("pdd").joinpath("cli.py")
            fallback_path = str(p.parent)
            # Also set it back into the environment for consistency
            os.environ["PDD_PATH"] = fallback_path
            return fallback_path
        except ImportError:
            rprint(
                "[red]Error: Could not determine the path to the 'pdd' package. "
                "Please set the PDD_PATH environment variable manually.[/red]"
            )
            sys.exit(1)

# ----------------------------------------------------------------------
# Simplified shell RC path logic
# ----------------------------------------------------------------------
def get_shell_rc_path(shell: str) -> Optional[str]:
    """Return the default RC file path for a given shell name."""
    home = os.path.expanduser("~")
    if shell == "bash":
        return os.path.join(home, ".bashrc")
    elif shell == "zsh":
        return os.path.join(home, ".zshrc")
    elif shell == "fish":
        return os.path.join(home, ".config", "fish", "config.fish")
    return None


def get_current_shell() -> Optional[str]:


    """Determine the currently running shell more reliably."""
    if not os.environ.get('PYTEST_CURRENT_TEST'):
        # Method 1: Check process name using 'ps'
        try:
            import subprocess
            result = subprocess.run(['ps', '-p', str(os.getppid()), '-o', 'comm='], 
                                capture_output=True, text=True)
            if result.returncode == 0:
                # Strip whitespace and get basename without path
                shell = os.path.basename(result.stdout.strip())
                # Remove leading dash if present (login shell)
                return shell.lstrip('-')
        except (subprocess.SubprocessError, FileNotFoundError):
            pass

        # Method 2: Check $0 special parameter
        try:
            result = subprocess.run(['sh', '-c', 'echo "$0"'], 
                                capture_output=True, text=True)
            if result.returncode == 0:
                shell = os.path.basename(result.stdout.strip())
                return shell.lstrip('-')
        except (subprocess.SubprocessError, FileNotFoundError):
            pass

    # Fallback to SHELL env var if all else fails
    return os.path.basename(os.environ.get("SHELL", ""))


def get_completion_script_extension(shell: str) -> str:
    """Get the appropriate file extension for shell completion scripts."""
    mapping = {
        "bash": "sh",
        "zsh": "zsh",
        "fish": "fish"
    }
    return mapping.get(shell, shell)


def install_completion(quiet: bool = False):
    """
    Install shell completion for the PDD CLI by detecting the user's shell,
    copying the relevant completion script, and appending a source command
    to the user's shell RC file if not already present.
    """
    shell = get_current_shell()
    rc_file = get_shell_rc_path(shell)
    if not rc_file:
        if not quiet:
            rprint(f"[red]Unsupported shell: {shell}[/red]")
        raise click.Abort()

    ext = get_completion_script_extension(shell)

    # Dynamically look up the local path at runtime:
    local_pdd_path = get_local_pdd_path()
    completion_script_path = os.path.join(local_pdd_path, f"pdd_completion.{ext}")

    if not os.path.exists(completion_script_path):
        if not quiet:
            rprint(f"[red]Completion script not found: {completion_script_path}[/red]")
        raise click.Abort()

    source_command = f"source {completion_script_path}"

    try:
        # Ensure the RC file exists (create if missing).
        if not os.path.exists(rc_file):
            # Create parent directories if they don't exist
            rc_dir = os.path.dirname(rc_file)
            if rc_dir: # Ensure rc_dir is not an empty string (e.g. if rc_file is in current dir)
                 os.makedirs(rc_dir, exist_ok=True)
            with open(rc_file, "w", encoding="utf-8") as cf:
                cf.write("") # Create an empty file

        # Read existing content
        with open(rc_file, "r", encoding="utf-8") as cf:
            content = cf.read()

        if source_command not in content:
            with open(rc_file, "a", encoding="utf-8") as rf:
                rf.write(f"\n# PDD CLI completion\n{source_command}\n")
            
            if not quiet:
                rprint(f"[green]Shell completion installed for {shell}.[/green]")
                rprint(f"Please restart your shell or run 'source {rc_file}' to enable completion.")
        else:
            if not quiet:
                rprint(f"[yellow]Shell completion already installed for {shell}.[/yellow]")
    except OSError as exc:
        if not quiet:
            rprint(f"[red]Failed to install shell completion: {exc}[/red]")
        raise click.Abort()