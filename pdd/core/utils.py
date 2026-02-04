"""
Helper functions for the PDD CLI.
"""
import os
import sys
import subprocess
from pathlib import Path
from typing import Optional
import click

from ..install_completion import (
    get_current_shell,
    get_shell_rc_path,
)

def _first_pending_command(ctx: click.Context) -> Optional[str]:
    """Return the first subcommand scheduled for this invocation."""
    for arg in ctx.protected_args:
        if not arg.startswith("-"):
            return arg
    return None


def _api_env_exists() -> bool:
    """Check whether the ~/.pdd/api-env file exists."""
    return (Path.home() / ".pdd" / "api-env").exists()


def _completion_installed() -> bool:
    """Check if the shell RC file already sources the PDD completion script."""
    shell = get_current_shell()
    rc_path = get_shell_rc_path(shell) if shell else None
    if not rc_path:
        return False

    try:
        content = Path(rc_path).read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return False

    return "PDD CLI completion" in content or "pdd_completion" in content


def _project_has_local_configuration() -> bool:
    """Detect project-level env configuration that should suppress reminders."""
    cwd = Path.cwd()

    env_file = cwd / ".env"
    if env_file.exists():
        try:
            env_content = env_file.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            env_content = ""
        if any(token in env_content for token in ("OPENAI_API_KEY=", "GOOGLE_API_KEY=", "ANTHROPIC_API_KEY=")):
            return True

    project_pdd_dir = cwd / ".pdd"
    if project_pdd_dir.exists():
        return True

    return False


def _should_show_onboarding_reminder(ctx: click.Context) -> bool:
    """Determine whether to display the onboarding reminder banner."""
    suppress = os.getenv("PDD_SUPPRESS_SETUP_REMINDER", "").lower()
    if suppress in {"1", "true", "yes"}:
        return False

    first_command = _first_pending_command(ctx)
    if first_command == "setup":
        return False

    if _api_env_exists():
        return False

    if _project_has_local_configuration():
        return False

    if _completion_installed():
        return False

    return True


def _run_setup_utility() -> None:
    """Execute the interactive setup utility script."""
    result = subprocess.run([sys.executable, "-m", "pdd.setup_tool"])
    if result.returncode not in (0, None):
        raise RuntimeError(f"Setup utility exited with status {result.returncode}")
