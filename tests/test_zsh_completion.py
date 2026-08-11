"""Regression tests for the shipped Zsh completion dispatcher."""

from pathlib import Path
import shutil
import subprocess

import pytest


ROOT = Path(__file__).resolve().parents[1]
COMPLETION = ROOT / "pdd" / "pdd_completion.zsh"

pytestmark = pytest.mark.skipif(shutil.which("zsh") is None, reason="requires zsh")


def _resolved_subcommand(*words: str) -> str:
    """Source the completion file and return its parsed command token."""
    result = subprocess.run(
        [
            "zsh",
            "-fc",
            'source "$1"; shift; words=("$@"); CURRENT=${#words}; _pdd_find_subcommand',
            "zsh",
            str(COMPLETION),
            *words,
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def test_zsh_completion_resolves_sync_after_local_global_option() -> None:
    """`pdd --local sync` must use sync-specific completion."""
    assert _resolved_subcommand("pdd", "--local", "sync", "--skip") == "sync"


def test_zsh_completion_skips_value_of_global_option_before_sync() -> None:
    """A global option's value must not be mistaken for the command."""
    assert _resolved_subcommand("pdd", "--context", "local", "sync") == "sync"


def test_zsh_completion_resolves_current_cli_command_after_global_option() -> None:
    """Global options must also work with commands added after this script."""
    assert _resolved_subcommand("pdd", "--local", "validate") == "validate"


def test_zsh_completion_does_not_skip_unknown_global_option() -> None:
    """Misspelled options must not dispatch completion for a later command."""
    assert _resolved_subcommand("pdd", "--modle", "claude", "sync") == ""
