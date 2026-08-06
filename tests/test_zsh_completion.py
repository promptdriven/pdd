"""Regression tests for the shipped Zsh completion dispatcher."""

from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
COMPLETION = ROOT / "pdd" / "pdd_completion.zsh"


def _resolved_subcommand(*words: str) -> str:
    """Source the completion file and return its parsed command token."""
    invocation = " ".join(words)
    result = subprocess.run(
        [
            "zsh",
            "-fc",
            (
                f"source {COMPLETION}; "
                f"words=({invocation}); CURRENT=${{#words}}; "
                "_pdd_find_subcommand"
            ),
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
