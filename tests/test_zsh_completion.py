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
        check=False,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def _completion_output(*words: str) -> str:
    """Run the dispatcher with completion helpers replaced by observable stubs."""
    result = subprocess.run(
        [
            "zsh",
            "-fc",
            (
                'source "$1"; shift; '
                '_arguments() { print -r -- "arguments:$*"; state=group_command; return 1; }; '
                '_describe() { local name="${@: -1}"; '
                'print -r -- "describe:${(j: :)${(P)name}}"; return 0; }; '
                'words=("$@"); CURRENT=${#words}; curcontext=:completion::; _pdd'
            ),
            "zsh",
            str(COMPLETION),
            *words,
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    return result.stdout


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


@pytest.mark.parametrize(
    "words",
    [
        ("pdd", "--force", "sync"),
        ("pdd", "--verbose", "sync"),
        ("pdd", "--quiet", "sync"),
        ("pdd", "--color", "sync"),
        ("pdd", "--no-color", "sync"),
        ("pdd", "--estimate", "sync"),
        ("pdd", "--dry-run-cost", "sync"),
        ("pdd", "--estimate-json", "sync"),
        ("pdd", "--review-examples", "sync"),
        ("pdd", "--local", "sync"),
        ("pdd", "--core-dump", "sync"),
        ("pdd", "--no-core-dump", "sync"),
        ("pdd", "--compress-examples", "sync"),
        ("pdd", "--compress-test-context", "sync"),
        ("pdd", "--strength", "0.5", "sync"),
        ("pdd", "--strength=0.5", "sync"),
        ("pdd", "--model", "claude", "sync"),
        ("pdd", "--model=claude", "sync"),
        ("pdd", "--temperature", "0.5", "sync"),
        ("pdd", "--temperature=0.5", "sync"),
        ("pdd", "--time", "0.5", "sync"),
        ("pdd", "--time=0.5", "sync"),
        ("pdd", "--output-cost", "costs.csv", "sync"),
        ("pdd", "--output-cost=costs.csv", "sync"),
        ("pdd", "--context", "local", "sync"),
        ("pdd", "--context=local", "sync"),
        ("pdd", "--keep-core-dumps", "2", "sync"),
        ("pdd", "--keep-core-dumps=2", "sync"),
        ("pdd", "--context-compression", "all", "sync"),
        ("pdd", "--context-compression=all", "sync"),
        ("pdd", "--compression-fallback", "full", "sync"),
        ("pdd", "--compression-fallback=full", "sync"),
    ],
)
def test_zsh_completion_resolves_sync_after_each_global_option(words: tuple[str, ...]) -> None:
    """Every non-eager global option reaches sync in both supported forms."""
    assert _resolved_subcommand(*words) == "sync"


def test_zsh_completion_supports_option_terminator_before_command() -> None:
    """Click accepts a subcommand after a literal option terminator."""
    assert _resolved_subcommand("pdd", "--", "sync") == "sync"


@pytest.mark.parametrize("option", ("--help", "--version", "--list-contexts"))
def test_zsh_completion_does_not_dispatch_after_eager_global_option(option: str) -> None:
    """Eager global options exit before a later command can execute."""
    assert _resolved_subcommand("pdd", option, "sync") == ""


def test_zsh_completion_dispatches_sync_specific_completion() -> None:
    """The dispatcher, not just the parser, selects sync completion."""
    assert "--skip-verify" in _completion_output("pdd", "--local", "sync")


@pytest.mark.parametrize(
    ("group", "command"),
    [
        ("auth", "login"),
        ("templates", "list"),
        ("contracts", "check"),
        ("sessions", "cleanup"),
        ("story", "link"),
        ("firecrawl-cache", "stats"),
    ],
)
def test_zsh_completion_dispatches_group_subcommands(group: str, command: str) -> None:
    """Groups reached after a global option offer their registered subcommands."""
    assert command in _completion_output("pdd", "--local", group)
