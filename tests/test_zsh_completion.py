"""Regression tests for the shipped Zsh completion dispatcher."""

from pathlib import Path
import shutil
import subprocess
import time

import pexpect
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


def _native_completion_output(command: str) -> str:
    """Complete *command* through Zsh's real interactive completion frame.

    Do not replace `_arguments`, `_describe`, or `state`: doing so can hide
    positional parsing bugs in the completion function itself.
    """
    shell = pexpect.spawn(
        "zsh", ["-f", "-i"], encoding="utf-8", timeout=5, dimensions=(40, 160)
    )
    shell.delaybeforesend = 0.01
    try:
        shell.expect_exact("% ")
        shell.sendline("PROMPT='PDD_PROMPT> '")
        # The first match is echoed input; the second is the rendered prompt.
        shell.expect_exact("PDD_PROMPT> ")
        shell.expect_exact("PDD_PROMPT> ")
        shell.sendline(
            f"autoload -Uz compinit; compinit -D -i; source {COMPLETION}; compdef _pdd pdd"
        )
        shell.expect_exact("PDD_PROMPT> ")
        shell.send(command)
        time.sleep(0.05)
        shell.sendcontrol("i")
        # ZLE renders candidates asynchronously on the PTY.  Drain until it
        # has been quiet briefly: the first read often contains only the
        # echoed command, while candidates arrive in a later terminal write.
        completion_parts: list[str] = []
        while True:
            try:
                completion_parts.append(shell.read_nonblocking(10_000, timeout=0.2))
            except pexpect.TIMEOUT:
                break
        completion_output = "".join(completion_parts)
        # A unique candidate is inserted into ZLE's buffer rather than printed.
        # Cancel instead of accepting the buffer: accepting it executes the real
        # PDD command (which may wait on network or project state).
        shell.sendcontrol("c")
        shell.expect_exact("PDD_PROMPT> ")
        return completion_output + shell.before
    finally:
        shell.close(force=True)


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
        ("pdd", "typo", "sync"),
        ("pdd", "--", "typo", "sync"),
    ],
)
def test_zsh_completion_stops_at_the_first_invalid_command_token(words: tuple[str, ...]) -> None:
    """Click treats the first bare token as the command, even after `--`."""
    assert _resolved_subcommand(*words) == ""


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
    """A global option still reaches sync in a real Zsh completion context."""
    assert "--skip-verify" in _native_completion_output("pdd --local sync --skip-")


@pytest.mark.parametrize("prefix", ("--mo", "--context-com"))
def test_zsh_completion_offers_new_global_options(prefix: str) -> None:
    """Global option suggestions are tested through `_arguments`, not the scanner."""
    expected = "--model" if prefix == "--mo" else "--context-compression"
    assert expected in _native_completion_output(f"pdd {prefix}")


@pytest.mark.parametrize(
    ("prefix", "group", "command"),
    [
        ("", "auth", "login"),
        ("--local ", "auth", "login"),
        ("", "templates", "list"),
        ("--local ", "templates", "list"),
        ("", "contracts", "check"),
        ("--local ", "contracts", "check"),
        ("", "sessions", "cleanup"),
        ("--local ", "sessions", "cleanup"),
        ("", "story", "link"),
        ("--local ", "story", "link"),
        ("", "firecrawl-cache", "stats"),
        ("--local ", "firecrawl-cache", "stats"),
    ],
)
def test_zsh_completion_dispatches_group_subcommands(
    prefix: str, group: str, command: str
) -> None:
    """Nested groups work with and without a global option before the root command."""
    assert command in _native_completion_output(f"pdd {prefix}{group} ")


def test_zsh_completion_dispatches_checkup_gate_after_global_option() -> None:
    """Nested checkup completion is located relative to its resolved command."""
    assert "--policy" in _native_completion_output("pdd --local checkup gate --po")
