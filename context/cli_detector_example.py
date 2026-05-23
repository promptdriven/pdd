"""Runnable example for `pdd.cli_detector`.

This script demonstrates the public API without requiring user interaction.
All external boundaries (subprocess, shutil.which, input) are mocked.

Demonstrated APIs:
    - CliBootstrapResult: dataclass describing a single CLI bootstrap result.
    - detect_and_bootstrap_cli() -> List[CliBootstrapResult]
    - detect_cli_tools() -> None  (legacy status display)
    - PROVIDER_PRIMARY_KEY, PROVIDER_DISPLAY, CLI_PREFERENCE, SHELL_RC_MAP
"""

from __future__ import annotations

import os
import sys
from unittest import mock

# Make the package importable regardless of working directory.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pdd.cli_detector import (  # noqa: E402
    CliBootstrapResult,
    detect_and_bootstrap_cli,
    detect_cli_tools,
    PROVIDER_PRIMARY_KEY,
    PROVIDER_DISPLAY,
    CLI_PREFERENCE,
    SHELL_RC_MAP,
)


def section(title: str) -> None:
    """Print a small section banner."""
    print()
    print("=" * len(title))
    print(title)
    print("=" * len(title))


def demo_constants() -> None:
    """Show the module-level constants other modules rely on."""
    section("Module-level constants")
    print("CLI_PREFERENCE (table order):", CLI_PREFERENCE)
    print("PROVIDER_DISPLAY:", PROVIDER_DISPLAY)
    print("PROVIDER_PRIMARY_KEY:", PROVIDER_PRIMARY_KEY)
    print("SHELL_RC_MAP:", SHELL_RC_MAP)


def demo_dataclass() -> None:
    """Show the result dataclass with defaults and a populated example."""
    section("CliBootstrapResult dataclass")
    empty = CliBootstrapResult()
    print("Defaults:        ", empty)
    populated = CliBootstrapResult(
        cli_name="claude",
        provider="anthropic",
        cli_path="/usr/local/bin/claude",
        api_key_configured=True,
    )
    print("Populated:       ", populated)
    skipped = CliBootstrapResult(skipped=True)
    print("Skipped sentinel:", skipped)


def demo_bootstrap_default_selection() -> None:
    """Run detect_and_bootstrap_cli() with mocks; user accepts the default."""
    section("detect_and_bootstrap_cli — default selection")

    cli_paths = {"claude": "/usr/local/bin/claude"}

    def fake_find(name):
        return cli_paths.get(name)

    def fake_subprocess_run(cmd, **kwargs):
        proc = mock.MagicMock()
        proc.returncode = 0
        proc.stdout = "claude-cli 1.0.0\n"
        proc.stderr = ""
        return proc

    inputs = iter([""])  # press Enter to accept the default

    env_patch = {"ANTHROPIC_API_KEY": "sk-demo", "SHELL": "/bin/bash"}

    with mock.patch.dict(os.environ, env_patch, clear=False), \
            mock.patch("pdd.cli_detector._find_cli_binary", side_effect=fake_find), \
            mock.patch("pdd.cli_detector._has_provider_oauth", return_value=False), \
            mock.patch("pdd.cli_detector._prompt_input", lambda _p="": next(inputs)), \
            mock.patch("pdd.cli_detector.subprocess.run", side_effect=fake_subprocess_run), \
            mock.patch("pdd.cli_detector._print_step_banner"):
        results = detect_and_bootstrap_cli()

    print("Number of results:", len(results))
    for r in results:
        print("  ->", r)


def demo_bootstrap_quit() -> None:
    """User selects 'q' to skip — returns a single skipped result."""
    section("detect_and_bootstrap_cli — user quits")

    inputs = iter(["q"])

    with mock.patch("pdd.cli_detector._find_cli_binary", return_value=None), \
            mock.patch("pdd.cli_detector._has_provider_oauth", return_value=False), \
            mock.patch("pdd.cli_detector._prompt_input", lambda _p="": next(inputs)), \
            mock.patch("pdd.cli_detector._print_step_banner"):
        results = detect_and_bootstrap_cli()

    print("Number of results:", len(results))
    print("First skipped flag:", results[0].skipped)


def demo_legacy() -> None:
    """Run the legacy detect_cli_tools() helper."""
    section("detect_cli_tools (legacy)")

    cli_paths = {"claude": "/usr/local/bin/claude"}

    def fake_which(name):
        return cli_paths.get(name)

    with mock.patch("pdd.cli_detector._which", side_effect=fake_which):
        detect_cli_tools()


def main() -> int:
    demo_constants()
    demo_dataclass()
    demo_bootstrap_default_selection()
    demo_bootstrap_quit()
    demo_legacy()
    print()
    print("OK — cli_detector example completed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
