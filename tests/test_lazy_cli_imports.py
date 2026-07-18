"""Regression tests for lightweight package and CLI command discovery."""
from __future__ import annotations

import json
import os
import subprocess
import sys

import click


EXPECTED_COMMANDS = {
    "auth", "auto-deps", "baseline", "bug", "certify", "change", "checkup",
    "conflicts", "connect", "context", "contracts", "crash", "detect",
    "example", "extracts", "firecrawl-cache", "fix", "generate",
    "install-hooks", "install_completion", "preprocess", "reconcile", "recover",
    "replay", "report-core", "sessions", "setup", "split", "story", "sync",
    "sync-architecture", "templates", "test", "trace", "update", "validate",
    "verify", "which",
}


def test_package_and_cli_discovery_do_not_import_llm_stack() -> None:
    """Simple command discovery must not initialize optional LLM dependencies."""
    script = """
import json
import sys
import pdd
package_light = 'pdd.llm_invoke' not in sys.modules
from pdd.cli import cli
cli_light = 'pdd.llm_invoke' not in sys.modules and 'pdd.sync_main' not in sys.modules
print(json.dumps({'package_light': package_light, 'cli_light': cli_light}))
"""
    env = os.environ.copy()
    env["PDD_AUTO_UPDATE"] = "false"
    result = subprocess.run(
        [sys.executable, "-c", script],
        check=True,
        capture_output=True,
        text=True,
        env=env,
    )

    assert json.loads(result.stdout) == {"package_light": True, "cli_light": True}


def test_lazy_command_registry_preserves_public_command_names() -> None:
    """Deferred registration exposes exactly the historical Click names."""
    from pdd.cli import cli
    from pdd.commands import _COMMANDS

    assert set(_COMMANDS) == EXPECTED_COMMANDS
    assert set(cli.list_commands(click.Context(cli))) == EXPECTED_COMMANDS


def test_package_lazy_export_resolves_and_caches_legacy_symbol() -> None:
    """Package-level imports retain object identity after deferred resolution."""
    import pdd
    from pdd.get_lint_commands import get_lint_commands as implementation

    pdd.__dict__.pop("get_lint_commands", None)
    resolved = pdd.get_lint_commands

    assert resolved is implementation
    assert pdd.__dict__["get_lint_commands"] is implementation


def test_star_imports_preserve_lazy_legacy_exports() -> None:
    """Lazy exports remain visible to callers using the historical star API."""
    package_namespace: dict[str, object] = {}
    cli_namespace: dict[str, object] = {}

    exec("from pdd import *", package_namespace)
    exec("from pdd.cli import *", cli_namespace)

    assert "run_agentic_task" in package_namespace
    assert "get_lint_commands" in package_namespace
    assert "sync_main" in cli_namespace
    assert "process_commands" in cli_namespace
