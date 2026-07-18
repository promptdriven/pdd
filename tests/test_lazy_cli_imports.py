"""Regression tests for lightweight package and CLI command discovery."""
from __future__ import annotations

import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from types import SimpleNamespace

import click
import pytest


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
    assert len(cli.commands) == len(EXPECTED_COMMANDS)
    assert "sync" in cli.commands

    sync_from_item = cli.commands["sync"]

    assert cli.commands.get("sync") is sync_from_item
    assert cli.get_command(click.Context(cli), "sync") is sync_from_item


def test_commands_package_preserves_historical_exports_and_identity() -> None:
    """Former eager package exports resolve to the Click registry objects."""
    from pdd import commands
    from pdd.cli import cli
    from pdd.commands import contracts_cli, generate, sync_architecture

    assert isinstance(generate, click.Command)
    assert isinstance(sync_architecture, click.Command)
    assert isinstance(contracts_cli, click.Command)
    assert generate is cli.commands["generate"]
    assert sync_architecture is cli.commands["sync-architecture"]
    assert contracts_cli is cli.commands["contracts"]
    assert set(commands.__all__) >= {
        "generate", "sync_architecture", "contracts_cli", "story_cli",
        "firecrawl_cache",
    }

    registered = list(cli.commands.values())
    for export_name in commands._EXPORTS:
        exported = getattr(commands, export_name)
        assert isinstance(exported, click.Command), export_name
        assert any(exported is command for command in registered), export_name


def test_register_commands_supports_plain_click_group_dispatch() -> None:
    """Registration remains usable outside the custom PDDCLI subclass."""
    from click.testing import CliRunner
    from pdd.commands import register_commands

    group = click.Group("standalone")
    register_commands(group)

    assert len(group.commands) == len(EXPECTED_COMMANDS)
    assert set(group.list_commands(click.Context(group))) == EXPECTED_COMMANDS
    assert CliRunner().invoke(group, ["reconcile", "--help"]).exit_code == 0


def test_lazy_command_resolution_is_thread_safe() -> None:
    """Concurrent first access caches one shared Click command instance."""
    from pdd.commands import LazyCommandMapping, _COMMANDS

    mapping = LazyCommandMapping(_COMMANDS)
    with ThreadPoolExecutor(max_workers=8) as executor:
        commands = list(executor.map(lambda _: mapping["sync"], range(32)))

    assert len({id(command) for command in commands}) == 1


def test_lazy_mapping_has_stable_native_dict_shape_and_value_views() -> None:
    """Raw storage has all keys while value-facing APIs expose real commands."""
    from pdd.commands import LazyCommandMapping, _COMMANDS, _UNLOADED_COMMAND

    mapping = LazyCommandMapping(_COMMANDS)
    expected_order = list(_COMMANDS)

    assert "__len__" not in LazyCommandMapping.__dict__
    assert dict.__len__(mapping) == len(_COMMANDS)
    assert list(mapping) == expected_order
    assert sum(value is _UNLOADED_COMMAND for value in dict.values(mapping)) == 38
    assert "generate" in repr(mapping)
    assert mapping != {}

    copied = dict(LazyCommandMapping(_COMMANDS))
    union = LazyCommandMapping(_COMMANDS) | {}
    reverse_union = {"plugin": click.Command("plugin")} | LazyCommandMapping(_COMMANDS)
    items = dict(mapping.items())

    assert list(mapping) == expected_order
    assert all(isinstance(value, click.Command) for value in copied.values())
    assert all(isinstance(value, click.Command) for value in union.values())
    assert all(isinstance(value, click.Command) for value in reverse_union.values())
    assert LazyCommandMapping(_COMMANDS) == copied
    assert all(items[key] is mapping[key] for key in expected_order)
    assert all(value is mapping[key] for key, value in mapping.items())


def test_lazy_mapping_json_never_silently_looks_empty() -> None:
    """Raw unloaded values fail serialization like historical Click commands."""
    from pdd.commands import LazyCommandMapping, _COMMANDS

    with pytest.raises(TypeError):
        json.dumps(LazyCommandMapping(_COMMANDS))


def test_lazy_mapping_failed_import_remains_retryable(monkeypatch) -> None:
    """A failed first load leaves the stable slot unloaded for a later retry."""
    from pdd import commands
    from pdd.commands import LazyCommandMapping, _UNLOADED_COMMAND

    expected = click.Command("retried")
    attempts = 0

    def flaky_import(_module_name: str):
        nonlocal attempts
        attempts += 1
        if attempts == 1:
            raise ImportError("transient")
        return SimpleNamespace(command=expected)

    monkeypatch.setattr(commands, "import_module", flaky_import)
    mapping = LazyCommandMapping({"retry": ("fake.module", "command")})

    with pytest.raises(ImportError, match="transient"):
        mapping["retry"]
    assert dict.__getitem__(mapping, "retry") is _UNLOADED_COMMAND
    assert mapping["retry"] is expected


def test_lazy_mapping_order_and_mutations_match_dict_behavior() -> None:
    """Reads keep order and ordinary mutations update lazy bookkeeping."""
    from pdd.commands import LazyCommandMapping, _COMMANDS, register_commands

    plugin = click.Command("plugin")
    existing_sync = click.Command("custom-sync")
    mapping = LazyCommandMapping(_COMMANDS, {"plugin": plugin, "sync": existing_sync})
    initial_order = ["plugin", "sync", *[key for key in _COMMANDS if key != "sync"]]

    assert list(mapping) == initial_order
    assert mapping["sync"] is existing_sync
    assert mapping["generate"] is mapping.get("generate")
    assert list(mapping) == initial_order

    last_key = initial_order[-1]
    popped_key, popped_value = mapping.popitem()
    assert popped_key == last_key
    assert isinstance(popped_value, click.Command)
    assert last_key not in mapping

    replacement = click.Command("replacement")
    mapping.update({"generate": replacement})
    assert mapping["generate"] is replacement
    assert mapping.setdefault("generate", click.Command("ignored")) is replacement
    mapping["extra"] = plugin
    assert mapping.pop("extra") is plugin
    del mapping["test"]
    assert "test" not in mapping
    mapping.clear()
    assert len(mapping) == 0
    group = click.Group("reloaded")
    group.commands = mapping
    register_commands(group)
    assert list(group.commands) == list(_COMMANDS)
    assert len(group.commands) == 38


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
