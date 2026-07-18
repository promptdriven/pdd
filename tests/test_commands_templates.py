# tests/test_commands_templates.py
"""Tests for commands/templates."""
import os
import sys
import subprocess
import json
from concurrent.futures import ThreadPoolExecutor
from types import SimpleNamespace
from unittest.mock import patch

import pytest
from click.testing import CliRunner
import click

from pdd import cli

RUN_ALL_TESTS_ENABLED = os.getenv("PDD_RUN_ALL_TESTS") == "1"


@patch('pdd.template_registry.list_templates')
def test_cli_templates_list_default(mock_list_templates, runner):
    """`pdd templates list` should pretty-print template metadata."""
    mock_list_templates.return_value = [
        {
            "name": "architecture/architecture_json",
            "description": "Architecture outline",
            "version": "1.0.0",
            "tags": ["architecture", "json"],
        }
    ]

    result = runner.invoke(cli.templates_group, ["list"])

    assert result.exception is None, f"Unexpected exception: {result.exception}"
    assert result.exit_code == 0
    mock_list_templates.assert_called_once_with(None)
    assert "Available Templates" in result.output, f"output was: {result.output!r}"
    assert "architecture/architecture_json" in result.output
    assert "Architecture outline" in result.output

@patch('pdd.template_registry.list_templates')
def test_cli_templates_list_json_filter(mock_list_templates, runner):
    """`pdd templates list --json --filter` should return JSON and pass the filter tag."""
    payload = [
        {
            "name": "frontend/nextjs",
            "description": "Next.js app",
            "version": "2.0.0",
            "tags": ["frontend"],
        }
    ]
    mock_list_templates.return_value = payload

    result = runner.invoke(cli.templates_group, ["list", "--json", "--filter", "tag=frontend"])

    assert result.exit_code == 0
    mock_list_templates.assert_called_once_with("tag=frontend")

    import json as _json

    parsed = _json.loads(result.output)
    assert parsed == payload

@patch('pdd.template_registry.show_template')
def test_cli_templates_show_outputs_sections(mock_show_template, runner):
    """`pdd templates show` should render template metadata sections."""
    mock_show_template.return_value = {
        "summary": {
            "name": "architecture/architecture_json",
            "description": "Architecture outline",
            "version": "1.0.0",
            "tags": ["architecture"],
            "language": "json",
            "output": "architecture.json",
            "path": "/tmp/arch.prompt",
        },
        "variables": {"PRD_FILE": {"required": True, "type": "path"}},
        "usage": {"generate": [{"command": "pdd generate ..."}]},
        "discover": {"enabled": True},
        "output_schema": {"type": "object"},
        "notes": "Provide a PRD file.",
    }

    result = runner.invoke(cli.templates_group, ["show", "architecture/architecture_json"])

    assert result.exception is None, f"Unexpected exception: {result.exception}"
    assert result.exit_code == 0
    mock_show_template.assert_called_once_with("architecture/architecture_json")
    assert "Template Summary:" in result.output, f"output was: {result.output!r}"
    assert "Architecture outline" in result.output
    assert "Version" in result.output
    assert "Variables:" in result.output
    assert "Output Schema" in result.output
    assert "Provide a PRD file." in result.output

@patch('pdd.template_registry.copy_template')
def test_cli_templates_copy_invokes_registry(mock_copy_template, runner, tmp_path):
    """`pdd templates copy` should copy via the registry and report the destination."""
    destination = tmp_path / "prompts" / "architecture" / "architecture_json.prompt"
    mock_copy_template.return_value = str(destination)

    result = runner.invoke(
        cli.templates_group,
        [
            "copy",
            "architecture/architecture_json",
            "--to",
            str(destination.parent),
        ],
    )

    assert result.exception is None, f"Unexpected exception: {result.exception}"
    assert result.exit_code == 0
    mock_copy_template.assert_called_once_with("architecture/architecture_json", str(destination.parent))
    assert "Copied to" in result.output, f"output was: {result.output!r}"
    assert "architecture_json.prompt" in result.output.replace("\n", "")

def test_cli_templates_group_registered():
    """Ensure the templates command group is reachable from the top-level CLI."""
    assert "templates" in cli.cli.commands
    assert cli.cli.commands["templates"] is cli.templates_group


def test_cli_templates_export_tracks_real_module_reload() -> None:
    """A restored registry must not retain a pre-reload Click group."""
    import importlib

    # ``tests/core/test_cli.py`` snapshots the real commands, then restores
    # them with this ordinary dict clear/update sequence after every test.
    # Preserve the canonical-target provenance across that broader-suite
    # state instead of making reload correctness depend on test order.
    registry = cli.cli.commands
    snapshot = registry.copy()
    registry.clear()
    registry.update(snapshot)

    cli.__dict__.pop("templates_group", None)
    templates_module = importlib.import_module("pdd.commands.templates")
    before_export = cli.templates_group
    before_registry = cli.cli.commands["templates"]
    assert before_export is before_registry

    reloaded = importlib.reload(templates_module)
    after_registry = cli.cli.commands["templates"]
    after_export = cli.templates_group

    assert after_export is reloaded.templates_group
    assert after_export is after_registry
    assert after_export is not before_export


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


def test_lazy_mapping_preserves_override_loaded_before_target(monkeypatch) -> None:
    """An explicit plugin is not reclassified before its target is imported."""
    from pdd.commands import LazyCommandMapping

    module_name = "fake.late_command"
    plugin = click.Command("plugin")
    canonical = click.Command("canonical")
    monkeypatch.delitem(sys.modules, module_name, raising=False)
    mapping = LazyCommandMapping(
        {"replaceable": (module_name, "command")},
        {"replaceable": plugin},
    )

    assert mapping["replaceable"] is plugin
    monkeypatch.setitem(sys.modules, module_name, SimpleNamespace(command=canonical))
    assert mapping["replaceable"] is plugin


def test_lazy_mapping_survives_module_sentinel_refresh(monkeypatch) -> None:
    """Re-registration and reloaded exports retain one lazy identity."""
    import importlib

    commands_module = importlib.import_module("pdd.commands")
    expected = click.Command("reload-safe")
    replacement = click.Command("replacement")
    imports: list[str] = []
    resolved = SimpleNamespace(command=expected)
    targets = {"reload-safe": ("fake.module", "command")}
    monkeypatch.setitem(sys.modules, "fake.module", resolved)
    monkeypatch.setitem(
        commands_module._EXPORTS,
        "reload_safe",
        ("fake.module", "command"),
    )
    mapping = commands_module.LazyCommandMapping(targets)

    monkeypatch.setattr(commands_module, "_UNLOADED_COMMAND", object())

    def resolve(module_name: str):
        imports.append(module_name)
        return resolved

    monkeypatch.setattr(
        commands_module,
        "import_module",
        resolve,
    )
    replacement = commands_module.LazyCommandMapping(targets, mapping)
    group = click.Group("root", commands=replacement)

    assert imports == []
    assert group.get_command(click.Context(group), "reload-safe") is expected
    assert imports == ["fake.module"]
    mapping._resolved_keys.clear()
    assert group.get_command(click.Context(group), "reload-safe") is expected
    resolved.command = replacement
    assert commands_module.reload_safe is replacement
    assert group.get_command(click.Context(group), "reload-safe") is replacement


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

# --- Global Options Tests ---
