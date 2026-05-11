"""
Tests for pdd.commands.__init__ — the command registration module.

# ------------------------------------------------------------------ Test Plan
# Spec-derived requirements covered:
#   R1.  Module exports `register_commands` with signature
#        ``(cli: click.Group) -> None``.
#        → test_register_commands_signature_and_return_none
#   R2.  Module begins with ``from __future__ import annotations``.
#        → test_future_annotations_present
#   R3.  Internal imports use single-dot relative form (no ``from pdd.``).
#        → test_uses_relative_internal_imports
#   R4.  `register_commands` registers commands from `.generate`:
#        generate, test, example.
#        → test_generate_commands_registered
#   R5.  Registers `fix` from `.fix`.
#        → test_fix_command_registered
#   R6.  Registers `split`, `change`, `update` from `.modify`.
#        → test_modify_commands_registered
#   R7.  Registers `sync`, `auto_deps`, `setup`, `sync_code`, `metadata`
#        from `.maintenance`.
#        → test_maintenance_commands_registered
#   R8.  Registers `checkup` from `.checkup`.
#        → test_checkup_command_registered
#   R9.  Registers `detect_change`, `conflicts`, `bug`, `crash`, `trace`
#        from `.analysis`.
#        → test_analysis_commands_registered
#   R10. Registers `connect` from `.connect`.
#        → test_connect_command_registered
#   R11. Registers `auth_group` from `.auth`.
#        → test_auth_group_registered
#   R12. Registers `preprocess` from `.misc`.
#        → test_preprocess_command_registered
#   R13. Registers `sessions` from `.sessions`.
#        → test_sessions_command_registered
#   R14. Registers `report_core` from `.report`.
#        → test_report_core_registered
#   R15. Registers `templates_group` from `.templates`.
#        → test_templates_group_registered
#   R16. Registers `install_completion_cmd` (as name="install_completion")
#        and `verify` from `.utility`.
#        → test_install_completion_uses_explicit_name
#        → test_verify_command_registered
#   R17. Registers `which` from `.which`.
#        → test_which_command_registered
#   R18. Registers `firecrawl_cache` from `.firecrawl`.
#        → test_firecrawl_cache_registered
#   R19. Calling `register_commands` mutates the supplied group in place
#        and returns ``None``.
#        → test_register_commands_returns_none_and_mutates_in_place
#   R20. Each registered object is a ``click.BaseCommand`` instance.
#        → test_all_registered_objects_are_click_commands
#   R21. Click group is registered as a Group (not a plain command) —
#        regression guard for templates_group, auth_group, metadata.
#        → test_groups_are_click_groups
#   R22. `register_commands` is idempotent when called on a fresh group
#        and produces the same key set.
#        → test_registration_is_deterministic
#   R23. Required symbols are importable from `pdd.commands.__init__`
#        at module load.
#        → test_required_symbols_importable
"""

from __future__ import annotations

import inspect
import os
import sys
from typing import get_type_hints

# Ensure the local source tree shadows any installed copy of pdd.
_PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if _PROJECT_ROOT not in sys.path:
    sys.path.insert(0, _PROJECT_ROOT)
for _name in list(sys.modules):
    if _name == "pdd" or _name.startswith("pdd."):
        del sys.modules[_name]

import click  # noqa: E402
import pytest  # noqa: E402

from pdd.commands import register_commands  # noqa: E402
from pdd import commands as commands_pkg  # noqa: E402


# --------------------------------------------------------------------------- #
# Helpers
# --------------------------------------------------------------------------- #

def _fresh_group() -> click.Group:
    @click.group()
    def cli() -> None:
        """test cli"""

    return cli


def _registered(cli: click.Group) -> dict[str, click.BaseCommand]:
    return dict(cli.commands)


# --------------------------------------------------------------------------- #
# R1, R2, R3, R19, R20, R22, R23 — structural / behavioural checks
# --------------------------------------------------------------------------- #

def test_register_commands_signature_and_return_none() -> None:
    sig = inspect.signature(register_commands)
    params = list(sig.parameters.values())
    assert len(params) == 1, "register_commands must take exactly one argument"
    assert params[0].name == "cli"
    hints = get_type_hints(register_commands)
    assert hints.get("cli") is click.Group
    assert hints.get("return") is type(None)  # noqa: E721


def test_future_annotations_present() -> None:
    src_path = os.path.join(
        _PROJECT_ROOT, "pdd", "commands", "__init__.py"
    )
    with open(src_path, "r", encoding="utf-8") as fh:
        source = fh.read()
    assert "from __future__ import annotations" in source.splitlines()[0:5], (
        "Spec requires `from __future__ import annotations` near the top."
    )


def test_uses_relative_internal_imports() -> None:
    src_path = os.path.join(
        _PROJECT_ROOT, "pdd", "commands", "__init__.py"
    )
    with open(src_path, "r", encoding="utf-8") as fh:
        source = fh.read()
    # internal sibling imports MUST be relative, not absolute pdd.commands.xxx
    assert "from pdd.commands." not in source
    assert "from .generate import" in source
    assert "from .maintenance import" in source


def test_register_commands_returns_none_and_mutates_in_place() -> None:
    cli = _fresh_group()
    assert len(cli.commands) == 0
    result = register_commands(cli)
    assert result is None
    assert len(cli.commands) > 0


def test_all_registered_objects_are_click_commands() -> None:
    cli = _fresh_group()
    register_commands(cli)
    for name, cmd in cli.commands.items():
        assert isinstance(cmd, click.BaseCommand), (
            f"{name!r} should be a click.BaseCommand, got {type(cmd)!r}"
        )


def test_registration_is_deterministic() -> None:
    cli_a = _fresh_group()
    cli_b = _fresh_group()
    register_commands(cli_a)
    register_commands(cli_b)
    assert set(cli_a.commands.keys()) == set(cli_b.commands.keys())


def test_required_symbols_importable() -> None:
    # register_commands must be the only required public API.
    assert callable(getattr(commands_pkg, "register_commands"))


# --------------------------------------------------------------------------- #
# R4 — .generate: generate, test, example
# --------------------------------------------------------------------------- #

def test_generate_commands_registered() -> None:
    cli = _fresh_group()
    register_commands(cli)
    cmds = _registered(cli)
    from pdd.commands.generate import generate, test, example
    assert cmds.get(generate.name) is generate
    assert cmds.get(test.name) is test
    assert cmds.get(example.name) is example


# --------------------------------------------------------------------------- #
# R5 — .fix: fix
# --------------------------------------------------------------------------- #

def test_fix_command_registered() -> None:
    cli = _fresh_group()
    register_commands(cli)
    from pdd.commands.fix import fix
    assert cli.commands.get(fix.name) is fix


# --------------------------------------------------------------------------- #
# R6 — .modify: split, change, update
# --------------------------------------------------------------------------- #

def test_modify_commands_registered() -> None:
    cli = _fresh_group()
    register_commands(cli)
    from pdd.commands.modify import split, change, update
    assert cli.commands.get(split.name) is split
    assert cli.commands.get(change.name) is change
    assert cli.commands.get(update.name) is update


# --------------------------------------------------------------------------- #
# R7 — .maintenance: sync, auto_deps, setup, sync_code, metadata
# --------------------------------------------------------------------------- #

def test_maintenance_commands_registered() -> None:
    cli = _fresh_group()
    register_commands(cli)
    from pdd.commands.maintenance import (
        sync,
        auto_deps,
        setup,
        sync_code,
        metadata,
    )
    assert cli.commands.get(sync.name) is sync
    assert cli.commands.get(auto_deps.name) is auto_deps
    assert cli.commands.get(setup.name) is setup
    # sync_code may share a click-name with another command (alias);
    # ensure the underlying object was added to the cli at some name.
    assert sync_code in cli.commands.values()
    assert cli.commands.get(metadata.name) is metadata


# --------------------------------------------------------------------------- #
# R8 — .checkup: checkup
# --------------------------------------------------------------------------- #

def test_checkup_command_registered() -> None:
    cli = _fresh_group()
    register_commands(cli)
    from pdd.commands.checkup import checkup
    assert cli.commands.get(checkup.name) is checkup


# --------------------------------------------------------------------------- #
# R9 — .analysis: detect_change, conflicts, bug, crash, trace
# --------------------------------------------------------------------------- #

def test_analysis_commands_registered() -> None:
    cli = _fresh_group()
    register_commands(cli)
    from pdd.commands.analysis import detect_change, conflicts, bug, crash, trace
    assert cli.commands.get(detect_change.name) is detect_change
    assert cli.commands.get(conflicts.name) is conflicts
    assert cli.commands.get(bug.name) is bug
    assert cli.commands.get(crash.name) is crash
    assert cli.commands.get(trace.name) is trace


# --------------------------------------------------------------------------- #
# R10 — .connect: connect
# --------------------------------------------------------------------------- #

def test_connect_command_registered() -> None:
    cli = _fresh_group()
    register_commands(cli)
    from pdd.commands.connect import connect
    assert cli.commands.get(connect.name) is connect


# --------------------------------------------------------------------------- #
# R11 — .auth: auth_group
# --------------------------------------------------------------------------- #

def test_auth_group_registered() -> None:
    cli = _fresh_group()
    register_commands(cli)
    from pdd.commands.auth import auth_group
    assert cli.commands.get(auth_group.name) is auth_group


# --------------------------------------------------------------------------- #
# R12 — .misc: preprocess
# --------------------------------------------------------------------------- #

def test_preprocess_command_registered() -> None:
    cli = _fresh_group()
    register_commands(cli)
    from pdd.commands.misc import preprocess
    assert cli.commands.get(preprocess.name) is preprocess


# --------------------------------------------------------------------------- #
# R13 — .sessions: sessions
# --------------------------------------------------------------------------- #

def test_sessions_command_registered() -> None:
    cli = _fresh_group()
    register_commands(cli)
    from pdd.commands.sessions import sessions
    assert cli.commands.get(sessions.name) is sessions


# --------------------------------------------------------------------------- #
# R14 — .report: report_core
# --------------------------------------------------------------------------- #

def test_report_core_registered() -> None:
    cli = _fresh_group()
    register_commands(cli)
    from pdd.commands.report import report_core
    assert cli.commands.get(report_core.name) is report_core


# --------------------------------------------------------------------------- #
# R15 — .templates: templates_group
# --------------------------------------------------------------------------- #

def test_templates_group_registered() -> None:
    cli = _fresh_group()
    register_commands(cli)
    from pdd.commands.templates import templates_group
    assert cli.commands.get(templates_group.name) is templates_group


# --------------------------------------------------------------------------- #
# R16 — .utility: install_completion_cmd (renamed) and verify
# --------------------------------------------------------------------------- #

def test_install_completion_uses_explicit_name() -> None:
    cli = _fresh_group()
    register_commands(cli)
    from pdd.commands.utility import install_completion_cmd
    # spec requires registration with the exact name "install_completion"
    assert "install_completion" in cli.commands
    assert cli.commands["install_completion"] is install_completion_cmd


def test_verify_command_registered() -> None:
    cli = _fresh_group()
    register_commands(cli)
    from pdd.commands.utility import verify
    assert cli.commands.get(verify.name) is verify


# --------------------------------------------------------------------------- #
# R17 — .which: which
# --------------------------------------------------------------------------- #

def test_which_command_registered() -> None:
    cli = _fresh_group()
    register_commands(cli)
    from pdd.commands.which import which
    assert cli.commands.get(which.name) is which


# --------------------------------------------------------------------------- #
# R18 — .firecrawl: firecrawl_cache
# --------------------------------------------------------------------------- #

def test_firecrawl_cache_registered() -> None:
    cli = _fresh_group()
    register_commands(cli)
    from pdd.commands.firecrawl import firecrawl_cache
    assert cli.commands.get(firecrawl_cache.name) is firecrawl_cache


# --------------------------------------------------------------------------- #
# R21 — Groups must remain click.Group instances
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize(
    "import_path,name",
    [
        ("pdd.commands.templates", "templates_group"),
        ("pdd.commands.auth", "auth_group"),
        ("pdd.commands.maintenance", "metadata"),
    ],
)
def test_groups_are_click_groups(import_path: str, name: str) -> None:
    import importlib

    mod = importlib.import_module(import_path)
    obj = getattr(mod, name)
    assert isinstance(obj, click.Group), (
        f"{import_path}.{name} should be a click.Group for nested-command support"
    )
