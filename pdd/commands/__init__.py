"""Command registration module with deferred handler imports."""
from __future__ import annotations

from collections.abc import ItemsView, KeysView, ValuesView
from importlib import import_module
import sys
from threading import RLock
from types import ModuleType
from typing import Any, Iterator

import click


_COMMANDS = {
    "generate": ("pdd.commands.generate", "generate"),
    "test": ("pdd.commands.generate", "test"),
    "example": ("pdd.commands.generate", "example"),
    "fix": ("pdd.commands.fix", "fix"),
    "split": ("pdd.commands.modify", "split"),
    "change": ("pdd.commands.modify", "change"),
    "update": ("pdd.commands.modify", "update"),
    "sync": ("pdd.commands.maintenance", "sync"),
    "sync-architecture": ("pdd.commands.maintenance", "sync_architecture"),
    "checkup": ("pdd.commands.checkup", "checkup"),
    "contracts": ("pdd.commands.contracts", "contracts_cli"),
    "auto-deps": ("pdd.commands.maintenance", "auto_deps"),
    "setup": ("pdd.commands.maintenance", "setup"),
    "detect": ("pdd.commands.analysis", "detect_change"),
    "conflicts": ("pdd.commands.analysis", "conflicts"),
    "bug": ("pdd.commands.analysis", "bug"),
    "crash": ("pdd.commands.analysis", "crash"),
    "trace": ("pdd.commands.analysis", "trace"),
    "preprocess": ("pdd.commands.misc", "preprocess"),
    "extracts": ("pdd.commands.extracts", "extracts"),
    "report-core": ("pdd.commands.report", "report_core"),
    "replay": ("pdd.commands.replay", "replay"),
    "context": ("pdd.commands.context", "context"),
    "install_completion": ("pdd.commands.utility", "install_completion_cmd"),
    "verify": ("pdd.commands.utility", "verify"),
    "which": ("pdd.commands.which", "which"),
    "reconcile": ("pdd.commands.reconcile", "reconcile"),
    "install-hooks": ("pdd.commands.reconcile", "install_hooks"),
    "certify": ("pdd.commands.sync_core", "certify"),
    "recover": ("pdd.commands.sync_core", "recover"),
    "baseline": ("pdd.commands.sync_core", "baseline"),
    "validate": ("pdd.commands.sync_core", "validate"),
    "templates": ("pdd.commands.templates", "templates_group"),
    "connect": ("pdd.commands.connect", "connect"),
    "auth": ("pdd.commands.auth", "auth_group"),
    "sessions": ("pdd.commands.sessions", "sessions"),
    "firecrawl-cache": ("pdd.commands.firecrawl", "firecrawl_cache_group"),
    "story": ("pdd.commands.story", "story"),
}


_EXPORTS = {
    "generate": ("pdd.commands.generate", "generate"),
    "test": ("pdd.commands.generate", "test"),
    "example": ("pdd.commands.generate", "example"),
    "fix": ("pdd.commands.fix", "fix"),
    "split": ("pdd.commands.modify", "split"),
    "change": ("pdd.commands.modify", "change"),
    "update": ("pdd.commands.modify", "update"),
    "sync": ("pdd.commands.maintenance", "sync"),
    "sync_architecture": ("pdd.commands.maintenance", "sync_architecture"),
    "auto_deps": ("pdd.commands.maintenance", "auto_deps"),
    "setup": ("pdd.commands.maintenance", "setup"),
    "checkup": ("pdd.commands.checkup", "checkup"),
    "contracts_cli": ("pdd.commands.contracts", "contracts_cli"),
    "detect_change": ("pdd.commands.analysis", "detect_change"),
    "conflicts": ("pdd.commands.analysis", "conflicts"),
    "bug": ("pdd.commands.analysis", "bug"),
    "crash": ("pdd.commands.analysis", "crash"),
    "trace": ("pdd.commands.analysis", "trace"),
    "connect": ("pdd.commands.connect", "connect"),
    "auth_group": ("pdd.commands.auth", "auth_group"),
    "preprocess": ("pdd.commands.misc", "preprocess"),
    "extracts": ("pdd.commands.extracts", "extracts"),
    "sessions": ("pdd.commands.sessions", "sessions"),
    "report_core": ("pdd.commands.report", "report_core"),
    "replay": ("pdd.commands.replay", "replay"),
    "context": ("pdd.commands.context", "context"),
    "templates_group": ("pdd.commands.templates", "templates_group"),
    "install_completion_cmd": ("pdd.commands.utility", "install_completion_cmd"),
    "verify": ("pdd.commands.utility", "verify"),
    "which": ("pdd.commands.which", "which"),
    "firecrawl_cache": ("pdd.commands.firecrawl", "firecrawl_cache"),
    "story_cli": ("pdd.commands.story", "story_cli"),
    "install_hooks": ("pdd.commands.reconcile", "install_hooks"),
    "reconcile": ("pdd.commands.reconcile", "reconcile"),
    "baseline": ("pdd.commands.sync_core", "baseline"),
    "certify": ("pdd.commands.sync_core", "certify"),
    "recover": ("pdd.commands.sync_core", "recover"),
    "validate": ("pdd.commands.sync_core", "validate"),
}

__all__ = ["LazyCommandMapping", "register_commands", *sorted(_EXPORTS)]


class LazyCommandMapping(dict[str, click.Command]):
    """A normal mutable command dictionary that materializes deferred values."""

    def __init__(
        self,
        targets: dict[str, tuple[str, str]],
        existing: dict[str, click.Command] | None = None,
    ) -> None:
        super().__init__(existing or {})
        self._targets = dict(targets)
        self._lock = RLock()

    def __iter__(self) -> Iterator[str]:
        return iter(dict.fromkeys((*dict.__iter__(self), *self._targets)))

    def __len__(self) -> int:
        return len(set(dict.__iter__(self)) | set(self._targets))

    def __contains__(self, key: object) -> bool:
        return dict.__contains__(self, key) or key in self._targets

    def __getitem__(self, key: str) -> click.Command:
        try:
            return dict.__getitem__(self, key)
        except KeyError:
            pass
        target = self._targets.get(key)
        if target is None:
            raise KeyError(key)
        with self._lock:
            try:
                return dict.__getitem__(self, key)
            except KeyError:
                module_name, attribute = target
                command = getattr(import_module(module_name), attribute)
                dict.__setitem__(self, key, command)
                return command

    def get(self, key: str, default: Any = None) -> Any:
        try:
            return self[key]
        except KeyError:
            return default

    def keys(self) -> KeysView[str]:
        return KeysView(self)

    def items(self) -> ItemsView[str, click.Command]:
        return ItemsView(self)

    def values(self) -> ValuesView[click.Command]:
        return ValuesView(self)

    def copy(self) -> dict[str, click.Command]:
        return dict(self.items())

    def __delitem__(self, key: str) -> None:
        if key not in self:
            raise KeyError(key)
        self._targets.pop(key, None)
        if dict.__contains__(self, key):
            dict.__delitem__(self, key)

    def clear(self) -> None:
        dict.clear(self)
        self._targets.clear()

    def pop(self, key: str, *default: Any) -> Any:
        if len(default) > 1:
            raise TypeError(f"pop expected at most 2 arguments, got {len(default) + 1}")
        if key not in self:
            if default:
                return default[0]
            raise KeyError(key)
        value = self[key]
        self.__delitem__(key)
        return value

    def popitem(self) -> tuple[str, click.Command]:
        try:
            key = next(reversed(tuple(self)))
        except StopIteration as error:
            raise KeyError("popitem(): dictionary is empty") from error
        return key, self.pop(key)

    def setdefault(self, key: str, default: click.Command | None = None) -> Any:
        if key in self:
            return self[key]
        dict.__setitem__(self, key, default)
        return default


def __getattr__(name: str) -> Any:
    """Resolve historical package-level command exports on demand."""
    target = _EXPORTS.get(name)
    if target is None:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
    module_name, attribute = target
    value = getattr(import_module(module_name), attribute)
    globals()[name] = value
    return value


def __dir__() -> list[str]:
    return sorted(set(globals()) | set(_EXPORTS))


class _CommandsModule(ModuleType):
    """Keep command exports authoritative over same-named submodule attributes."""

    def __getattribute__(self, name: str) -> Any:
        exports = ModuleType.__getattribute__(self, "_EXPORTS")
        target = exports.get(name)
        if target is not None:
            module_name, attribute = target
            value = getattr(import_module(module_name), attribute)
            ModuleType.__setattr__(self, name, value)
            return value
        return ModuleType.__getattribute__(self, name)


sys.modules[__name__].__class__ = _CommandsModule


def register_commands(cli: click.Group) -> None:
    """Register subcommands without importing their implementation modules."""
    if isinstance(cli.commands, LazyCommandMapping):
        cli.commands._targets.update(_COMMANDS)
        return
    cli.commands = LazyCommandMapping(_COMMANDS, cli.commands)
