"""Command registration module with deferred handler imports."""
from __future__ import annotations

from collections.abc import Mapping
from importlib import import_module
import sys
from threading import RLock
from types import ModuleType
from typing import Any

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

_UNLOADED_COMMAND = object()


class LazyCommandMapping(dict[str, click.Command]):
    """A normal mutable command dictionary that materializes deferred values."""

    def __init__(
        self,
        targets: dict[str, tuple[str, str]],
        existing: dict[str, click.Command] | None = None,
    ) -> None:
        super().__init__()
        # Keep the marker with the mapping. ``importlib.reload`` re-executes
        # this module in place and replaces module globals, while Click groups
        # can retain an existing mapping created before the reload.
        self._unloaded_command = _UNLOADED_COMMAND
        self._targets = dict(getattr(existing, "_targets", {}))
        self._resolved_keys = set(getattr(existing, "_resolved_keys", ()))
        self._lock = RLock()
        existing_marker = getattr(existing, "_unloaded_command", None)
        if isinstance(existing, dict) and existing_marker is not None:
            # Copy raw slots so re-registering after a module reload remains
            # lazy. Translate the prior instance's marker to this instance's
            # marker without importing any command implementations.
            for key in dict.__iter__(existing):
                value = dict.__getitem__(existing, key)
                if value is existing_marker:
                    value = self._unloaded_command
                dict.__setitem__(self, key, value)
        elif existing:
            self.update(existing)
        self.add_targets(targets)

    def add_targets(self, targets: dict[str, tuple[str, str]]) -> None:
        """Add deferred commands without replacing existing/plugin commands."""
        self._targets.update(targets)
        for key in targets:
            if not dict.__contains__(self, key):
                dict.__setitem__(self, key, self._unloaded_command)

    def __getitem__(self, key: str) -> click.Command:
        value = dict.__getitem__(self, key)
        if value is not self._unloaded_command:
            target = self._targets.get(key)
            if target is not None:
                module_name, attribute = target
                module = sys.modules.get(module_name)
                current = getattr(module, attribute, value) if module else value
                if (
                    key not in self._resolved_keys
                    and module is not None
                    and current is value
                ):
                    with self._lock:
                        if dict.__getitem__(self, key) is value:
                            self._resolved_keys.add(key)
                elif key in self._resolved_keys and current is not value:
                    with self._lock:
                        value = dict.__getitem__(self, key)
                        if key in self._resolved_keys:
                            module = sys.modules.get(module_name)
                            current = (
                                getattr(module, attribute, value) if module else value
                            )
                            if current is not value:
                                dict.__setitem__(self, key, current)
                                value = current
            return value
        with self._lock:
            value = dict.__getitem__(self, key)
            if value is not self._unloaded_command:
                return value
            module_name, attribute = self._targets[key]
            command = getattr(import_module(module_name), attribute)
            dict.__setitem__(self, key, command)
            self._resolved_keys.add(key)
            return command

    def get(self, key: str, default: Any = None) -> Any:
        try:
            return self[key]
        except KeyError:
            return default

    def __iter__(self):
        return dict.__iter__(self)

    def keys(self):
        # The override makes ``dict(mapping)`` use the mapping protocol and
        # therefore our resolving ``__getitem__`` instead of copying raw slots.
        return dict.keys(self)

    def _materialize_all(self) -> None:
        for key in dict.__iter__(self):
            self[key]

    def items(self):
        self._materialize_all()
        return dict.items(self)

    def values(self):
        self._materialize_all()
        return dict.values(self)

    def copy(self) -> dict[str, click.Command]:
        self._materialize_all()
        return dict.copy(self)

    def __repr__(self) -> str:
        self._materialize_all()
        return dict.__repr__(self)

    def __eq__(self, other: object) -> bool:
        self._materialize_all()
        if isinstance(other, LazyCommandMapping):
            other._materialize_all()
        return dict.__eq__(self, other)

    def __or__(self, other: Mapping[Any, Any]) -> dict[Any, Any]:
        self._materialize_all()
        return dict.__or__(self, other)

    def __ror__(self, other: Mapping[Any, Any]) -> dict[Any, Any]:
        self._materialize_all()
        return dict.__or__(dict(other), self)

    def __delitem__(self, key: str) -> None:
        dict.__getitem__(self, key)
        self._targets.pop(key, None)
        self._resolved_keys.discard(key)
        dict.__delitem__(self, key)

    def __setitem__(self, key: str, value: click.Command) -> None:
        dict.__setitem__(self, key, value)
        target = self._targets.get(key)
        if target is not None:
            module_name, attribute = target
            module = sys.modules.get(module_name)
            if (
                module is not None
                and getattr(module, attribute, self._unloaded_command) is value
            ):
                self._resolved_keys.add(key)
                return
        self._resolved_keys.discard(key)

    def clear(self) -> None:
        dict.clear(self)
        # Targets describe which names are canonical, not which slots are
        # currently present. Retain them so a normal clear/update snapshot
        # restore can recover canonical provenance without turning explicit
        # plugin replacements into reload-managed commands.
        self._resolved_keys.clear()

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
            key = next(reversed(self))
        except StopIteration as error:
            raise KeyError("popitem(): dictionary is empty") from error
        return key, self.pop(key)

    def setdefault(self, key: str, default: click.Command | None = None) -> Any:
        if key in self:
            return self[key]
        self[key] = default
        return default

    def update(self, *args: Any, **kwargs: click.Command) -> None:
        if len(args) > 1:
            raise TypeError(f"update expected at most 1 argument, got {len(args)}")
        if args:
            source = args[0]
            if hasattr(source, "keys"):
                for key in source.keys():
                    self[key] = source[key]
            else:
                for key, value in source:
                    self[key] = value
        for key, value in kwargs.items():
            self[key] = value


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
        cli.commands.add_targets(_COMMANDS)
        return
    cli.commands = LazyCommandMapping(_COMMANDS, cli.commands)
