"""Protected language and artifact-format identity registry."""

from __future__ import annotations

import csv
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Optional


class LanguageRegistryError(ValueError):
    """Raised when language identity is unknown, ambiguous, or inconsistent."""


_LEGACY_ALIASES = {
    "c-plus-plus": ("cpp",),
    "c-sharp": ("csharp",),
    "f-sharp": ("fsharp",),
    "javascriptreact": ("jsx",),
    "objective-c": ("objectivec",),
    "restructuredtext": ("rst",),
    "typescriptreact": ("tsx",),
    "yaml": ("yml",),
}


def _language_id(name: str) -> str:
    expanded = name.casefold().replace("++", " plus plus ").replace("#", " sharp ")
    identifier = re.sub(r"[^a-z0-9]+", "-", expanded).strip("-")
    if not identifier:
        raise LanguageRegistryError(f"language has no stable identifier: {name!r}")
    return identifier


@dataclass(frozen=True, order=True)
class LanguageSpec:
    """Stable language identity and its explicitly supported output formats."""

    language_id: str
    display_name: str
    aliases: tuple[str, ...]
    extensions: tuple[str, ...]
    output_roles: tuple[str, ...]


@dataclass(frozen=True)
class _LanguageRow:
    display_name: str
    extension: str
    output_roles: tuple[str, ...]


def _read_rows(path: Path) -> tuple[_LanguageRow, ...]:
    rows: list[_LanguageRow] = []
    try:
        with path.open(newline="", encoding="utf-8") as handle:
            for raw in csv.DictReader(handle):
                name = (raw.get("language") or "").strip()
                if not name:
                    raise LanguageRegistryError("language registry contains an empty name")
                extension = (raw.get("extension") or "").strip().casefold()
                if extension and not extension.startswith("."):
                    extension = "." + extension
                roles = tuple(
                    sorted(
                        role.strip().casefold()
                        for role in (raw.get("outputs") or "").split("|")
                        if role.strip()
                    )
                )
                rows.append(_LanguageRow(name, extension, roles))
    except (OSError, csv.Error) as exc:
        raise LanguageRegistryError(f"cannot read language registry: {path}") from exc
    return tuple(rows)


class LanguageRegistry:
    """Deterministic alias and extension resolution with ambiguity rejection."""

    def __init__(self, specs: Iterable[LanguageSpec]) -> None:
        ordered = tuple(sorted(specs))
        if not ordered:
            raise LanguageRegistryError("language registry must not be empty")
        self.specs = ordered
        self._by_id = {spec.language_id: spec for spec in ordered}
        if len(self._by_id) != len(ordered):
            raise LanguageRegistryError("duplicate stable language ID")
        self._by_alias: dict[str, LanguageSpec] = {}
        self._by_extension: dict[str, list[LanguageSpec]] = {}
        for spec in ordered:
            for alias in spec.aliases:
                normalized = alias.casefold()
                previous = self._by_alias.get(normalized)
                if previous is not None and previous != spec:
                    raise LanguageRegistryError(f"ambiguous language alias: {alias}")
                self._by_alias[normalized] = spec
            for extension in spec.extensions:
                self._by_extension.setdefault(extension, []).append(spec)

    @classmethod
    def from_csv(cls, path: Path) -> "LanguageRegistry":
        """Load and merge all rows without selecting a first-row winner."""
        grouped: dict[str, list[_LanguageRow]] = {}
        for row in _read_rows(path):
            grouped.setdefault(_language_id(row.display_name), []).append(row)
        specs: list[LanguageSpec] = []
        for language_id, rows in grouped.items():
            displays = {row.display_name for row in rows}
            aliases = tuple(
                sorted(
                    {name.casefold() for name in displays}
                    | {language_id}
                    | set(_LEGACY_ALIASES.get(language_id, ()))
                )
            )
            extensions = tuple(sorted({row.extension for row in rows}))
            roles = tuple(sorted({role for row in rows for role in row.output_roles}))
            specs.append(
                LanguageSpec(
                    language_id,
                    sorted(displays, key=str.casefold)[0],
                    aliases,
                    extensions,
                    roles,
                )
            )
        return cls(specs)

    @classmethod
    def bundled(cls) -> "LanguageRegistry":
        """Load the package-bundled registry in source and wheel installations."""
        module = Path(__file__)
        data = (
            module.parent / "data"
            if __package__ == "pdd_sync_checker"
            else module.parents[1] / "data"
        )
        return cls.from_csv(data / "language_format.csv")

    def resolve_alias(self, alias: str) -> LanguageSpec:
        """Resolve one explicit language alias to its stable identity."""
        spec = self._by_alias.get(alias.casefold())
        if spec is None:
            raise LanguageRegistryError(f"unknown language alias: {alias}")
        return spec

    def resolve_extension(
        self,
        extension: str,
        *,
        explicit_language: Optional[str] = None,
    ) -> LanguageSpec:
        """Resolve an extension only when it names exactly one language."""
        normalized = extension.casefold()
        if normalized and not normalized.startswith("."):
            normalized = "." + normalized
        if explicit_language is not None:
            spec = self.resolve_alias(explicit_language)
            if normalized not in spec.extensions:
                raise LanguageRegistryError(
                    f"extension {normalized!r} is not valid for {spec.language_id}"
                )
            return spec
        matches = self._by_extension.get(normalized, [])
        if len(matches) != 1:
            names = ", ".join(spec.language_id for spec in matches) or "none"
            raise LanguageRegistryError(
                f"extension {normalized!r} is ambiguous or unknown: {names}"
            )
        return matches[0]

    def digest(self) -> str:
        """Return the protected deterministic registry digest."""
        payload = [
            {
                "language_id": spec.language_id,
                "display_name": spec.display_name,
                "aliases": spec.aliases,
                "extensions": spec.extensions,
                "output_roles": spec.output_roles,
            }
            for spec in self.specs
        ]
        encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
        return hashlib.sha256(encoded).hexdigest()
