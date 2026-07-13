"""Deterministic base/head candidate inventory and unit manifest."""

from __future__ import annotations

import hashlib
import fnmatch
import json
import posixpath
import subprocess
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Optional

import yaml

from .decommission import (
    DecommissionTombstone,
    control_transition_invalid,
    enforce_head_fixed_point,
    load_expected_registry,
    load_tombstones,
)
from .identity import REPOSITORY_ID_RELPATH, canonical_repository_id
from .git_io import read_git_blob
from .language import LanguageRegistry, LanguageRegistryError
from .types import CandidateId, InventoryStatus, UnitId


class ManifestError(ValueError):
    """Raised when Git inventory or protected manifest inputs are invalid."""


@dataclass(frozen=True, order=True)
class GitTreeEntry:
    """Mode and object identity for one tracked path in a Git tree."""

    relpath: PurePosixPath
    git_mode: str
    object_id: str


@dataclass(frozen=True, order=True)
# pylint: disable=too-many-instance-attributes
class CandidateRecord:
    """Complete base/head accounting for one tracked candidate path."""

    candidate_id: CandidateId
    inventory: InventoryStatus
    in_base: bool
    in_head: bool
    ownership_provenance: str
    base_object_id: str | None = None
    base_git_mode: str | None = None
    head_object_id: str | None = None
    head_git_mode: str | None = None
    unit_id: UnitId | None = None


@dataclass(frozen=True, order=True)
class ManifestUnit:
    """Prompt-backed unit identity and its exact architecture-owned outputs."""

    unit_id: UnitId
    present_in_base: bool
    present_in_head: bool
    artifact_paths: tuple[PurePosixPath, ...]
    tombstoned: bool


@dataclass(frozen=True)
class ManifestRefs:
    """Protected base and checked-head Git references."""

    base: str
    head: str


@dataclass(frozen=True, order=True)
class OwnershipRule:
    """Protected-base classification for an otherwise unmatched tracked path."""

    pattern: str
    inventory: InventoryStatus
    role: str
    owner: str
    preauthorize_absent: bool = False


@dataclass(frozen=True)
class _TreeManifest:
    """Parsed candidate inputs for one immutable Git tree."""

    ref: str
    entries: dict[PurePosixPath, GitTreeEntry]
    units: dict[PurePosixPath, UnitId]
    outputs: dict[PurePosixPath, UnitId]
    invalid_reasons: tuple[str, ...]


@dataclass(frozen=True)
class _UnitSources:
    """Base/head identity and output maps used during unit assembly."""

    base_units: dict[PurePosixPath, UnitId]
    head_units: dict[PurePosixPath, UnitId]
    base_outputs: dict[PurePosixPath, UnitId]
    head_outputs: dict[PurePosixPath, UnitId]


@dataclass(frozen=True)
class _CandidateSources:
    """Inputs used to classify the independent tracked-path partition."""

    repository_id: str
    base_entries: dict[PurePosixPath, GitTreeEntry]
    head_entries: dict[PurePosixPath, GitTreeEntry]
    prompt_owner: dict[PurePosixPath, UnitId]
    output_owner: dict[PurePosixPath, UnitId]
    ownership_rules: tuple[OwnershipRule, ...]


@dataclass(frozen=True)
class UnitManifest:
    """Deterministic partition of the protected base/head candidate universe."""

    repository_id: str
    language_registry_digest: str
    refs: ManifestRefs
    candidates: tuple[CandidateRecord, ...]
    units: tuple[ManifestUnit, ...]
    expected_managed: tuple[UnitId, ...]
    invalid_reasons: tuple[str, ...]
    unaccounted_tracked_paths: tuple[PurePosixPath, ...]

    @property
    def base_ref(self) -> str:
        """Return the protected base reference."""
        return self.refs.base

    @property
    def head_ref(self) -> str:
        """Return the checked head reference."""
        return self.refs.head

    @property
    def managed_units(self) -> tuple[ManifestUnit, ...]:
        """Return prompt-backed units currently present in the head tree."""
        return tuple(unit for unit in self.units if unit.present_in_head)

    def digest(self) -> str:
        """Return a deterministic digest of identity, ownership, and paths."""
        structural_candidates = [
            item
            for item in self.candidates
            if not _is_dynamic_canonical_state(item.candidate_id.artifact_relpath)
        ]
        payload = {
            "repository_id": self.repository_id,
            "language_registry_digest": self.language_registry_digest,
            "candidates": [
                {
                    "path": item.candidate_id.artifact_relpath.as_posix(),
                    "role": item.candidate_id.role,
                    "inventory": item.inventory.value,
                    "in_base": item.in_base,
                    "in_head": item.in_head,
                    "provenance": item.ownership_provenance,
                    "base_object_id": item.base_object_id,
                    "base_git_mode": item.base_git_mode,
                    "head_object_id": item.head_object_id,
                    "head_git_mode": item.head_git_mode,
                    "unit": _unit_payload(item.unit_id),
                }
                for item in structural_candidates
            ],
            "units": [
                {
                    "id": _unit_payload(item.unit_id),
                    "present_in_base": item.present_in_base,
                    "present_in_head": item.present_in_head,
                    "artifact_paths": [path.as_posix() for path in item.artifact_paths],
                    "tombstoned": item.tombstoned,
                }
                for item in self.units
            ],
            "expected_managed": [_unit_payload(item) for item in self.expected_managed],
            "invalid_reasons": self.invalid_reasons,
            "unaccounted": [path.as_posix() for path in self.unaccounted_tracked_paths],
        }
        encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
        return hashlib.sha256(encoded).hexdigest()

    def unit_digest(self, unit: ManifestUnit) -> str:
        """Bind one unit to its own manifest slice and relevant policy."""
        if unit not in self.units:
            raise ValueError("unit is not part of this manifest")
        owned_paths = {unit.unit_id.prompt_relpath, *unit.artifact_paths}
        candidates = [
            item
            for item in self.candidates
            if not _is_dynamic_canonical_state(item.candidate_id.artifact_relpath)
            and (
                item.unit_id == unit.unit_id
                or item.candidate_id.artifact_relpath in owned_paths
            )
        ]
        payload = {
            "repository_id": self.repository_id,
            "language_registry_digest": self.language_registry_digest,
            "unit": {
                "id": _unit_payload(unit.unit_id),
                "present_in_base": unit.present_in_base,
                "present_in_head": unit.present_in_head,
                "artifact_paths": [path.as_posix() for path in unit.artifact_paths],
                "tombstoned": unit.tombstoned,
            },
            "candidates": [
                {
                    "path": item.candidate_id.artifact_relpath.as_posix(),
                    "role": item.candidate_id.role,
                    "inventory": item.inventory.value,
                    "in_base": item.in_base,
                    "in_head": item.in_head,
                    "provenance": item.ownership_provenance,
                    "base_object_id": item.base_object_id,
                    "base_git_mode": item.base_git_mode,
                    "head_object_id": item.head_object_id,
                    "head_git_mode": item.head_git_mode,
                    "unit": _unit_payload(item.unit_id),
                }
                for item in candidates
            ],
        }
        encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
        return hashlib.sha256(encoded).hexdigest()


def _unit_payload(unit_id: UnitId | None) -> dict[str, str] | None:
    if unit_id is None:
        return None
    return {
        "repository_id": unit_id.repository_id,
        "prompt_relpath": unit_id.prompt_relpath.as_posix(),
        "language_id": unit_id.language_id,
    }


def _git(root: Path, *args: str) -> bytes:
    result = subprocess.run(
        ["git", *args],
        cwd=root,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        detail = result.stderr.decode(errors="replace").strip()
        raise ManifestError(f"Git inventory command failed: {detail}")
    return result.stdout


def _tree_entries(root: Path, ref: str) -> dict[PurePosixPath, GitTreeEntry]:
    raw = _git(root, "ls-tree", "-r", "-z", "--full-tree", ref)
    entries: dict[PurePosixPath, GitTreeEntry] = {}
    for record in raw.split(b"\0"):
        if not record:
            continue
        metadata, path_bytes = record.split(b"\t", 1)
        mode, object_type, object_id = metadata.decode("ascii").split()
        if object_type not in {"blob", "commit"}:
            continue
        relpath = PurePosixPath(path_bytes.decode("utf-8", errors="strict"))
        entries[relpath] = GitTreeEntry(relpath, mode, object_id)
    return entries


def _blob(root: Path, ref: str, path: PurePosixPath) -> bytes:
    return _git(root, "show", f"{ref}:{path.as_posix()}")


def _prompt_units(
    ref: str,
    entries: dict[PurePosixPath, GitTreeEntry],
    repository_id: str,
    registry: LanguageRegistry,
    ownership_rules: tuple[OwnershipRule, ...],
    protected_owned_paths: set[PurePosixPath],
) -> tuple[dict[PurePosixPath, UnitId], list[str]]:
    # pylint: disable=too-many-arguments,too-many-positional-arguments
    units: dict[PurePosixPath, UnitId] = {}
    invalid: list[str] = []
    for path in sorted(entries):
        if path.suffix != ".prompt" or "_" not in path.stem:
            continue
        rule, rule_error = (
            _ownership_for(path, ownership_rules)
            if path in protected_owned_paths
            else (None, None)
        )
        if rule_error:
            invalid.append(f"{ref}:{rule_error}")
            continue
        if rule is not None and rule.inventory is InventoryStatus.HUMAN_OWNED:
            continue
        language_alias = path.stem.rsplit("_", 1)[1]
        try:
            language = registry.resolve_alias(language_alias)
        except LanguageRegistryError as exc:
            invalid.append(f"{ref}:{path.as_posix()}: {exc}")
            continue
        units[path] = UnitId(repository_id, path, language.language_id)
    return units, invalid


def _architecture_outputs(
    root: Path,
    ref: str,
    entries: dict[PurePosixPath, GitTreeEntry],
    prompt_units: dict[PurePosixPath, UnitId],
    ownership_rules: tuple[OwnershipRule, ...],
    protected_owned_paths: set[PurePosixPath],
) -> tuple[dict[PurePosixPath, UnitId], list[str]]:
    # pylint: disable=too-many-arguments,too-many-positional-arguments,too-many-locals
    outputs: dict[PurePosixPath, UnitId] = {}
    invalid: list[str] = []
    by_name = _paths_by_name(prompt_units)
    for architecture_path in sorted(
        path for path in entries if path.name == "architecture.json"
    ):
        rule, rule_error = (
            _ownership_for(architecture_path, ownership_rules)
            if architecture_path in protected_owned_paths
            else (None, None)
        )
        if rule_error:
            invalid.append(f"{ref}:{rule_error}")
            continue
        if rule is not None and rule.role == "excluded-project":
            continue
        modules, error = _architecture_modules(root, ref, architecture_path)
        if error:
            invalid.append(error)
            continue
        mapped, mapping_errors = _map_architecture_modules(
            ref, architecture_path, modules, by_name, prompt_units
        )
        invalid.extend(mapping_errors)
        for output, unit_id in mapped.items():
            previous = outputs.get(output)
            if previous is not None and previous != unit_id:
                invalid.append(f"{ref}:{output.as_posix()}: duplicate unit ownership")
            else:
                outputs[output] = unit_id
    return outputs, invalid


def _governing_config(
    prompt_path: PurePosixPath,
    entries: dict[PurePosixPath, GitTreeEntry],
) -> PurePosixPath | None:
    # pylint: disable=too-many-arguments,too-many-positional-arguments,too-many-locals
    for parent in (prompt_path.parent, *prompt_path.parents):
        candidate = parent / ".pddrc"
        if candidate in entries:
            return candidate
    root = PurePosixPath(".pddrc")
    return root if root in entries else None


def _config_context(
    payload: object,
    config_path: PurePosixPath,
    prompt_path: PurePosixPath,
) -> tuple[dict[str, object] | None, PurePosixPath | None, str | None]:
    contexts = payload.get("contexts") if isinstance(payload, dict) else None
    if not isinstance(contexts, dict):
        return None, None, "contexts must be a mapping"
    matches: list[tuple[int, int, dict[str, object], PurePosixPath]] = []
    for index, (_name, context) in enumerate(contexts.items()):
        defaults = context.get("defaults") if isinstance(context, dict) else None
        prompts_dir = defaults.get("prompts_dir") if isinstance(defaults, dict) else None
        if not isinstance(prompts_dir, str) or not prompts_dir.strip():
            continue
        root = config_path.parent / PurePosixPath(prompts_dir)
        root = PurePosixPath(posixpath.normpath(root.as_posix()))
        try:
            prompt_path.relative_to(root)
        except ValueError:
            continue
        matches.append((len(root.parts), index, defaults, root))
    if not matches:
        return None, None, None
    matches.sort(key=lambda item: (-item[0], item[1]))
    return matches[0][2], matches[0][3], None


def _configured_output(
    prompt_path: PurePosixPath,
    unit_id: UnitId,
    config_path: PurePosixPath,
    defaults: dict[str, object],
    prompts_root: PurePosixPath,
    registry: LanguageRegistry,
) -> PurePosixPath | None:
    # pylint: disable=too-many-arguments,too-many-positional-arguments,too-many-locals
    relative = prompt_path.relative_to(prompts_root)
    name = relative.stem.rsplit("_", 1)[0]
    category = "" if relative.parent == PurePosixPath(".") else relative.parent.as_posix()
    values = {
        "name": name,
        "language": unit_id.language_id,
        "category": category,
        "dir_prefix": f"{category}/" if category else "",
    }
    outputs = defaults.get("outputs")
    code = outputs.get("code") if isinstance(outputs, dict) else None
    template = code.get("path") if isinstance(code, dict) else None
    if isinstance(template, str) and template:
        try:
            rendered = template.format_map(values)
        except (KeyError, ValueError) as exc:
            raise ManifestError("configured code output template is invalid") from exc
        return config_path.parent / PurePosixPath(rendered)
    generate = defaults.get("generate_output_path")
    if not isinstance(generate, str) or not generate:
        return None
    spec = registry.resolve_alias(unit_id.language_id)
    extensions = tuple(item for item in spec.extensions if item)
    if len(extensions) != 1:
        raise ManifestError("configured output language has no unique extension")
    output_root = config_path.parent / PurePosixPath(generate)
    return output_root / relative.parent / f"{name}{extensions[0]}"


def _config_outputs(
    root: Path,
    ref: str,
    entries: dict[PurePosixPath, GitTreeEntry],
    prompt_units: dict[PurePosixPath, UnitId],
    architecture_outputs: dict[PurePosixPath, UnitId],
    registry: LanguageRegistry,
) -> tuple[dict[PurePosixPath, UnitId], list[str]]:
    # pylint: disable=too-many-arguments,too-many-positional-arguments,too-many-locals
    outputs: dict[PurePosixPath, UnitId] = {}
    invalid: list[str] = []
    architecture_units = set(architecture_outputs.values())
    configs: dict[PurePosixPath, object] = {}
    for prompt_path, unit_id in prompt_units.items():
        if unit_id in architecture_units:
            continue
        config_path = _governing_config(prompt_path, entries)
        if config_path is None:
            continue
        if config_path not in configs:
            try:
                configs[config_path] = yaml.safe_load(_blob(root, ref, config_path))
            except (UnicodeDecodeError, yaml.YAMLError) as exc:
                invalid.append(f"{ref}:{config_path}: invalid config: {exc}")
                configs[config_path] = None
        defaults, prompts_root, error = _config_context(
            configs[config_path], config_path, prompt_path
        )
        if error:
            invalid.append(f"{ref}:{prompt_path}: {error}")
            continue
        if defaults is None or prompts_root is None:
            continue
        try:
            output = _configured_output(
                prompt_path,
                unit_id,
                config_path,
                defaults,
                prompts_root,
                registry,
            )
        except (LanguageRegistryError, ManifestError) as exc:
            invalid.append(f"{ref}:{prompt_path}: {exc}")
            continue
        if output is None:
            continue
        output = PurePosixPath(posixpath.normpath(output.as_posix()))
        if output.is_absolute() or ".." in output.parts:
            invalid.append(f"{ref}:{prompt_path}: configured output escapes repository")
            continue
        previous = outputs.get(output) or architecture_outputs.get(output)
        if previous is not None and previous != unit_id:
            invalid.append(f"{ref}:{output}: duplicate configured output ownership")
            continue
        outputs[output] = unit_id
    return outputs, invalid


def _paths_by_name(
    prompt_units: dict[PurePosixPath, UnitId],
) -> dict[str, list[PurePosixPath]]:
    """Index prompt identities without resolving ambiguous leaves."""
    by_name: dict[str, list[PurePosixPath]] = {}
    for path in prompt_units:
        by_name.setdefault(path.name, []).append(path)
    return by_name


def _architecture_modules(
    root: Path,
    ref: str,
    architecture_path: PurePosixPath,
) -> tuple[list[object], str | None]:
    """Load one architecture module list from an immutable Git blob."""
    try:
        payload = json.loads(_blob(root, ref, architecture_path))
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        return [], f"{ref}:{architecture_path.as_posix()}: invalid JSON: {exc}"
    modules = payload.get("modules", []) if isinstance(payload, dict) else payload
    if not isinstance(modules, list):
        return [], f"{ref}:{architecture_path.as_posix()}: modules must be a list"
    return modules, None


def _map_architecture_modules(
    ref: str,
    architecture_path: PurePosixPath,
    modules: list[object],
    by_name: dict[str, list[PurePosixPath]],
    prompt_units: dict[PurePosixPath, UnitId],
) -> tuple[dict[PurePosixPath, UnitId], list[str]]:
    """Map exact architecture entries without basename guessing."""
    # pylint: disable=too-many-locals
    outputs: dict[PurePosixPath, UnitId] = {}
    invalid: list[str] = []
    for item in modules:
        if not isinstance(item, dict):
            invalid.append(f"{ref}:{architecture_path.as_posix()}: invalid module entry")
            continue
        filename = item.get("filename")
        filepath = item.get("filepath")
        if not isinstance(filename, str) or not isinstance(filepath, str):
            continue
        if PurePosixPath(filename).suffix != ".prompt":
            continue
        declared = PurePosixPath(filename)
        parent = architecture_path.parent
        exact_candidates = (
            parent / "prompts" / declared,
            parent / "pdd" / "prompts" / declared,
            parent / declared,
            PurePosixPath("prompts") / declared,
        )
        exact_match = next(
            (path for path in exact_candidates if path in prompt_units), None
        )
        matches = [exact_match] if exact_match is not None else by_name.get(
            declared.name, []
        )
        if len(matches) != 1:
            invalid.append(
                f"{ref}:{architecture_path.as_posix()}: prompt mapping for "
                f"{filename!r} has {len(matches)} matches"
            )
            continue
        declared_output = PurePosixPath(filepath)
        output = parent / declared_output
        if declared_output.is_absolute() or ".." in declared_output.parts:
            invalid.append(f"{ref}:{architecture_path.as_posix()}: invalid output {filepath}")
            continue
        if output in outputs:
            invalid.append(
                f"{ref}:{architecture_path.as_posix()}: duplicate output {filepath}"
            )
            continue
        outputs[output] = prompt_units[matches[0]]
    return outputs, invalid


def _manifest_unit(
    prompt_path: PurePosixPath,
    sources: _UnitSources,
    tombstone: DecommissionTombstone | None,
    head_ref: str,
) -> tuple[ManifestUnit, str | None]:
    """Build one unit and validate any decommission transition."""
    unit_id = sources.head_units.get(prompt_path) or sources.base_units[prompt_path]
    base_artifacts = {
        path for path, owner in sources.base_outputs.items() if owner == unit_id
    }
    head_artifacts = {
        path for path, owner in sources.head_outputs.items() if owner == unit_id
    }
    removed = prompt_path in sources.base_units and prompt_path not in sources.head_units
    tombstoned = bool(
        removed
        and tombstone
        and set(tombstone.artifact_paths) == base_artifacts | {prompt_path}
        and tombstone.baseline_status == "IN_SYNC"
    )
    reason = None
    if removed and not tombstoned:
        reason = (
            f"{head_ref}:{prompt_path.as_posix()}: removed managed unit lacks "
            "a complete IN_SYNC tombstone"
        )
    elif tombstone and (
        set(tombstone.artifact_paths) != base_artifacts | {prompt_path}
        or tombstone.baseline_status != "IN_SYNC"
    ):
        reason = f"{head_ref}:{prompt_path.as_posix()}: decommission authorization is incomplete"
    unit = ManifestUnit(
        unit_id,
        prompt_path in sources.base_units,
        prompt_path in sources.head_units,
        tuple(sorted(base_artifacts | head_artifacts)),
        tombstoned,
    )
    return unit, reason


def _manifest_units(
    sources: _UnitSources,
    tombstones: dict[PurePosixPath, DecommissionTombstone],
    head_ref: str,
    registry_paths: set[PurePosixPath],
) -> tuple[list[ManifestUnit], list[str]]:
    """Assemble units and validate protected decommission transitions."""
    units: list[ManifestUnit] = []
    invalid: list[str] = []
    paths = set(sources.base_units) | set(sources.head_units)
    for prompt_path in sorted(paths):
        unit, reason = _manifest_unit(
            prompt_path, sources, tombstones.get(prompt_path), head_ref
        )
        units.append(unit)
        if reason:
            invalid.append(reason)
    unknown = set(tombstones) - set(sources.base_units) - registry_paths
    invalid.extend(
        f"{head_ref}:{path.as_posix()}: tombstone has no base unit"
        for path in sorted(unknown)
    )
    return units, invalid


def _candidate_records(
    sources: _CandidateSources,
) -> tuple[list[CandidateRecord], set[PurePosixPath], list[str]]:
    """Partition every tracked path into managed or historical human ownership."""
    candidates: list[CandidateRecord] = []
    accounted: set[PurePosixPath] = set()
    invalid: list[str] = []
    for path in sorted(set(sources.base_entries) | set(sources.head_entries)):
        unit_id = sources.prompt_owner.get(path) or sources.output_owner.get(path)
        if path in sources.base_entries:
            rule, rule_error = _ownership_for(path, sources.ownership_rules)
        else:
            exact_rules = tuple(
                item
                for item in sources.ownership_rules
                if item.preauthorize_absent and item.pattern == path.as_posix()
            )
            rule, rule_error = _ownership_for(path, exact_rules)
        if path in sources.prompt_owner:
            role = "prompt"
            inventory = InventoryStatus.MANAGED
            provenance = "prompt-backed"
        elif path in sources.output_owner:
            role, inventory, provenance = "code", InventoryStatus.MANAGED, "architecture"
        elif rule is not None and rule.role == "excluded-project":
            role = rule.role
            inventory = rule.inventory
            provenance = f"protected-ownership:{rule.owner}:{rule.pattern}"
        elif _is_protected_control(path):
            role = "policy"
            inventory = InventoryStatus.MANAGED
            provenance = "protected-control"
        else:
            if rule is None:
                role = "unaccounted"
                inventory = InventoryStatus.INVALID
                provenance = "none"
                invalid.append(
                    rule_error or f"{path.as_posix()}: tracked path has no ownership rule"
                )
            else:
                role = rule.role
                inventory = rule.inventory
                provenance = f"protected-ownership:{rule.owner}:{rule.pattern}"
        candidates.append(
            CandidateRecord(
                CandidateId(sources.repository_id, path, role),
                inventory,
                path in sources.base_entries,
                path in sources.head_entries,
                provenance,
                sources.base_entries.get(path).object_id
                if path in sources.base_entries
                else None,
                sources.base_entries.get(path).git_mode
                if path in sources.base_entries
                else None,
                sources.head_entries.get(path).object_id
                if path in sources.head_entries
                else None,
                sources.head_entries.get(path).git_mode
                if path in sources.head_entries
                else None,
                unit_id,
            )
        )
        if inventory is not InventoryStatus.INVALID:
            accounted.add(path)
    return candidates, accounted, invalid


def _is_protected_control(path: PurePosixPath) -> bool:
    """Return whether a path is an intrinsic canonical policy/config input."""
    under_canonical_state = _is_dynamic_canonical_state(path)
    return under_canonical_state or (
        path.name in {".pddrc", "architecture.json"}
        or path
        in {
            PurePosixPath(".pdd/repository-id"),
            PurePosixPath(".pdd/expected-managed.json"),
            PurePosixPath(".pdd/sync-policy.json"),
            PurePosixPath(".pdd/verification-profiles.json"),
            PurePosixPath(".pdd/verification-profile-rotations.json"),
            PurePosixPath(".pdd/attestation-trust.json"),
            PurePosixPath(".pdd/sync-ownership.json"),
            PurePosixPath(".pdd/sync-tombstones.json"),
            PurePosixPath(".pdd/sync-waivers.json"),
        }
    )


def _is_dynamic_canonical_state(path: PurePosixPath) -> bool:
    """Return whether content-addressed runtime state must not self-hash."""
    return path.parts[:3] in {
        (".pdd", "meta", "v2"),
        (".pdd", "evidence", "v2"),
    }


def _ownership_for(
    path: PurePosixPath,
    rules: tuple[OwnershipRule, ...],
) -> tuple[OwnershipRule | None, str | None]:
    matches = [rule for rule in rules if fnmatch.fnmatchcase(path.as_posix(), rule.pattern)]
    if not matches:
        return None, None
    outcomes = {(item.inventory, item.role, item.owner) for item in matches}
    if len(outcomes) != 1:
        return None, f"{path.as_posix()}: protected ownership rules are ambiguous"
    return matches[0], None


def _ownership_rules(root: Path, protected_base_ref: str) -> tuple[OwnershipRule, ...]:
    """Load unmatched-path ownership only from the protected base tree."""
    path = PurePosixPath(".pdd/sync-ownership.json")
    raw = read_git_blob(root, protected_base_ref, path)
    if raw is None:
        return ()
    try:
        payload = json.loads(raw)
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise ManifestError("protected sync ownership policy is malformed") from exc
    rows = payload.get("rules") if isinstance(payload, dict) else None
    if not isinstance(rows, list):
        raise ManifestError("protected sync ownership rules must be a list")
    rules: list[OwnershipRule] = []
    patterns: set[str] = set()
    for item in rows:
        if not isinstance(item, dict):
            raise ManifestError("protected ownership rule must be an object")
        try:
            pattern = str(item["pattern"])
            inventory = InventoryStatus(str(item["inventory"]))
            role = str(item["role"])
            owner = str(item["owner"])
        except (KeyError, ValueError) as exc:
            raise ManifestError("protected ownership rule is malformed") from exc
        preauthorize_absent = item.get("preauthorize_absent", False)
        if not isinstance(preauthorize_absent, bool):
            raise ManifestError("protected ownership rule is malformed")
        rule = OwnershipRule(
            pattern, inventory, role, owner, preauthorize_absent
        )
        if not _valid_ownership_rule(rule):
            raise ManifestError("protected ownership rule is overly broad or invalid")
        if pattern in patterns:
            raise ManifestError(f"protected ownership rule has duplicate pattern: {pattern}")
        patterns.add(pattern)
        rules.append(rule)
    return tuple(sorted(rules))


def _valid_ownership_rule(rule: OwnershipRule) -> bool:
    """Reject catch-all or escaping rules that could hide future managed debt."""
    path = PurePosixPath(rule.pattern)
    pattern_valid = (
        rule.pattern not in {"*", "**", "**/*"}
        and not rule.pattern.startswith("/")
        and ".." not in path.parts
    )
    identity_valid = bool(rule.role and rule.owner)
    inventory_valid = rule.inventory in {
        InventoryStatus.MANAGED,
        InventoryStatus.HUMAN_OWNED,
    }
    absent_authorization_valid = not rule.preauthorize_absent or not any(
        token in rule.pattern for token in ("*", "?", "[")
    )
    return (
        pattern_valid
        and identity_valid
        and inventory_valid
        and absent_authorization_valid
    )


def _tree_manifest(
    root: Path,
    ref: str,
    repository_id: str,
    registry: LanguageRegistry,
    ownership_rules: tuple[OwnershipRule, ...],
    protected_owned_paths: Optional[set[PurePosixPath]] = None,
) -> _TreeManifest:
    # pylint: disable=too-many-arguments,too-many-positional-arguments
    """Parse one immutable tree into canonical units and architecture outputs."""
    entries = _tree_entries(root, ref)
    units, unit_invalid = _prompt_units(
        ref,
        entries,
        repository_id,
        registry,
        ownership_rules,
        protected_owned_paths or set(entries),
    )
    outputs, architecture_invalid = _architecture_outputs(
        root,
        ref,
        entries,
        units,
        ownership_rules,
        protected_owned_paths or set(entries),
    )
    configured_outputs, config_invalid = _config_outputs(
        root,
        ref,
        entries,
        units,
        outputs,
        registry,
    )
    outputs.update(configured_outputs)
    generated_prompt_outputs = {
        path
        for path, owner in outputs.items()
        if path in units and units[path] != owner
    }
    units = {
        path: unit_id
        for path, unit_id in units.items()
        if path not in generated_prompt_outputs
    }
    return _TreeManifest(
        ref,
        entries,
        units,
        outputs,
        tuple(unit_invalid + architecture_invalid + config_invalid),
    )


def _protected_expected_units(
    units: list[ManifestUnit],
    tombstones: dict[PurePosixPath, DecommissionTombstone],
    registry: set[UnitId] | None,
) -> tuple[set[UnitId], list[str]]:
    """Apply the protected denominator and authorized removal transitions."""
    discovered = {unit.unit_id for unit in units}
    if registry is None:
        return discovered, []
    missing_registry = {
        unit.unit_id
        for unit in units
        if unit.present_in_base and unit.unit_id not in registry
    }
    authorized_removed = {
        item
        for item in registry
        if item.prompt_relpath in tombstones
        and not any(unit.unit_id == item and unit.present_in_head for unit in units)
    }
    head_additions = {
        unit.unit_id
        for unit in units
        if unit.present_in_head and not unit.present_in_base
    }
    expected = (registry - authorized_removed) | head_additions
    unresolved = registry - discovered - authorized_removed
    invalid = [
        *(
            f"{item.prompt_relpath}: protected expected-managed registry omits base unit"
            for item in sorted(missing_registry)
        ),
        *(
            f"{item.prompt_relpath}: expected managed unit is absent without authorization"
            for item in sorted(unresolved)
        ),
    ]
    return expected, invalid


def _assemble_manifest(
    repository_id: str,
    language_registry_digest: str,
    base: _TreeManifest,
    head: _TreeManifest,
    tombstones: dict[PurePosixPath, DecommissionTombstone],
    expected_registry: set[UnitId] | None,
    ownership_rules: tuple[OwnershipRule, ...],
) -> UnitManifest:
    # pylint: disable=too-many-arguments,too-many-positional-arguments
    """Combine parsed trees into the final candidate and unit partition."""
    invalid = list(base.invalid_reasons + head.invalid_reasons)
    units, tombstone_invalid = _manifest_units(
        _UnitSources(base.units, head.units, base.outputs, head.outputs),
        tombstones,
        head.ref,
        {item.prompt_relpath for item in (expected_registry or set())},
    )
    invalid.extend(tombstone_invalid)
    candidates, accounted, ownership_invalid = _candidate_records(
        _CandidateSources(
            repository_id,
            base.entries,
            head.entries,
            {**base.units, **head.units},
            {**base.outputs, **head.outputs},
            ownership_rules,
        )
    )
    invalid.extend(ownership_invalid)
    expected, expected_invalid = _protected_expected_units(
        units, tombstones, expected_registry
    )
    invalid.extend(expected_invalid)
    return UnitManifest(
        repository_id,
        language_registry_digest,
        ManifestRefs(base.ref, head.ref),
        tuple(candidates),
        tuple(sorted(units)),
        tuple(sorted(expected)),
        tuple(sorted(invalid)),
        tuple(sorted((set(base.entries) | set(head.entries)) - accounted)),
    )


def build_unit_manifest(
    root: Path,
    *,
    base_ref: str,
    head_ref: str,
    registry: Optional[LanguageRegistry] = None,
) -> UnitManifest:
    # pylint: disable=too-many-locals
    """Build the complete protected base/head candidate union from Git objects."""
    repository_root = Path(root).resolve()
    identity_path = PurePosixPath(REPOSITORY_ID_RELPATH.as_posix())
    base_identity = read_git_blob(repository_root, base_ref, identity_path)
    head_identity = read_git_blob(repository_root, head_ref, identity_path)
    if base_identity is None or head_identity is None:
        raise ManifestError("base and head must contain .pdd/repository-id")
    try:
        base_repository_id = canonical_repository_id(base_identity.decode("ascii"))
        head_repository_id = canonical_repository_id(head_identity.decode("ascii"))
    except (UnicodeDecodeError, ValueError) as exc:
        raise ManifestError("protected repository identity is malformed") from exc
    if base_repository_id != head_repository_id:
        raise ManifestError("repository identity changed between protected base and head")
    repository_id = base_repository_id
    language_registry = registry or LanguageRegistry.bundled()
    ownership = _ownership_rules(repository_root, base_ref)
    base = _tree_manifest(
        repository_root, base_ref, repository_id, language_registry, ownership
    )
    head = _tree_manifest(repository_root, head_ref, repository_id,
                          language_registry, ownership, set(base.entries))
    try:
        tombstones = load_tombstones(repository_root, base_ref)
        head_tombstones = load_tombstones(repository_root, head_ref)
        expected_registry = load_expected_registry(
            repository_root, base_ref, repository_id
        )
        head_expected_registry = load_expected_registry(
            repository_root, head_ref, repository_id
        )
    except ValueError as exc:
        raise ManifestError(str(exc)) from exc
    transition = _assemble_manifest(repository_id, language_registry.digest(),
                                    base, head, tombstones, expected_registry,
                                    ownership)
    if base_ref == head_ref:
        return transition

    head_ownership = _ownership_rules(repository_root, head_ref)
    stable_base = _tree_manifest(repository_root, head_ref, repository_id,
                                 language_registry, head_ownership)
    stable = _assemble_manifest(repository_id, language_registry.digest(),
                                stable_base, stable_base, head_tombstones,
                                head_expected_registry, head_ownership)
    control_invalid = control_transition_invalid(
        repository_root, base_ref, head_ref, ownership, head_ownership
    )
    return enforce_head_fixed_point(transition, stable, control_invalid)
