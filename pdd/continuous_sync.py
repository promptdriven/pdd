"""Deterministic continuous-sync classification and reconciliation reports."""
from __future__ import annotations

import json
import os
import stat
import subprocess
from dataclasses import dataclass
from datetime import datetime, timezone
from functools import lru_cache
from itertools import combinations
from pathlib import Path, PurePosixPath
from typing import Any, Dict, Iterable, List, Optional

from .operation_log import (
    _safe_basename,
    infer_module_identity,
)
from .sync_determine_operation import (
    Fingerprint,
    calculate_current_hashes,
    calculate_sha256,
    get_extension,
)
from .sync_core import CanonicalReportOptions, build_canonical_report
from .construct_paths import _find_pddrc_file, _load_pddrc_config


MAX_PROMPT_DISCOVERY_FILES = 10000
MAX_PROMPT_DISCOVERY_ENTRIES = 50000
MAX_REPAIR_DISCOVERY_ENTRIES = 50000
SKIPPED_DISCOVERY_DIRS = {
    ".git",
    ".hg",
    ".svn",
    ".pdd",
    "__pycache__",
    "node_modules",
    ".venv",
    "venv",
}
DRIFT_CLASSIFICATIONS = {
    "DOC_CHANGED",
    "PROMPT_CHANGED",
    "CODE_CHANGED",
    "TEST_CHANGED",
    "EXAMPLE_CHANGED",
    "DERIVED_CHANGED",
}
CONFLICT_CLASSIFICATION = "CONFLICT"
UNBASELINED_CLASSIFICATION = "UNBASELINED"
FAILURE_CLASSIFICATION = "FAILURE"


@dataclass(frozen=True)
class SyncUnit:
    """A prompt-derived unit discovered for deterministic classification."""

    basename: str
    language: str
    prompt_path: Path
    prompts_dir: Path


@dataclass(frozen=True)
class DiscoveryFailure:
    """A prompt discovery failure that must be visible in JSON output."""

    prompt_root: Path
    reason: str
    failure: str


def project_root(start: Optional[Path] = None) -> Path:
    """Return the nearest PDD project root, then git root, then CWD."""
    current = (start or Path.cwd()).resolve()
    if current.is_file():
        current = current.parent
    for candidate in (current, *current.parents):
        if (candidate / ".pddrc").exists():
            return candidate
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=str(current),
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode == 0 and result.stdout.strip():
            return Path(result.stdout.strip()).resolve()
    except OSError:
        pass
    return current


def repository_root(start: Optional[Path] = None) -> Path:
    """Return the enclosing Git repository root independently of `.pddrc`."""
    current = (start or Path.cwd()).resolve()
    if not current.is_dir():
        current = current.parent
    while not current.exists() and current.parent != current:
        current = current.parent
    result = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        cwd=current,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0 or not result.stdout.strip():
        return current
    return Path(result.stdout.strip()).resolve()


def _git_root_from_marker(start: Path) -> Optional[Path]:
    """Resolve the enclosing worktree root without spawning Git."""
    candidate = start if start.is_dir() else start.parent
    for parent in (candidate, *candidate.parents):
        if (parent / ".git").exists():
            return parent
    return None


def _git_head_token(root: Path) -> str:
    """Return a filesystem token that changes when checked-out HEAD changes."""
    marker = root / ".git"
    git_dir = marker
    if marker.is_file():
        value = marker.read_text(encoding="utf-8").strip()
        if not value.startswith("gitdir:"):
            return value
        git_dir = Path(value.split(":", 1)[1].strip())
        if not git_dir.is_absolute():
            git_dir = (root / git_dir).resolve()
    try:
        value = (git_dir / "HEAD").read_text(encoding="utf-8").strip()
    except OSError:
        return ""
    if value.startswith("ref:"):
        ref_name = value.split(":", 1)[1].strip()
        common_dir = git_dir
        try:
            common_value = (git_dir / "commondir").read_text(encoding="utf-8").strip()
            common_dir = Path(common_value)
            if not common_dir.is_absolute():
                common_dir = (git_dir / common_dir).resolve()
        except OSError:
            pass
        ref = common_dir / ref_name
        try:
            return f"{value}:{ref.read_text(encoding='utf-8').strip()}"
        except OSError:
            try:
                packed = (common_dir / "packed-refs").read_text(encoding="utf-8")
            except OSError:
                packed = ""
            suffix = f" {ref_name}"
            for line in packed.splitlines():
                if line.endswith(suffix):
                    return f"{value}:{line.split(' ', 1)[0]}"
    return value


@lru_cache(maxsize=128)
def _committed_canonical_policy(
    root_value: str,
    protected_ref: str,
    head_token: str,
) -> tuple[bool, str]:
    """Read activation once per repository, protected ref, and checked-out HEAD."""
    del head_token  # Included solely to invalidate the cache after HEAD movement.
    root = Path(root_value)
    policy = subprocess.run(
        ["git", "show", f"{protected_ref}:.pdd/sync-policy.json"],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    if policy.returncode != 0:
        return False, "policy cannot be resolved"
    identity = subprocess.run(
        ["git", "cat-file", "-e", f"{protected_ref}:.pdd/repository-id"],
        cwd=root,
        capture_output=True,
        check=False,
    )
    if identity.returncode != 0:
        return False, "identity cannot be resolved"
    try:
        payload = json.loads(policy.stdout)
    except json.JSONDecodeError:
        return False, "policy is malformed"
    if payload != {"schema_version": 1, "enforcement": "active"}:
        return False, "policy is not active"
    return True, ""


def canonical_sync_enabled(root: Path) -> bool:
    """Return whether protected committed policy activates canonical sync."""
    protected_ref = os.environ.get("PDD_SYNC_PROTECTED_BASE_SHA")
    candidate = Path(root).resolve()
    if not candidate.is_dir():
        candidate = candidate.parent
    if protected_ref is None:
        ancestors = (candidate, *candidate.parents)
        has_worktree_policy = any(
            (parent / ".pdd/sync-policy.json").is_file() for parent in ancestors
        )
        repository_marker = next(
            (
                parent / ".git"
                for parent in ancestors
                if (parent / ".git").exists()
            ),
            None,
        )
        has_repository_marker = bool(
            repository_marker is not None
            and (
                repository_marker.is_dir()
                or _valid_gitdir_file(repository_marker)
            )
        )
        if not has_worktree_policy and not has_repository_marker:
            return False
    root = _git_root_from_marker(candidate)
    if root is None:
        if protected_ref is not None:
            raise ValueError("explicit protected sync repository cannot be resolved")
        return False
    protected_ref = protected_ref or "HEAD"
    active, reason = _committed_canonical_policy(
        str(root), protected_ref, _git_head_token(root)
    )
    if not active and os.environ.get("PDD_SYNC_PROTECTED_BASE_SHA") is not None:
        raise ValueError(f"explicit protected sync {reason}")
    return active


def _valid_gitdir_file(marker: Path) -> bool:
    """Return whether a file-form linked-worktree marker names a live gitdir."""
    if not marker.is_file():
        return False
    try:
        prefix, value = marker.read_text(encoding="utf-8").strip().split(":", 1)
    except (OSError, ValueError, UnicodeDecodeError):
        return False
    if prefix.casefold() != "gitdir":
        return False
    gitdir = Path(value.strip())
    if not gitdir.is_absolute():
        gitdir = marker.parent / gitdir
    return gitdir.is_dir()


def _prompts_dir_for(prompt_path: Path) -> Path:
    """Return the concrete prompts directory to pass into path resolution."""
    return prompt_path.parent


def _is_hidden_or_system_dir(path: Path) -> bool:
    return path.name.startswith(".") or path.name in SKIPPED_DISCOVERY_DIRS


def _bounded_prompt_paths(prompt_root: Path) -> tuple[List[Path], Optional[DiscoveryFailure]]:
    prompt_paths: List[Path] = []
    visited_entries = 0
    walk_failure: DiscoveryFailure | None = None

    def on_walk_error(error: OSError) -> None:
        nonlocal walk_failure
        walk_failure = DiscoveryFailure(
            prompt_root=prompt_root,
            reason=f"configured prompt root traversal failed: {error}",
            failure="prompt_traversal_error",
        )

    for current_root, dirnames, filenames in os.walk(prompt_root, onerror=on_walk_error):
        if walk_failure is not None:
            return prompt_paths, walk_failure
        current = Path(current_root)
        visited_entries += 1 + len(dirnames) + len(filenames)
        if visited_entries > MAX_PROMPT_DISCOVERY_ENTRIES:
            return prompt_paths, DiscoveryFailure(
                prompt_root=prompt_root,
                reason=(
                    "configured prompt root exceeded traversal budget "
                    f"of {MAX_PROMPT_DISCOVERY_ENTRIES} directory entries"
                ),
                failure="prompt_traversal_budget",
            )
        dirnames[:] = [
            dirname
            for dirname in sorted(dirnames)
            if not _is_hidden_or_system_dir(current / dirname)
        ]
        for filename in sorted(filenames):
            if not filename.endswith(".prompt") or "_" not in filename:
                continue
            prompt_paths.append(current / filename)
            if len(prompt_paths) > MAX_PROMPT_DISCOVERY_FILES:
                return prompt_paths, DiscoveryFailure(
                    prompt_root=prompt_root,
                    reason=(
                        "configured prompt root exceeded traversal budget "
                        f"of {MAX_PROMPT_DISCOVERY_FILES} prompt files"
                    ),
                    failure="prompt_traversal_budget",
                )
    return sorted(prompt_paths), None


def _prompt_units(prompt_root: Path) -> tuple[List[SyncUnit], List[DiscoveryFailure]]:
    units: List[SyncUnit] = []
    failures: List[DiscoveryFailure] = []
    prompt_paths, failure = _bounded_prompt_paths(prompt_root)
    if failure is not None:
        failures.append(failure)
    for prompt_path in prompt_paths[:MAX_PROMPT_DISCOVERY_FILES]:
        basename, language = infer_module_identity(prompt_path)
        if basename is None or language is None:
            continue
        units.append(
            SyncUnit(
                basename=basename,
                language=language,
                prompt_path=prompt_path,
                prompts_dir=_prompts_dir_for(prompt_path),
            )
        )
    return units, failures


def _is_safe_prompt_root(base: Path, prompt_root: Path) -> bool:
    """Return whether a configured prompt root is within the project boundary."""
    try:
        prompt_root.resolve(strict=False).relative_to(base.resolve(strict=False))
    except ValueError:
        return False
    return True


def _configured_prompt_roots(base: Path) -> List[Path]:
    """Return normalized prompt roots configured for the legacy report.

    The report owns discovery, so configured roots must be resolved before it
    passes a fixed relative pattern to ``Path.rglob``.  In particular, an
    absolute ``prompts_dir`` is a root, never a glob pattern to append to one.
    """
    pddrc_path = _find_pddrc_file(base)
    configured: List[Path] = []
    if pddrc_path is not None:
        try:
            contexts = _load_pddrc_config(pddrc_path).get("contexts", {})
        except ValueError:
            contexts = {}
        for context in contexts.values():
            defaults = context.get("defaults", {}) if isinstance(context, dict) else {}
            raw_root = defaults.get("prompts_dir")
            if not isinstance(raw_root, str) or not raw_root.strip():
                continue
            root = Path(raw_root).expanduser()
            if not root.is_absolute():
                root = pddrc_path.parent / root
            configured.append(root.resolve(strict=False))

    if not configured:
        configured.append((base / "prompts").resolve(strict=False))
    return list(dict.fromkeys(configured))


def _validated_prompt_roots(base: Path) -> tuple[List[Path], List[DiscoveryFailure]]:
    roots: List[Path] = []
    failures: List[DiscoveryFailure] = []
    for prompt_root in _configured_prompt_roots(base):
        if _is_safe_prompt_root(base, prompt_root):
            roots.append(prompt_root)
            continue
        failures.append(
            DiscoveryFailure(
                prompt_root=prompt_root,
                reason="configured prompt root is outside project",
                failure="unsafe_prompt_root",
            )
        )
    return roots, failures


def _matches_module(unit: SyncUnit, wanted: set[str]) -> bool:
    return (
        unit.basename in wanted
        or _safe_basename(unit.basename) in wanted
        or unit.prompt_path.stem in wanted
    )


def _metadata_identity(path: Path) -> Optional[tuple[str, str]]:
    stem = path.stem
    if stem.endswith("_run") or "_" not in stem:
        return None
    basename, language = stem.rsplit("_", 1)
    if not basename or not language:
        return None
    return basename, language


def _module_token_basename(token: str, language: str) -> str:
    basename = token[:-7] if token.endswith(".prompt") else token
    language_suffix = f"_{language}"
    if basename.endswith(language_suffix):
        return basename[: -len(language_suffix)]
    return basename


def _requested_basename_for_identity(
    identity: tuple[str, str],
    wanted: set[str],
) -> Optional[str]:
    safe_basename, language = identity
    for item in sorted(wanted):
        basename = _module_token_basename(item, language)
        if basename == safe_basename or _safe_basename(basename) == safe_basename:
            return basename
    return None


def _identity_matches_wanted(identity: tuple[str, str], wanted: set[str]) -> bool:
    safe_basename, language = identity
    return (
        safe_basename in wanted
        or f"{safe_basename}_{language}" in wanted
        or f"{safe_basename}_{language}.prompt" in wanted
        or _requested_basename_for_identity(identity, wanted) is not None
    )


def _prompt_path_for_basename(prompt_root: Path, basename: str, language: str) -> Path:
    parts = Path(basename).parts
    if len(parts) <= 1:
        return prompt_root / f"{basename}_{language}.prompt"
    return prompt_root.joinpath(*parts[:-1], f"{parts[-1]}_{language}.prompt")


def _slash_candidates(safe_basename: str) -> List[str]:
    parts = safe_basename.split("_")
    if len(parts) <= 1:
        return []

    candidates: List[str] = []
    separators = range(1, len(parts))
    for count in range(1, len(parts)):
        for slash_positions in combinations(separators, count):
            chunks: List[str] = [parts[0]]
            for index, part in enumerate(parts[1:], start=1):
                if index in slash_positions:
                    chunks.append("/")
                else:
                    chunks.append("_")
                chunks.append(part)
            candidates.append("".join(chunks))
    return candidates


def _existing_artifact_score(
    basename: str,
    language: str,
    prompt_root: Path,
) -> int:
    try:
        prompt_path = prompt_root / f"{Path(basename).name}_{language}.prompt"
        paths = _resolve_report_paths(
            SyncUnit(basename, language, prompt_path, prompt_root),
            project_root(prompt_root),
        )
    except ValueError:
        return 0
    score = 0
    for artifact in ("code", "example", "test"):
        path = paths.get(artifact)
        if path is not None and path.exists():
            score += 1
    return score


def _infer_basename_from_artifacts(
    safe_basename: str,
    language: str,
    prompt_root: Path,
) -> str:
    best = safe_basename
    best_score = _existing_artifact_score(best, language, prompt_root)
    for candidate in _slash_candidates(safe_basename):
        score = _existing_artifact_score(candidate, language, prompt_root)
        if score > best_score:
            best = candidate
            best_score = score
    return best


def _unit_from_metadata_identity(
    identity: tuple[str, str],
    prompt_root: Path,
    prompt_index: Dict[tuple[str, str], SyncUnit],
    requested_basename: Optional[str] = None,
) -> SyncUnit:
    safe_basename, language = identity
    prompt_unit = prompt_index.get((safe_basename, language))
    if prompt_unit is not None:
        return prompt_unit

    basename = requested_basename or _infer_basename_from_artifacts(
        safe_basename,
        language,
        prompt_root,
    )
    prompt_path = _prompt_path_for_basename(prompt_root, basename, language)
    return SyncUnit(
        basename=basename,
        language=language,
        prompt_path=prompt_path,
        prompts_dir=prompt_root,
    )


def _metadata_identities(meta_root: Path) -> List[tuple[str, str]]:
    identities: List[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()
    if not meta_root.exists():
        return identities
    for path in sorted(meta_root.glob("*_*.json")):
        identity = _metadata_identity(path)
        if identity is None or identity in seen:
            continue
        seen.add(identity)
        identities.append(identity)
    return identities


def discover_units(
    root: Optional[Path] = None,
    modules: Optional[Iterable[str]] = None,
) -> List[SyncUnit]:
    """Discover prompt-backed units under ``root``."""
    units, _failures = _discover_units_and_failures(root, modules)
    return units


def _append_unique_unit(
    units: List[SyncUnit],
    seen: set[tuple[str, str, Path]],
    unit: SyncUnit,
) -> None:
    dedupe_key = (unit.basename, unit.language, unit.prompt_path)
    if dedupe_key in seen:
        return
    seen.add(dedupe_key)
    units.append(unit)


def _metadata_units(
    metadata_identities: List[tuple[str, str]],
    prompt_root: Path,
    prompt_index: Dict[tuple[str, str], SyncUnit],
    wanted: set[str],
) -> List[SyncUnit]:
    units: List[SyncUnit] = []
    seen: set[tuple[str, str, Path]] = set()
    for identity in metadata_identities:
        if wanted and not _identity_matches_wanted(identity, wanted):
            continue
        unit = _unit_from_metadata_identity(
            identity,
            prompt_root,
            prompt_index,
            requested_basename=_requested_basename_for_identity(identity, wanted),
        )
        _append_unique_unit(units, seen, unit)
    return units


def _discover_units_and_failures(
    root: Optional[Path] = None,
    modules: Optional[Iterable[str]] = None,
) -> tuple[List[SyncUnit], List[DiscoveryFailure]]:
    """Discover prompt-backed units and discovery failures under ``root``."""
    base = project_root(root)
    wanted = set(modules or [])
    prompt_roots, failures = _validated_prompt_roots(base)
    prompt_units: List[SyncUnit] = []
    for prompt_root in prompt_roots:
        if not prompt_root.is_dir():
            continue
        units, unit_failures = _prompt_units(prompt_root)
        prompt_units.extend(units)
        failures.extend(unit_failures)
    metadata_identities = _metadata_identities(base / ".pdd" / "meta")

    units = _metadata_units(
        metadata_identities,
        prompt_roots[0] if prompt_roots else base / "prompts",
        _prompt_index(prompt_units),
        wanted,
    )
    seen = {(unit.basename, unit.language, unit.prompt_path) for unit in units}
    if wanted:
        for unit in prompt_units:
            if not _matches_module(unit, wanted):
                continue
            _append_unique_unit(units, seen, unit)
        return units, failures

    for unit in prompt_units:
        _append_unique_unit(units, seen, unit)
    return units, failures


def _prompt_index(prompt_units: List[SyncUnit]) -> Dict[tuple[str, str], SyncUnit]:
    prompt_index: Dict[tuple[str, str], SyncUnit] = {}
    for unit in prompt_units:
        prompt_index.setdefault((_safe_basename(unit.basename), unit.language), unit)
    return prompt_index


def _discovery_failure_payload(failure: DiscoveryFailure, root: Path) -> Dict[str, Any]:
    try:
        prompt_root = failure.prompt_root.resolve(strict=False).relative_to(
            root.resolve()
        ).as_posix()
    except ValueError:
        prompt_root = str(failure.prompt_root)
    return {
        "basename": "",
        "language": "",
        "classification": FAILURE_CLASSIFICATION,
        "operation": "none",
        "reason": failure.reason,
        "changed_files": [],
        "metadata_valid": False,
        "paths": {"prompt_root": prompt_root},
        "failure": failure.failure,
    }


def _load_fingerprint_json(path: Path) -> tuple[Optional[Dict[str, Any]], Optional[str]]:
    try:
        mode = path.lstat().st_mode
    except FileNotFoundError:
        return None, "missing"
    if stat.S_ISLNK(mode) or not stat.S_ISREG(mode):
        return None, "invalid"
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None, "invalid"
    if not isinstance(data, dict):
        return None, "invalid"
    return data, None


def _fingerprint_from_payload(payload: Dict[str, Any]) -> Optional[Fingerprint]:
    """Decode the legacy fingerprint without invoking its directory-creating reader."""
    try:
        return Fingerprint(
            pdd_version=payload["pdd_version"],
            timestamp=payload["timestamp"],
            command=payload["command"],
            prompt_hash=payload.get("prompt_hash"),
            code_hash=payload.get("code_hash"),
            example_hash=payload.get("example_hash"),
            test_hash=payload.get("test_hash"),
            test_files=payload.get("test_files"),
            include_deps=payload.get("include_deps"),
        )
    except (KeyError, TypeError):
        return None


def _relative_or_raw(path: Path, root: Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return str(path)


def _paths_as_json(paths: Dict[str, Any], root: Path) -> Dict[str, Any]:
    payload: Dict[str, Any] = {}
    resolved_root = root.resolve()
    for key, value in paths.items():
        if isinstance(value, Path):
            try:
                payload[key] = value.resolve().relative_to(resolved_root).as_posix()
            except (OSError, ValueError):
                payload[key] = str(value)
        elif isinstance(value, list):
            payload[key] = [str(item) for item in value]
        else:
            payload[key] = str(value)
    return payload


def _architecture_filepath(
    unit: SyncUnit,
    base: Path,
) -> Path | None:
    """Return an architecture.json filepath match without mutating project state."""
    candidates = (unit.prompts_dir.parent / "architecture.json", base / "architecture.json")
    for architecture_path in dict.fromkeys(path.resolve(strict=False) for path in candidates):
        if not architecture_path.is_file():
            continue
        try:
            payload = json.loads(architecture_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise ValueError(f"architecture config is invalid: {architecture_path}") from exc
        if not isinstance(payload, list):
            raise ValueError(f"architecture config is invalid: {architecture_path}")
        matches: list[Path] = []
        for item in payload:
            if not isinstance(item, dict):
                continue
            filename = item.get("filename")
            filepath = item.get("filepath")
            if not isinstance(filename, str) or not isinstance(filepath, str):
                continue
            filename_path = Path(filename)
            prompt_matches = filename_path.name == unit.prompt_path.name
            try:
                prompt_matches = prompt_matches or filename_path == unit.prompt_path.relative_to(
                    unit.prompts_dir
                )
            except ValueError:
                pass
            if prompt_matches:
                output = Path(filepath)
                if output.is_absolute() or ".." in output.parts:
                    raise ValueError(f"architecture output is invalid: {filepath}")
                matches.append(architecture_path.parent / output)
        if len(matches) > 1:
            raise ValueError("ambiguous module configuration")
        if matches:
            return matches[0]
    return None


def _resolve_report_paths(unit: SyncUnit, base: Path) -> Dict[str, Any]:
    """Resolve report paths without creating directories or files."""
    extension = get_extension(unit.language)
    suffix = f".{extension}" if extension else ""
    code_path = _architecture_filepath(unit, base)
    code_stem = code_path.stem if code_path is not None else Path(unit.basename).name
    if code_path is None:
        code_path = base / f"{code_stem}{suffix}"
    return {
        "prompt": unit.prompt_path,
        "code": code_path,
        "example": base / "examples" / f"{code_stem}_example{suffix}",
        "test": base / "tests" / f"test_{code_stem}{suffix}",
        "test_files": [base / "tests" / f"test_{code_stem}{suffix}"],
    }


def _is_within_root(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
        return True
    except ValueError:
        return False


def _artifact_path_violation(path: Path, root: Path) -> Optional[str]:
    root = root.resolve()
    candidate = path if path.is_absolute() else root / path
    try:
        mode = candidate.lstat().st_mode
    except FileNotFoundError:
        mode = None
    if mode is not None and stat.S_ISLNK(mode):
        return "is a symlink"
    resolved = candidate.resolve(strict=False)
    if not _is_within_root(resolved, root):
        return "resolves outside project"
    if mode is None:
        return None
    if not stat.S_ISREG(mode):
        return "is not a regular file"
    return None


def _unsafe_fingerprinted_artifacts(
    paths: Dict[str, Any],
    root: Path,
) -> Dict[str, str]:
    unsafe: Dict[str, str] = {}
    for artifact in ("prompt", "code", "example", "test"):
        path = paths.get(artifact)
        if isinstance(path, Path):
            violation = _artifact_path_violation(path, root)
            if violation:
                unsafe[artifact] = violation
    for path in paths.get("test_files", []):
        if isinstance(path, Path):
            violation = _artifact_path_violation(path, root)
            if violation:
                unsafe[f"test_files:{_relative_or_raw(path, root.resolve())}"] = violation
    return unsafe


def _changed_artifacts(
    fingerprint: Fingerprint,
    paths: Dict[str, Path],
    current_hashes: Dict[str, Any],
) -> List[str]:
    changes: List[str] = []
    if current_hashes.get("prompt_hash") != fingerprint.prompt_hash:
        if (current_hashes.get("include_deps") or {}) != (
            fingerprint.include_deps or {}
        ):
            changes.append("doc")
        else:
            changes.append("prompt")
    if (
        paths.get("code")
        and paths["code"].exists()
        and current_hashes.get("code_hash") != fingerprint.code_hash
    ):
        changes.append("code")
    if (
        paths.get("example")
        and paths["example"].exists()
        and current_hashes.get("example_hash") != fingerprint.example_hash
    ):
        changes.append("example")
    if (
        paths.get("test")
        and paths["test"].exists()
        and current_hashes.get("test_hash") != fingerprint.test_hash
    ):
        changes.append("test")
    return changes


def _missing_fingerprinted_artifacts(
    fingerprint: Fingerprint,
    paths: Dict[str, Path],
) -> List[str]:
    missing: List[str] = []
    field_by_artifact = {
        "prompt": "prompt_hash",
        "code": "code_hash",
        "example": "example_hash",
        "test": "test_hash",
    }
    for artifact, field in field_by_artifact.items():
        path = paths.get(artifact)
        if getattr(fingerprint, field) and (path is None or not path.exists()):
            missing.append(artifact)
    return missing


def _artifact_search_name(
    artifact: str,
    basename: str,
    expected_path: Path,
) -> Optional[str]:
    suffix = expected_path.suffix
    leaf = Path(basename).name
    if artifact == "code":
        return f"{leaf}{suffix}"
    if artifact == "example":
        return f"{leaf}_example{suffix}"
    if artifact == "test":
        return f"test_{leaf}{suffix}"
    return None


def _find_matching_artifact(
    root: Path,
    filename: str,
    expected_hash: str,
) -> tuple[Optional[Path], Optional[DiscoveryFailure]]:
    matches: List[Path] = []
    resolved_root = root.resolve()
    visited_entries = 0
    walk_failure: DiscoveryFailure | None = None

    def on_walk_error(error: OSError) -> None:
        nonlocal walk_failure
        walk_failure = DiscoveryFailure(
            prompt_root=root,
            reason=f"repair search traversal failed: {error}",
            failure="repair_traversal_error",
        )

    for current_root, dirnames, filenames in os.walk(root, onerror=on_walk_error):
        if walk_failure is not None:
            return None, walk_failure
        current = Path(current_root)
        dirnames[:] = [
            dirname
            for dirname in sorted(dirnames)
            if not _is_hidden_or_system_dir(current / dirname)
        ]
        filenames = sorted(filenames)
        visited_entries += 1 + len(dirnames) + len(filenames)
        if visited_entries > MAX_REPAIR_DISCOVERY_ENTRIES:
            return None, DiscoveryFailure(
                prompt_root=root,
                reason=(
                    "repair search exceeded traversal budget "
                    f"of {MAX_REPAIR_DISCOVERY_ENTRIES} directory entries"
                ),
                failure="repair_traversal_budget",
            )
        for candidate_name in filenames:
            if candidate_name != filename:
                continue
            candidate = current / candidate_name
            if _artifact_path_violation(candidate, resolved_root):
                continue
            if candidate.is_file() and calculate_sha256(candidate) == expected_hash:
                matches.append(candidate)
    if len(matches) == 1:
        return matches[0], None
    return None, None


def _repair_missing_fingerprinted_paths(
    paths: Dict[str, Path],
    fingerprint: Fingerprint,
    basename: str,
    root: Path,
) -> tuple[Dict[str, Path], Optional[DiscoveryFailure]]:
    repaired = dict(paths)
    field_by_artifact = {
        "code": "code_hash",
        "example": "example_hash",
        "test": "test_hash",
    }
    for artifact, field in field_by_artifact.items():
        path = repaired.get(artifact)
        expected_hash = getattr(fingerprint, field)
        if path is None or path.exists() or not expected_hash:
            continue
        filename = _artifact_search_name(artifact, basename, path)
        if not filename:
            continue
        match, failure = _find_matching_artifact(root, filename, expected_hash)
        if failure is not None:
            return repaired, failure
        if match is None:
            continue
        repaired[artifact] = match
        if artifact == "test":
            repaired["test_files"] = [match]
    return repaired, None


def _missing_required_hashes(fingerprint: Fingerprint, paths: Dict[str, Path]) -> List[str]:
    missing: List[str] = []
    field_by_artifact = {
        "prompt": "prompt_hash",
        "code": "code_hash",
        "example": "example_hash",
        "test": "test_hash",
    }
    for artifact, field in field_by_artifact.items():
        path = paths.get(artifact)
        if path is not None and path.exists() and not getattr(fingerprint, field):
            missing.append(field)
    return missing


def _operation_for(classification: str, changes: List[str]) -> str:
    # pylint: disable=too-many-return-statements
    if classification == "IN_SYNC":
        return "nothing"
    if classification == "DOC_CHANGED":
        return "reconcile"
    if classification == "PROMPT_CHANGED":
        return "generate"
    if classification == "CODE_CHANGED":
        return "update"
    if classification == "TEST_CHANGED":
        return "test"
    if classification == "EXAMPLE_CHANGED":
        return "verify"
    if classification == "CONFLICT":
        return "conflict"
    if classification in {"UNBASELINED", "FAILURE"}:
        return "none"
    if "code" in changes or "example" in changes:
        return "verify"
    if "test" in changes:
        return "test"
    return "reconcile"


def _classification_for_changes(changes: List[str]) -> str:
    # pylint: disable=too-many-return-statements
    derived = [item for item in changes if item not in {"prompt", "doc"}]
    if any(item in changes for item in ("prompt", "doc")) and derived:
        return CONFLICT_CLASSIFICATION
    if changes == ["doc"]:
        return "DOC_CHANGED"
    if changes == ["prompt"]:
        return "PROMPT_CHANGED"
    if changes == ["code"]:
        return "CODE_CHANGED"
    if changes == ["test"]:
        return "TEST_CHANGED"
    if changes == ["example"]:
        return "EXAMPLE_CHANGED"
    if changes:
        return "DERIVED_CHANGED"
    return "IN_SYNC"


def classify_unit(unit: SyncUnit, root: Optional[Path] = None) -> Dict[str, Any]:
    # pylint: disable=broad-exception-caught,too-many-locals,too-many-return-statements
    """Classify one sync unit without mutating files."""
    base = project_root(root)
    # A report must not create `.pdd/meta` just to discover that no fingerprint
    # exists.  The legacy helper creates its parent directory as a write-side
    # convenience, so derive the read-only project-relative location here.
    fp_path = base / ".pdd" / "meta" / f"{_safe_basename(unit.basename)}_{unit.language}.json"
    try:
        paths = _resolve_report_paths(unit, base)
    except Exception as exc:  # pragma: no cover - surfaced in JSON report
        return {
            "basename": unit.basename,
            "language": unit.language,
            "classification": FAILURE_CLASSIFICATION,
            "operation": "none",
            "reason": f"path resolution failed: {exc}",
            "changed_files": [],
            "metadata_valid": False,
            "fingerprint_path": str(fp_path),
            "paths": {"prompt": str(unit.prompt_path)},
            "failure": "path_resolution",
        }

    _raw_fp, raw_error = _load_fingerprint_json(fp_path)
    fingerprint = (
        None if raw_error is not None else _fingerprint_from_payload(_raw_fp)
    )
    if raw_error is not None or fingerprint is None:
        return {
            "basename": unit.basename,
            "language": unit.language,
            "classification": UNBASELINED_CLASSIFICATION,
            "operation": "none",
            "reason": (
                f"fingerprint {raw_error}"
                if raw_error is not None
                else "fingerprint invalid"
            ),
            "changed_files": [],
            "metadata_valid": False,
            "fingerprint_path": str(fp_path),
            "paths": _paths_as_json(paths, base),
        }

    if not unit.prompt_path.exists():
        paths, repair_failure = _repair_missing_fingerprinted_paths(
            paths,
            fingerprint,
            unit.basename,
            base,
        )
        if repair_failure is not None:
            return {
                "basename": unit.basename,
                "language": unit.language,
                "classification": FAILURE_CLASSIFICATION,
                "operation": "none",
                "reason": repair_failure.reason,
                "changed_files": [],
                "metadata_valid": False,
                "fingerprint_path": str(fp_path),
                "paths": _paths_as_json(paths, base),
                "failure": repair_failure.failure,
            }

    unsafe_artifacts = _unsafe_fingerprinted_artifacts(paths, base)
    if unsafe_artifacts:
        changed_files = sorted(
            key.split(":", 1)[0] for key in unsafe_artifacts
        )
        return {
            "basename": unit.basename,
            "language": unit.language,
            "classification": FAILURE_CLASSIFICATION,
            "operation": "none",
            "reason": "unsafe fingerprinted artifacts: "
            + ", ".join(
                f"{artifact} {reason}"
                for artifact, reason in sorted(unsafe_artifacts.items())
            ),
            "changed_files": changed_files,
            "metadata_valid": False,
            "fingerprint_path": str(fp_path),
            "paths": _paths_as_json(paths, base),
            "failure": "unsafe_artifacts",
        }

    missing_hashes = _missing_required_hashes(fingerprint, paths)
    if missing_hashes:
        return {
            "basename": unit.basename,
            "language": unit.language,
            "classification": FAILURE_CLASSIFICATION,
            "operation": "none",
            "reason": "incomplete metadata: " + ", ".join(sorted(missing_hashes)),
            "changed_files": [],
            "metadata_valid": False,
            "fingerprint_path": str(fp_path),
            "paths": _paths_as_json(paths, base),
            "failure": "incomplete_metadata",
        }

    missing_artifacts = _missing_fingerprinted_artifacts(fingerprint, paths)
    if missing_artifacts:
        return {
            "basename": unit.basename,
            "language": unit.language,
            "classification": FAILURE_CLASSIFICATION,
            "operation": "none",
            "reason": "missing fingerprinted artifacts: "
            + ", ".join(sorted(missing_artifacts)),
            "changed_files": missing_artifacts,
            "metadata_valid": True,
            "fingerprint_path": str(fp_path),
            "paths": _paths_as_json(paths, base),
            "failure": "missing_artifacts",
        }

    current_hashes = calculate_current_hashes(
        paths,
        stored_include_deps=fingerprint.include_deps,
    )
    changes = _changed_artifacts(fingerprint, paths, current_hashes)
    classification = _classification_for_changes(changes)
    return {
        "basename": unit.basename,
        "language": unit.language,
        "classification": classification,
        "operation": _operation_for(classification, changes),
        "reason": (
            "all hashes match fingerprint"
            if classification == "IN_SYNC"
            else f"{', '.join(changes)} changed since fingerprint"
        ),
        "changed_files": changes,
        "metadata_valid": True,
        "fingerprint_path": str(fp_path),
        "paths": _paths_as_json(paths, base),
        "hashes": {
            "prompt_hash": current_hashes.get("prompt_hash"),
            "code_hash": current_hashes.get("code_hash"),
            "example_hash": current_hashes.get("example_hash"),
            "test_hash": current_hashes.get("test_hash"),
        },
    }


def _build_summary(units: List[Dict[str, Any]]) -> Dict[str, int]:
    return {
        "metadata_stale": sum(
            1 for unit in units if unit["classification"] in DRIFT_CLASSIFICATIONS
        ),
        "conflicts": sum(
            1 for unit in units if unit["classification"] == CONFLICT_CLASSIFICATION
        ),
        "unbaselined": sum(
            1
            for unit in units
            if unit["classification"] == UNBASELINED_CLASSIFICATION
        ),
        "failures": sum(
            1 for unit in units if unit["classification"] == FAILURE_CLASSIFICATION
        ),
        "synced": sum(1 for unit in units if unit["classification"] == "IN_SYNC"),
        "total": len(units),
    }


def _append_ledger(
    root: Path,
    consumer: str,
    units: List[Dict[str, Any]],
) -> Optional[str]:
    ledger_path = root / ".pdd" / "drift-ledger.jsonl"
    ledger_path.parent.mkdir(parents=True, exist_ok=True)
    wrote = False
    with ledger_path.open("a", encoding="utf-8") as handle:
        for unit in units:
            if unit["classification"] == "IN_SYNC":
                continue
            entry = {
                "timestamp": datetime.now(timezone.utc).isoformat(),
                "consumer": consumer,
                "basename": unit["basename"],
                "language": unit["language"],
                "classification": unit["classification"],
                "operation": unit["operation"],
                "changed_files": unit.get("changed_files", []),
                "reason": unit.get("reason", ""),
            }
            handle.write(json.dumps(entry, sort_keys=True) + "\n")
            wrote = True
    return str(ledger_path) if wrote else None


def build_report(
    *,
    consumer: str,
    root: Optional[Path] = None,
    modules: Optional[Iterable[str]] = None,
    heal: bool = False,
    ledger: bool = False,
) -> Dict[str, Any]:
    """Build a shared continuous-sync JSON report."""
    if heal:
        raise ValueError(
            "blind fingerprint healing is disabled; use an explicit repair or "
            "reviewed baseline workflow"
        )
    base = project_root(root)
    if canonical_sync_enabled(base):
        if ledger:
            raise ValueError(
                "canonical read-only reporting cannot append a repository ledger"
            )
        return _canonical_compatibility_report(base, consumer, modules)
    units, discovery_failures = _discover_units_and_failures(base, modules=modules)
    classified = [classify_unit(unit, base) for unit in units]
    classified.extend(
        _discovery_failure_payload(failure, base) for failure in discovery_failures
    )
    summary = _build_summary(classified)
    ledger_path = _append_ledger(base, consumer, classified) if ledger else None
    ok = (
        summary["total"] > 0
        and summary["metadata_stale"] == 0
        and summary["conflicts"] == 0
        and summary["unbaselined"] == 0
        and summary["failures"] == 0
    )
    report = {
        "ok": ok,
        "consumer": consumer,
        "project_root": str(base),
        "summary": summary,
        "metadata_stale": summary["metadata_stale"],
        "units": classified,
        "drift": [
            unit
            for unit in classified
            if unit["classification"] in DRIFT_CLASSIFICATIONS
        ],
        "conflicts": [
            unit
            for unit in classified
            if unit["classification"] == CONFLICT_CLASSIFICATION
        ],
        "unbaselined": [
            unit
            for unit in classified
            if unit["classification"] == UNBASELINED_CLASSIFICATION
        ],
        "failures": [
            unit
            for unit in classified
            if unit["classification"] == FAILURE_CLASSIFICATION
        ],
        "healed": [],
    }
    if ledger_path:
        report["ledger_path"] = ledger_path
    return report


def _canonical_compatibility_report(
    root: Path,
    consumer: str,
    modules: Optional[Iterable[str]],
) -> Dict[str, Any]:
    """Project the trusted canonical report into the legacy consumer schema."""
    canonical = build_canonical_report(
        root,
        CanonicalReportOptions(modules=tuple(modules or ())),
    )
    projected = []
    for unit in canonical["units"]:
        baseline = unit["baseline"]
        semantic = unit["semantic"]
        if unit["in_sync"]:
            classification = "IN_SYNC"
        elif baseline == "UNBASELINED":
            classification = UNBASELINED_CLASSIFICATION
        elif semantic == "CONFLICT":
            classification = CONFLICT_CLASSIFICATION
        elif baseline == "DRIFTED":
            classification = "DERIVED_CHANGED"
        else:
            classification = FAILURE_CLASSIFICATION
        projected.append(
            {
                "basename": PurePosixPath(unit["subject"]).relative_to(
                    "prompts"
                ).with_suffix("").as_posix().rsplit("_", 1)[0],
                "language": Path(unit["subject"]).stem.rsplit("_", 1)[-1],
                "classification": classification,
                "operation": "none",
                "reason": unit["reason"],
                "changed_files": unit["changed_roles"],
                "metadata_valid": baseline not in {"UNBASELINED", "CORRUPT"},
                "subject": unit["subject"],
            }
        )
    summary = _build_summary(projected)
    summary["metadata_stale"] = len([
        item for item in projected if item["classification"] in DRIFT_CLASSIFICATIONS
    ])
    summary["conflicts"] = len([
        item for item in projected if item["classification"] == CONFLICT_CLASSIFICATION
    ])
    summary["unbaselined"] = len([
        item for item in projected if item["classification"] == UNBASELINED_CLASSIFICATION
    ])
    summary["failures"] = len([
        item for item in projected if item["classification"] == FAILURE_CLASSIFICATION
    ])
    summary["synced"] = len([
        item for item in projected if item["classification"] == "IN_SYNC"
    ])
    summary["total"] = len(projected)
    return {
        "ok": bool(projected) and all(
            item["classification"] == "IN_SYNC" for item in projected
        ),
        "consumer": consumer,
        "project_root": str(root),
        "summary": summary,
        "metadata_stale": summary["metadata_stale"],
        "units": projected,
        "drift": [
            unit
            for unit in projected
            if unit["classification"] in DRIFT_CLASSIFICATIONS
        ],
        "conflicts": [
            unit
            for unit in projected
            if unit["classification"] == CONFLICT_CLASSIFICATION
        ],
        "unbaselined": [
            unit
            for unit in projected
            if unit["classification"] == UNBASELINED_CLASSIFICATION
        ],
        "failures": [
            unit
            for unit in projected
            if unit["classification"] == FAILURE_CLASSIFICATION
        ],
        "healed": [],
        "canonical": canonical,
    }
