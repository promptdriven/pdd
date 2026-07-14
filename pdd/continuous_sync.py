"""Deterministic continuous-sync classification and reconciliation reports."""
# pylint: disable=too-many-lines
from __future__ import annotations

import json
import os
import stat
import subprocess
from dataclasses import dataclass
from datetime import datetime, timezone
from functools import lru_cache
from pathlib import Path, PurePosixPath
from typing import Any, Dict, Iterable, List, Optional

from .operation_log import (
    _safe_basename,
)
from .sync_determine_operation import (
    Fingerprint,
    _architecture_artifact_paths,
    _expand_output_templates,
    _module_filepath_matches_basename,
    _relative_basename_for_context,
    _resolve_context_name_for_basename,
    calculate_current_hashes,
    calculate_sha256,
    get_extension,
)
from .architecture_registry import extract_modules
from .sync_core import CanonicalReportOptions, build_canonical_report
from .construct_paths import _load_pddrc_config


MAX_PROMPT_DISCOVERY_FILES = 10000
MAX_PROMPT_DISCOVERY_ENTRIES = 50000
MAX_PROMPT_DISCOVERY_ROOTS = 100
MAX_CONFIG_CONTEXTS = 1000
MAX_METADATA_INFERENCE_CANDIDATES = 32
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
    context_name: str | None = None
    pddrc_path: Path | None = None
    config: Dict[str, Any] | None = None


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


def lexical_repository_root(start: Optional[Path] = None) -> Path:
    """Return the Git root enclosing a lexical path without following its leaf."""
    current = Path(os.path.abspath(start or Path.cwd()))
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


def _bounded_prompt_paths(
    prompt_root: Path, budget: Dict[str, int]
) -> tuple[List[Path], Optional[DiscoveryFailure]]:
    prompt_paths: List[Path] = []
    pending = [prompt_root]
    while pending:
        current = pending.pop()
        try:
            entries = os.scandir(current)
            with entries:
                for entry in entries:
                    budget["entries"] += 1
                    if budget["entries"] > MAX_PROMPT_DISCOVERY_ENTRIES:
                        return prompt_paths, DiscoveryFailure(
                            prompt_root=prompt_root,
                            reason=(
                                "configured prompt root exceeded traversal budget "
                                f"of {MAX_PROMPT_DISCOVERY_ENTRIES} directory entries"
                            ),
                            failure="prompt_traversal_budget",
                        )
                    entry_path = current / entry.name
                    try:
                        is_directory = entry.is_dir(follow_symlinks=False)
                    except OSError as exc:
                        raise OSError(f"cannot inspect {entry_path}: {exc}") from exc
                    if is_directory:
                        if not _is_hidden_or_system_dir(entry_path):
                            pending.append(entry_path)
                        continue
                    if not entry.name.endswith(".prompt") or "_" not in entry.name:
                        continue
                    prompt_paths.append(entry_path)
                    budget["files"] += 1
                    if budget["files"] > MAX_PROMPT_DISCOVERY_FILES:
                        return prompt_paths, DiscoveryFailure(
                            prompt_root=prompt_root,
                            reason=(
                                "configured prompt root exceeded traversal budget "
                                f"of {MAX_PROMPT_DISCOVERY_FILES} prompt files"
                            ),
                            failure="prompt_traversal_budget",
                        )
        except OSError as exc:
            return prompt_paths, DiscoveryFailure(
                prompt_root=prompt_root,
                reason=f"configured prompt root traversal failed: {exc}",
                failure="prompt_traversal_error",
            )
    return sorted(prompt_paths), None


def _prompt_units(
    prompt_root: Path, budget: Dict[str, int], identity_roots: List[Path], base: Path,
    config_cache: Dict[Path, Dict[str, Any]],
) -> tuple[List[SyncUnit], List[DiscoveryFailure]]:
    units: List[SyncUnit] = []
    failures: List[DiscoveryFailure] = []
    prompt_paths, failure = _bounded_prompt_paths(prompt_root, budget)
    if failure is not None:
        failures.append(failure)
    for prompt_path in prompt_paths[:MAX_PROMPT_DISCOVERY_FILES]:
        nested_configs = [
            parent / ".pddrc"
            for parent in (prompt_path.parent, *prompt_path.parents)
            if _is_within_root(parent, base) and parent != base
        ]
        unsafe = next(
            (
                path
                for path in nested_configs
                if (path.is_symlink() or path.exists())
                and not _safe_control_file(path, base)
            ),
            None,
        )
        if unsafe is not None:
            failures.append(DiscoveryFailure(unsafe, f"unsafe nested config: {unsafe}", "unsafe_config"))
            continue
        owner = max(
            (root for root in identity_roots if _is_within_root(prompt_path, root)),
            key=lambda root: len(root.parts),
            default=prompt_root,
        )
        stem, separator, language = prompt_path.stem.rpartition("_")
        if not separator or not stem or not language:
            continue
        try:
            basename, context_name, pddrc_path, owner = _prompt_ownership(
                prompt_path, stem, owner, base, config_cache
            )
        except (OSError, RuntimeError, ValueError) as exc:
            failures.append(
                DiscoveryFailure(
                    prompt_path,
                    f"invalid owning config: {exc}",
                    "invalid_pddrc",
                )
            )
            continue
        language = language.lower()
        units.append(
            SyncUnit(
                basename=basename,
                language=language,
                prompt_path=prompt_path,
                prompts_dir=owner,
                context_name=context_name,
                pddrc_path=pddrc_path,
                config=config_cache.get(pddrc_path) if pddrc_path else None,
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


def _safe_control_file(path: Path, base: Path) -> bool:
    """Validate a candidate-controlled file path without following links."""
    return _safe_architecture_candidate(path, base)


def _project_config(base: Path) -> tuple[Path | None, Dict[str, Any]]:
    """Load the project config only after validating its logical path."""
    path = base / ".pddrc"
    if not _safe_control_file(path, base):
        raise UnsafeConfigError(f"unsafe project config: {path}")
    try:
        mode = path.lstat().st_mode
    except FileNotFoundError:
        return None, {}
    if not stat.S_ISREG(mode):
        raise UnsafeConfigError(f"unsafe project config: {path}")
    return path, _load_pddrc_config(path)


def _prompt_ownership(
    prompt_path: Path,
    stem: str,
    fallback_root: Path,
    base: Path,
    config_cache: Dict[Path, Dict[str, Any]] | None = None,
) -> tuple[str, str | None, Path | None, Path]:
    """Return basename and nearest validated config/context ownership."""
    config_candidates = [
        parent / ".pddrc"
        for parent in (prompt_path.parent, *prompt_path.parents)
        if _is_within_root(parent, base)
    ]
    for pddrc_path in config_candidates:
        if not pddrc_path.exists():
            continue
        if not _safe_control_file(pddrc_path, base):
            raise UnsafeConfigError(f"unsafe nested config: {pddrc_path}")
        if config_cache is not None and pddrc_path in config_cache:
            config = config_cache[pddrc_path]
        else:
            config = _load_pddrc_config(pddrc_path)
            if config_cache is not None:
                config_cache[pddrc_path] = config
        contexts = _validate_pddrc_structure(config)
        owned: list[tuple[int, str, Path]] = []
        if isinstance(contexts, dict):
            for context_name, context in contexts.items():
                defaults = context.get("defaults", {})
                # Only an explicit prompts_dir establishes prompt ownership.
                # Treating every unrelated context's missing value as the root
                # ``prompts`` directory creates same-depth ties; tuple ordering
                # then assigns root modules to an arbitrary context (currently
                # ``utils``), misrouting their test/example source sets.
                raw_root = defaults.get("prompts_dir")
                if not isinstance(raw_root, str) or not raw_root.strip():
                    continue
                prompt_root = Path(raw_root).expanduser()
                if not prompt_root.is_absolute():
                    prompt_root = pddrc_path.parent / prompt_root
                prompt_root = prompt_root.resolve(strict=False)
                if _is_safe_prompt_root(base, prompt_root) and _is_within_root(
                    prompt_path, prompt_root
                ):
                    owned.append((len(prompt_root.parts), context_name, prompt_root))
        if owned:
            _depth, context_name, prompt_root = max(owned)
            parent = prompt_path.parent.relative_to(prompt_root)
            basename = (parent / stem).as_posix() if parent.parts else stem
            return basename, context_name, pddrc_path, prompt_root
    parent = prompt_path.parent.relative_to(fallback_root)
    basename = (parent / stem).as_posix() if parent.parts else stem
    return basename, None, None, fallback_root


def _configured_prompt_roots(
    base: Path, pddrc_path: Path | None, config: Dict[str, Any]
) -> List[Path]:
    # pylint: disable=too-many-branches
    """Return normalized prompt roots configured for the legacy report.

    The report owns discovery, so configured roots must be resolved before it
    passes a fixed relative pattern to ``Path.rglob``.  In particular, an
    absolute ``prompts_dir`` is a root, never a glob pattern to append to one.
    """
    configured: List[Path] = []
    if pddrc_path is not None:
        contexts = _validate_pddrc_structure(config)
        for context in contexts.values():
            defaults = context.get("defaults", {})
            raw_root = defaults.get("prompts_dir", "prompts")
            root = Path(raw_root).expanduser()
            if not root.is_absolute():
                root = pddrc_path.parent / root
            configured.append(root.resolve(strict=False))

    if not configured:
        configured.append((base / "prompts").resolve(strict=False))
    unique = sorted(dict.fromkeys(configured), key=lambda item: len(item.parts))
    collapsed: List[Path] = []
    for candidate in unique:
        collapsed.append(candidate)
        if len(collapsed) > MAX_PROMPT_DISCOVERY_ROOTS:
            raise ValueError(
                f".pddrc exceeds configured prompt root limit of {MAX_PROMPT_DISCOVERY_ROOTS}"
            )
    return collapsed


def _validate_pddrc_structure(config: Any) -> Dict[str, Any]:
    """Return strictly validated contexts shared by root and nested configs."""
    if not isinstance(config, dict):
        raise ValueError(".pddrc must contain a mapping")
    contexts = config.get("contexts", {})
    if not isinstance(contexts, dict):
        raise ValueError(".pddrc contexts must contain a mapping")
    if len(contexts) > MAX_CONFIG_CONTEXTS:
        raise ValueError(
            f".pddrc exceeds context limit of {MAX_CONFIG_CONTEXTS}"
        )
    for context_name, context in contexts.items():
        if not isinstance(context_name, str) or not isinstance(context, dict):
            raise ValueError(".pddrc context must contain a mapping")
        defaults = context.get("defaults", {})
        if not isinstance(defaults, dict):
            raise ValueError(".pddrc defaults must contain a mapping")
        raw_root = defaults.get("prompts_dir", "prompts")
        if not isinstance(raw_root, str) or not raw_root.strip():
            raise ValueError(".pddrc prompts_dir must be a non-empty string")
    return contexts


def _validated_prompt_roots(
    base: Path, config_cache: Dict[Path, Dict[str, Any]] | None = None
) -> tuple[List[Path], List[DiscoveryFailure]]:
    roots: List[Path] = []
    failures: List[DiscoveryFailure] = []
    try:
        pddrc_path, config = _project_config(base)
        if pddrc_path is not None and config_cache is not None:
            config_cache[pddrc_path] = config
        configured_roots = _configured_prompt_roots(base, pddrc_path, config)
    except UnsafeConfigError as exc:
        return [], [DiscoveryFailure(base / ".pddrc", str(exc), "unsafe_config")]
    except (OSError, RuntimeError, ValueError) as exc:
        return [], [
            DiscoveryFailure(
                prompt_root=base / ".pddrc",
                reason=f"invalid .pddrc: {exc}",
                failure="invalid_pddrc",
            )
        ]
    for prompt_root in configured_roots:
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

    candidates = [safe_basename.replace("_", "/")]
    for index in range(1, len(parts)):
        candidates.append("_".join(parts[:index]) + "/" + "_".join(parts[index:]))
    return list(dict.fromkeys(candidates))[:MAX_METADATA_INFERENCE_CANDIDATES]


def _validated_artifact_exists(path: Path, base: Path) -> bool:
    """Stat an inferred artifact only after logical containment/link validation."""
    return _safe_architecture_candidate(path, base) and path.exists()


def _existing_artifact_score(
    basename: str,
    language: str,
    prompt_root: Path,
    pddrc_path: Path | None = None,
    config: Dict[str, Any] | None = None,
    budget: Optional[Dict[str, int]] = None,
) -> int:
    try:
        prompt_path = prompt_root / f"{Path(basename).name}_{language}.prompt"
        paths = _resolve_report_paths(
            SyncUnit(
                basename,
                language,
                prompt_path,
                prompt_root,
                pddrc_path=pddrc_path,
                config=config,
            ),
            project_root(prompt_root),
            budget,
        )
    except ValueError:
        return 0
    base = project_root(prompt_root)
    score = 0
    for artifact in ("code", "example", "test"):
        path = paths.get(artifact)
        if path is not None and _validated_artifact_exists(path, base):
            score += 1
    return score


def _infer_basename_from_artifacts(
    safe_basename: str,
    language: str,
    prompt_root: Path,
    budget: Dict[str, int],
    pddrc_path: Path | None = None,
    config: Dict[str, Any] | None = None,
) -> str:
    best = safe_basename
    best_score = _existing_artifact_score(
        best, language, prompt_root, pddrc_path, config, budget
    )
    for candidate in _slash_candidates(safe_basename):
        if budget["entries"] >= MAX_PROMPT_DISCOVERY_ENTRIES:
            break
        budget["entries"] += 1
        score = _existing_artifact_score(
            candidate, language, prompt_root, pddrc_path, config, budget
        )
        if score > best_score:
            best = candidate
            best_score = score
    return best


def _unit_from_metadata_identity(
    identity: tuple[str, str],
    prompt_root: Path,
    prompt_index: Dict[tuple[str, str], SyncUnit],
    requested_basename: Optional[str] = None,
    budget: Optional[Dict[str, int]] = None,
    pddrc_path: Path | None = None,
    config: Dict[str, Any] | None = None,
) -> SyncUnit:
    safe_basename, language = identity
    prompt_unit = prompt_index.get((safe_basename, language))
    if prompt_unit is not None:
        return prompt_unit

    basename = requested_basename or _infer_basename_from_artifacts(
        safe_basename,
        language,
        prompt_root,
        budget or {"entries": 0, "files": 0},
        pddrc_path,
        config,
    )
    prompt_path = _prompt_path_for_basename(prompt_root, basename, language)
    return SyncUnit(
        basename=basename,
        language=language,
        prompt_path=prompt_path,
        prompts_dir=prompt_root,
        pddrc_path=pddrc_path,
        config=config,
    )


def _path_component_violation(path: Path, root: Path, leaf_directory: bool) -> Optional[str]:
    # pylint: disable=too-many-return-statements
    """Return why a project-contained path is unsafe without following symlinks."""
    root_path = root.resolve()
    try:
        parts = path.relative_to(root_path).parts
    except ValueError:
        return "outside_project"
    cursor = root_path
    for index, part in enumerate(parts):
        cursor /= part
        try:
            mode = cursor.lstat().st_mode
        except FileNotFoundError:
            return "missing"
        except OSError:
            return "invalid"
        if stat.S_ISLNK(mode):
            return "symlink"
        is_leaf = index == len(parts) - 1
        if is_leaf:
            expected = stat.S_ISDIR(mode) if leaf_directory else stat.S_ISREG(mode)
        else:
            expected = stat.S_ISDIR(mode)
        if not expected:
            return "nonregular"
    try:
        path.resolve(strict=True).relative_to(root_path)
    except (OSError, ValueError):
        return "outside_project"
    return None


def _metadata_identities(
    meta_root: Path,
    base: Path,
    budget: Dict[str, int],
) -> tuple[List[tuple[str, str]], Optional[DiscoveryFailure]]:
    identities: List[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()
    violation = _path_component_violation(meta_root, base, leaf_directory=True)
    if violation == "missing":
        return identities, None
    if violation is not None:
        return [], DiscoveryFailure(
            prompt_root=meta_root,
            reason=f"unsafe metadata directory: {violation}",
            failure="unsafe_metadata",
        )
    remaining = max(0, MAX_PROMPT_DISCOVERY_ENTRIES - budget["entries"])
    try:
        paths = []
        with os.scandir(meta_root) as entries:
            for entry in entries:
                paths.append(meta_root / entry.name)
                if len(paths) > remaining:
                    break
    except OSError as exc:
        return [], DiscoveryFailure(meta_root, f"metadata traversal failed: {exc}", "metadata_traversal_error")
    exhausted = len(paths) > remaining
    paths = sorted(paths[:remaining])
    for path in paths:
        budget["entries"] += 1
        if budget["entries"] > MAX_PROMPT_DISCOVERY_ENTRIES:
            return identities, DiscoveryFailure(meta_root, "command discovery entry budget exhausted", "discovery_budget")
        if not path.name.endswith(".json") or "_" not in path.stem:
            continue
        identity = _metadata_identity(path)
        if identity is None or identity in seen:
            continue
        seen.add(identity)
        identities.append(identity)
        budget["files"] += 1
        if budget["files"] > MAX_PROMPT_DISCOVERY_FILES:
            return identities[:-1], DiscoveryFailure(meta_root, "command discovery unit budget exhausted", "discovery_budget")
    if exhausted:
        return identities, DiscoveryFailure(
            meta_root,
            "command discovery entry budget exhausted",
            "discovery_budget",
        )
    return identities, None


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
    budget: Dict[str, int],
    pddrc_path: Path | None,
    config: Dict[str, Any] | None,
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
            budget=budget,
            pddrc_path=pddrc_path,
            config=config,
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
    config_cache: Dict[Path, Dict[str, Any]] = {}
    prompt_roots, failures = _validated_prompt_roots(base, config_cache)
    if any(failure.failure == "invalid_pddrc" for failure in failures):
        return [], failures
    prompt_units: List[SyncUnit] = []
    budget = {"entries": 0, "files": 0}
    traversal_roots = [
        root for root in prompt_roots
        if not any(root != other and _is_within_root(root, other) for other in prompt_roots)
    ]
    for prompt_root in traversal_roots:
        if not prompt_root.is_dir():
            continue
        units, unit_failures = _prompt_units(
            prompt_root, budget, prompt_roots, base, config_cache
        )
        prompt_units.extend(units)
        failures.extend(unit_failures)
    metadata_identities, metadata_failure = _metadata_identities(
        base / ".pdd" / "meta", base, budget
    )
    if metadata_failure is not None:
        failures.append(metadata_failure)
        if metadata_failure.failure != "discovery_budget":
            return [], failures

    units = _metadata_units(
        metadata_identities,
        prompt_roots[0] if prompt_roots else base / "prompts",
        _prompt_index(prompt_units),
        wanted,
        budget,
        base / ".pddrc" if base / ".pddrc" in config_cache else None,
        config_cache.get(base / ".pddrc"),
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


def _load_fingerprint_json(
    path: Path,
    root: Path,
) -> tuple[Optional[Dict[str, Any]], Optional[str]]:
    # pylint: disable=too-many-return-statements
    violation = _path_component_violation(path, root, leaf_directory=False)
    if violation == "missing":
        return None, "missing"
    if violation is not None:
        return None, "unsafe_metadata"
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


def _include_dep_violation(dep_path_value: Any, root: Path) -> Optional[Dict[str, str]]:
    # pylint: disable=too-many-return-statements
    if not isinstance(dep_path_value, str) or not dep_path_value.strip():
        return {"path": str(dep_path_value), "reason": "invalid_path"}

    raw_path = Path(dep_path_value)
    dep_path = raw_path if raw_path.is_absolute() else root / raw_path
    dep_path = Path(os.path.abspath(os.path.normpath(os.fspath(dep_path))))
    root_path = root.resolve()
    try:
        common_path = os.path.commonpath([str(root_path), str(dep_path)])
    except ValueError:
        return {"path": dep_path_value, "reason": "outside_project"}
    if common_path != str(root_path):
        return {"path": dep_path_value, "reason": "outside_project"}

    try:
        relative_parts = Path(os.path.relpath(dep_path, root_path)).parts
    except ValueError:
        return {"path": dep_path_value, "reason": "outside_project"}

    cursor = root_path
    for index, part in enumerate(relative_parts):
        cursor = cursor / part
        is_leaf = index == len(relative_parts) - 1
        try:
            dep_stat = cursor.lstat()
        except ValueError:
            return {"path": dep_path_value, "reason": "invalid_path"}
        except OSError:
            return {"path": dep_path_value, "reason": "missing"}
        if stat.S_ISLNK(dep_stat.st_mode):
            return {"path": dep_path_value, "reason": "symlink"}
        if is_leaf:
            if not stat.S_ISREG(dep_stat.st_mode):
                return {"path": dep_path_value, "reason": "nonregular"}
        elif not stat.S_ISDIR(dep_stat.st_mode):
            return {"path": dep_path_value, "reason": "nonregular"}

    return None


def _unsafe_include_deps(
    include_deps: Any,
    root: Path,
) -> List[Dict[str, str]]:
    if include_deps is None:
        return []
    if not isinstance(include_deps, dict):
        return [{"path": str(include_deps), "reason": "invalid_shape"}]
    if not include_deps:
        return []
    violations = []
    for dep_path_value, digest in sorted(
        include_deps.items(), key=lambda item: str(item[0])
    ):
        violation = _include_dep_violation(dep_path_value, root)
        if violation is None and not isinstance(digest, str):
            violation = {"path": str(dep_path_value), "reason": "invalid_digest"}
        if violation is not None:
            violations.append(violation)
    return violations


def _paths_as_json(paths: Dict[str, Any], root: Path) -> Dict[str, Any]:
    payload: Dict[str, Any] = {}
    resolved_root = root.resolve()
    for key, value in paths.items():
        if isinstance(value, Path):
            try:
                payload[key] = value.resolve().relative_to(resolved_root).as_posix()
            except (OSError, RuntimeError, ValueError):
                payload[key] = str(value)
        elif isinstance(value, list):
            payload[key] = [
                _relative_or_raw(item, resolved_root)
                if isinstance(item, Path) else str(item)
                for item in value
            ]
        else:
            payload[key] = str(value)
    return payload


class UnsafeArchitectureError(ValueError):
    """Raised when architecture metadata is unsafe to inspect."""


class UnsafeConfigError(ValueError):
    """Raised when project configuration is unsafe to inspect."""


def _safe_architecture_candidate(path: Path, base: Path) -> bool:
    """Validate a logical architecture path without following symlinks."""
    base = base.resolve()
    candidate = path if path.is_absolute() else base / path
    candidate = Path(os.path.abspath(os.path.normpath(os.fspath(candidate))))
    try:
        parts = candidate.relative_to(base).parts
    except ValueError:
        return False
    cursor = base
    for part in parts:
        cursor /= part
        try:
            mode = cursor.lstat().st_mode
        except FileNotFoundError:
            return True
        except (OSError, ValueError):
            return False
        if stat.S_ISLNK(mode):
            return False
    return True


def _architecture_filepath(
    unit: SyncUnit,
    base: Path,
    context_name: str | None = None,
) -> tuple[Path | None, str | None, Path | None]:
    # pylint: disable=too-many-branches
    """Return an architecture.json filepath match without mutating project state."""
    candidates: list[Path] = []
    for parent in (unit.prompt_path.parent, *unit.prompt_path.parents):
        if not _is_within_root(parent, base):
            break
        candidates.append(parent / "architecture.json")
        if parent == base:
            break
    for architecture_path in dict.fromkeys(candidates):
        if not _safe_architecture_candidate(architecture_path, base):
            raise UnsafeArchitectureError(f"unsafe architecture config: {architecture_path}")
        if not architecture_path.is_file():
            continue
        try:
            payload = json.loads(architecture_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise ValueError(f"architecture config is invalid: {architecture_path}") from exc
        modules = extract_modules(payload)
        exact_matches: list[Path] = []
        leaf_matches: list[Path] = []
        for item in modules:
            if not isinstance(item, dict):
                continue
            filename = item.get("filename")
            filepath = item.get("filepath")
            if not isinstance(filename, str) or not isinstance(filepath, str):
                continue
            filename_path = Path(filename)
            try:
                prompt_relative = unit.prompt_path.relative_to(architecture_path.parent)
            except ValueError:
                prompt_relative = unit.prompt_path
            configured_name = f"{unit.basename}_{unit.language}.prompt".lower()
            is_exact = filename_path.as_posix().lower() in {
                prompt_relative.as_posix().lower(),
                configured_name,
            }
            path_aligned = _module_filepath_matches_basename(
                _module_token_basename(filename, unit.language),
                unit.basename,
                context_name=context_name or unit.context_name,
            )
            flat_basename = len(Path(unit.basename).parts) == 1
            leaf_match = (
                flat_basename
                and filename_path.name.lower() == unit.prompt_path.name.lower()
            )
            if (is_exact and (flat_basename or path_aligned)) or leaf_match:
                output = Path(filepath)
                if output.is_absolute() or ".." in output.parts:
                    raise ValueError(f"architecture output is invalid: {filepath}")
                (exact_matches if is_exact else leaf_matches).append(output)
        matches = exact_matches or leaf_matches
        if len(matches) > 1:
            raise ValueError("ambiguous module configuration")
        if matches:
            matched = matches[0]
            duplicate_leaf = sum(
                1
                for module in modules
                if isinstance(module, dict)
                and isinstance(module.get("filepath"), str)
                and Path(module["filepath"]).stem == matched.stem
            ) > 1
            derived_stem = (
                _safe_basename(matched.with_suffix("").as_posix())
                if duplicate_leaf
                else matched.stem
            )
            return matched, derived_stem, architecture_path.parent
    return None, None, None


def _configured_output_defaults(
    unit: SyncUnit, base: Path
) -> tuple[Dict[str, Any], str | None, Path | None, Dict[str, Any]]:
    """Return complete output defaults for the context owning ``unit``."""
    if unit.pddrc_path is not None:
        if not _safe_control_file(unit.pddrc_path, base):
            raise UnsafeConfigError(f"unsafe unit config: {unit.pddrc_path}")
        pddrc_path = unit.pddrc_path
        config = unit.config if unit.config is not None else _load_pddrc_config(pddrc_path)
    else:
        pddrc_path, config = _project_config(base)
    if pddrc_path is None:
        return {}, None, None, config
    contexts = _validate_pddrc_structure(config)
    context_name = _resolve_context_name_for_basename(
        unit.basename,
        context_override=unit.context_name,
        pddrc_path=pddrc_path,
        config=config,
    )
    if context_name is None:
        stem, separator, language = unit.prompt_path.stem.rpartition("_")
        if separator and stem and language:
            _basename, owned_context, owned_config, _root = _prompt_ownership(
                unit.prompt_path, stem, unit.prompts_dir, base,
                {pddrc_path: config},
            )
            if owned_config == pddrc_path:
                context_name = owned_context
    context = contexts.get(context_name, {}) if context_name else {}
    defaults = context.get("defaults", {}) if isinstance(context, dict) else {}
    if not isinstance(defaults, dict):
        raise ValueError(".pddrc defaults must contain a mapping")
    return defaults, context_name, pddrc_path, config


def _bounded_report_test_files(
    test_path: Path,
    base: Path,
    extension: str,
    budget: Optional[Dict[str, int]],
) -> List[Path]:
    """Discover contained matching tests after validating every path component."""
    if not _safe_architecture_candidate(test_path, base):
        raise ValueError("configured test path is outside project or symlinked")
    parent = test_path.parent
    if not _safe_architecture_candidate(parent, base):
        raise ValueError("configured test directory is outside project or symlinked")
    shared_budget = budget if budget is not None else {}
    matches: List[Path] = []
    try:
        entries = os.scandir(parent)
        with entries:
            for entry in entries:
                shared_budget["report_entries"] = (
                    shared_budget.get("report_entries", 0) + 1
                )
                if shared_budget["report_entries"] > MAX_REPAIR_DISCOVERY_ENTRIES:
                    raise ValueError("report test discovery budget exhausted")
                if not entry.is_file(follow_symlinks=False):
                    continue
                if not entry.name.startswith(test_path.stem):
                    continue
                if Path(entry.name).suffix != f".{extension}":
                    continue
                matches.append(parent / entry.name)
    except FileNotFoundError:
        return [test_path]
    except OSError as exc:
        raise ValueError(f"report test discovery failed: {exc}") from exc
    return sorted(matches) or [test_path]


def _resolve_report_paths(
    unit: SyncUnit,
    base: Path,
    command_budget: Optional[Dict[str, int]] = None,
) -> Dict[str, Any]:
    """Resolve report paths without creating directories or files."""
    extension = get_extension(unit.language)
    suffix = f".{extension}" if extension else ""
    defaults, context_name, pddrc_path, config = _configured_output_defaults(unit, base)
    architecture_filepath, architecture_stem, architecture_root = _architecture_filepath(
        unit, base, context_name
    )
    code_path = architecture_filepath
    architecture_path = code_path
    relative_basename = _relative_basename_for_context(
        unit.basename, context_name, pddrc_path=pddrc_path, config=config
    )
    code_stem = architecture_stem or relative_basename
    code_dir = defaults.get("generate_output_path", "")
    example_dir = defaults.get("example_output_path", "examples")
    test_dir = defaults.get("test_output_path", "tests")
    for value in (code_dir, example_dir, test_dir):
        if not isinstance(value, str):
            raise ValueError("configured output directory must be a string")
    architecture_paths = None
    if code_path is not None:
        architecture_paths = _architecture_artifact_paths(
            architecture_root or base,
            code_path,
            code_stem,
            extension,
            code_dir,
            example_dir,
            test_dir,
        )
        code_path = architecture_paths["code"]
    else:
        code_path = base / code_dir / f"{code_stem}{suffix}"
    artifact_root = architecture_root or base
    example_path = (
        architecture_paths["example"] if architecture_paths is not None
        else artifact_root / example_dir / f"{code_stem}_example{suffix}"
    )
    test_path = (
        architecture_paths["test"] if architecture_paths is not None
        else artifact_root / test_dir / f"test_{code_stem}{suffix}"
    )
    outputs = defaults.get("outputs")
    if isinstance(outputs, dict) and outputs:
        generated = _expand_output_templates(
            relative_basename,
            unit.language,
            extension,
            outputs,
            str(unit.prompt_path),
        )
        for output_name, rendered in generated.items():
            if output_name not in {"prompt", "code", "example", "test"}:
                continue
            raw_config = outputs.get(output_name, {})
            raw_template = (
                raw_config.get("path", "") if isinstance(raw_config, dict) else ""
            )
            if ".." in Path(raw_template).parts:
                raise ValueError(f"configured {output_name} path is outside project")
            candidate = rendered if rendered.is_absolute() else base / rendered
            if not _safe_architecture_candidate(candidate, base):
                raise ValueError(f"configured {output_name} path is outside project")
        if architecture_path is None and "code" in outputs:
            code_path = (
                generated["code"]
                if generated["code"].is_absolute()
                else base / generated["code"]
            )
        if "example" in outputs:
            example_path = (
                generated["example"]
                if generated["example"].is_absolute()
                else base / generated["example"]
            )
        if "test" in outputs:
            test_path = (
                generated["test"]
                if generated["test"].is_absolute()
                else base / generated["test"]
            )
    test_files = [test_path]
    if architecture_paths is not None:
        paths_are_safe = all(
            _safe_architecture_candidate(artifact_path, base)
            for artifact_path in (code_path, example_path, test_path)
        )
        if paths_are_safe:
            test_files = _bounded_report_test_files(
                test_path, base, extension, command_budget
            )
    return {
        "prompt": unit.prompt_path,
        "code": code_path,
        "example": example_path,
        "test": test_path,
        "test_files": test_files,
    }


def _is_within_root(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
        return True
    except ValueError:
        return False


def _artifact_path_violation(path: Path, root: Path) -> Optional[str]:
    # pylint: disable=too-many-return-statements
    root = root.resolve()
    candidate = path if path.is_absolute() else root / path
    normalized = Path(os.path.abspath(os.path.normpath(os.fspath(candidate))))
    try:
        relative_parts = normalized.relative_to(root).parts
    except ValueError:
        return "resolves outside project"
    cursor = root
    for part in relative_parts:
        cursor /= part
        try:
            component_mode = cursor.lstat().st_mode
        except FileNotFoundError:
            break
        except (OSError, RuntimeError, ValueError):
            return "is an invalid path"
        if stat.S_ISLNK(component_mode):
            return "is a symlink" if cursor == normalized else "contains a symlink"
    try:
        mode = candidate.lstat().st_mode
    except FileNotFoundError:
        mode = None
    except (OSError, RuntimeError, ValueError):
        return "is an invalid path"
    if mode is not None and stat.S_ISLNK(mode):
        return "is a symlink"
    try:
        resolved = candidate.resolve(strict=False)
    except (OSError, RuntimeError, ValueError):
        return "is an invalid path"
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


def _unsafe_artifact_result(
    unit: SyncUnit,
    paths: Dict[str, Any],
    root: Path,
    fingerprint_path: Path,
) -> Optional[Dict[str, Any]]:
    """Return a unit failure when any resolved artifact violates project safety."""
    unsafe_artifacts = _unsafe_fingerprinted_artifacts(paths, root)
    if not unsafe_artifacts:
        return None
    changed_files = sorted(key.split(":", 1)[0] for key in unsafe_artifacts)
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
        "fingerprint_path": str(fingerprint_path),
        "paths": _paths_as_json(paths, root),
        "failure": "unsafe_artifacts",
    }


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
    budget: Optional[Dict[str, int]] = None,
) -> tuple[Optional[Path], Optional[DiscoveryFailure]]:
    matches: List[Path] = []
    resolved_root = root.resolve()
    if budget is None:
        budget = {"repair_entries": 0}
    pending = [root]
    while pending:
        current = pending.pop()
        try:
            entries = os.scandir(current)
            with entries:
                for entry in entries:
                    budget["repair_entries"] = budget.get("repair_entries", 0) + 1
                    if budget["repair_entries"] > MAX_REPAIR_DISCOVERY_ENTRIES:
                        return None, DiscoveryFailure(
                            prompt_root=root,
                            reason=(
                                "repair search exceeded traversal budget "
                                f"of {MAX_REPAIR_DISCOVERY_ENTRIES} directory entries"
                            ),
                            failure="repair_traversal_budget",
                        )
                    candidate = current / entry.name
                    try:
                        is_directory = entry.is_dir(follow_symlinks=False)
                    except OSError as exc:
                        raise OSError(f"cannot inspect {candidate}: {exc}") from exc
                    if is_directory:
                        if not _is_hidden_or_system_dir(candidate):
                            pending.append(candidate)
                        continue
                    if entry.name != filename:
                        continue
                    if _artifact_path_violation(candidate, resolved_root):
                        continue
                    if (
                        entry.is_file(follow_symlinks=False)
                        and calculate_sha256(candidate) == expected_hash
                    ):
                        matches.append(candidate)
        except OSError as exc:
            return None, DiscoveryFailure(
                prompt_root=root,
                reason=f"repair search traversal failed: {exc}",
                failure="repair_traversal_error",
            )
    if len(matches) == 1:
        return matches[0], None
    return None, None


def _repair_missing_fingerprinted_paths(
    paths: Dict[str, Path],
    fingerprint: Fingerprint,
    basename: str,
    root: Path,
    budget: Optional[Dict[str, int]] = None,
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
        match, failure = _find_matching_artifact(root, filename, expected_hash, budget)
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


def classify_unit(
    unit: SyncUnit,
    root: Optional[Path] = None,
    command_budget: Optional[Dict[str, int]] = None,
) -> Dict[str, Any]:
    # pylint: disable=broad-exception-caught,too-many-locals,too-many-return-statements
    """Classify one sync unit without mutating files."""
    base = project_root(root)
    # A report must not create `.pdd/meta` just to discover that no fingerprint
    # exists.  The legacy helper creates its parent directory as a write-side
    # convenience, so derive the read-only project-relative location here.
    fp_path = base / ".pdd" / "meta" / f"{_safe_basename(unit.basename)}_{unit.language}.json"
    try:
        paths = _resolve_report_paths(unit, base, command_budget)
    except Exception as exc:  # surfaced in JSON report
        failure = (
            "unsafe_architecture"
            if isinstance(exc, UnsafeArchitectureError)
            else "path_resolution"
        )
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
            "failure": failure,
        }

    unsafe_result = _unsafe_artifact_result(unit, paths, base, fp_path)
    if unsafe_result is not None:
        return unsafe_result

    _raw_fp, raw_error = _load_fingerprint_json(fp_path, base)
    if raw_error == "unsafe_metadata":
        return {
            "basename": unit.basename,
            "language": unit.language,
            "classification": FAILURE_CLASSIFICATION,
            "operation": "none",
            "reason": "unsafe fingerprint metadata path",
            "changed_files": [],
            "metadata_valid": False,
            "fingerprint_path": str(fp_path),
            "paths": _paths_as_json(paths, base),
            "failure": "unsafe_metadata",
        }
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
            command_budget,
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

    unsafe_result = _unsafe_artifact_result(unit, paths, base, fp_path)
    if unsafe_result is not None:
        return unsafe_result

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

    unsafe_include_deps = _unsafe_include_deps(fingerprint.include_deps, base)
    if unsafe_include_deps:
        return {
            "basename": unit.basename,
            "language": unit.language,
            "classification": FAILURE_CLASSIFICATION,
            "operation": "none",
            "reason": "unsafe legacy include dependency metadata",
            "changed_files": [],
            "metadata_valid": False,
            "fingerprint_path": str(fp_path),
            "paths": _paths_as_json(paths, base),
            "failure": "unsafe_include_deps",
            "unsafe_include_deps": unsafe_include_deps,
        }

    try:
        current_hashes = calculate_current_hashes(
            paths,
            stored_include_deps=fingerprint.include_deps,
            dependency_root=base,
        )
    except Exception as exc:  # surfaced as a unit-scoped machine-readable failure
        return {
            "basename": unit.basename,
            "language": unit.language,
            "classification": FAILURE_CLASSIFICATION,
            "operation": "none",
            "reason": f"fingerprint hash calculation failed: {exc}",
            "changed_files": [],
            "metadata_valid": False,
            "fingerprint_path": str(fp_path),
            "paths": _paths_as_json(paths, base),
            "failure": "hash_calculation",
        }
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
    command_budget = {"repair_entries": 0}
    classified = [classify_unit(unit, base, command_budget) for unit in units]
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
