"""Deterministic continuous-sync classification and reconciliation (shared core).

This is the single implementation behind two surfaces:

* ``pdd reconcile`` (``pdd/commands/reconcile.py``) — classify drift and, for the
  safe cases, stamp ``.pdd/meta`` fingerprints to the current tree.
* ``scripts/stamp_fingerprints.py`` — the CI stamper/verifier, now a thin wrapper
  over this module (issue #1927: no second hashing implementation).

Unit/path resolution follows the repo's prompt tree and ``architecture.json``:
every ``pdd/prompts/[sub/]<leaf>_python.prompt`` is one unit whose basename keeps
its subdirectory (``commands/firecrawl``, not the flattened ``commands_firecrawl``),
and whose code path honours an ``architecture.json`` ``filepath`` override, else the
``pdd/<basename>.py`` convention. Each unit maps to its own
``.pdd/meta/<safe_basename>_python.json`` fingerprint. Hashing uses pdd's real
functions (``sync_determine_operation.calculate_current_hashes`` /
``operation_log.save_fingerprint``) so a reconcile stamp is byte-identical to what
``pdd sync`` would write. Zero LLM calls, no code/test regeneration.

Classification vocabulary (unchanged from #1954, the CONFLICT definition is shared
with the sync decision path in ``sync_determine_operation``): a unit is IN_SYNC,
one of the single-sided drift states (DOC/PROMPT/CODE/TEST/EXAMPLE/DERIVED_CHANGED),
CONFLICT (prompt-side *and* code/derived-side both moved vs the stored meta),
UNBASELINED (missing / structurally invalid fingerprint) or FAILURE (resolution
error). Machine-readable verdicts additionally carry the issue #884 shape
(``status`` / ``reasons`` / ``affected_artifacts`` / ``remediation``).
"""
# pylint: disable=too-many-lines
from __future__ import annotations

import contextlib
import fnmatch
import glob
import json
import os
import subprocess
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

from .operation_log import _safe_basename, save_fingerprint
from .sync_determine_operation import (
    Fingerprint,
    calculate_current_hashes,
    read_fingerprint,
)

# --- Constants ---------------------------------------------------------------

LANGUAGE = "python"
PROMPT_SUFFIX = f"_{LANGUAGE}.prompt"

# Hash fields compared to decide currency (metadata fields pdd_version /
# timestamp / command are not content-derived and are never compared).
HASH_FIELDS: Tuple[str, ...] = (
    "prompt_hash",
    "code_hash",
    "example_hash",
    "test_hash",
    "test_files",
    "include_deps",
)

# Fingerprint dataclass field order (mirrors sync_determine_operation.Fingerprint /
# operation_log.save_fingerprint's asdict(...) json.dump order). Re-exported for the
# stamper wrapper's byte-format test.
FIELD_ORDER: Tuple[str, ...] = (
    "pdd_version",
    "timestamp",
    "command",
    "prompt_hash",
    "code_hash",
    "example_hash",
    "test_hash",
    "test_files",
    "include_deps",
)

# ``command`` recorded when a unit is stamped for the first time (backfill). 'fix'
# satisfies sync's completion gates and triggers none of its special branches; it
# is the modal command among committed fingerprints.
NEW_UNIT_COMMAND = "fix"

IN_SYNC_CLASSIFICATION = "IN_SYNC"
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

# Issue #884 coarse verdict statuses (status / reasons / affected_artifacts /
# remediation is the report shape the drift classifier converges on).
STATUS_CURRENT = "current"
STATUS_STALE = "stale"
STATUS_STAMPED = "stamped"
STATUS_CONFLICT = "conflict"
STATUS_UNBASELINED = "unbaselined"
STATUS_FAILURE = "failure"


def _norm(value: Any) -> Any:
    """Normalise empty containers / falsey hashes to ``None`` for comparison.

    Mirrors the stamper's ``(x or None)`` currency check so an absent artifact
    (``None``) and an empty ``{}`` map compare equal.
    """
    return value or None


# --- Project root ------------------------------------------------------------


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


@contextlib.contextmanager
def _chdir(root: Path):
    """Run with ``cwd == root`` so <include> resolution + dep keys are repo-relative.

    pdd's ``calculate_prompt_hash`` resolves <include> refs against ``Path.cwd()``
    and stores ``include_deps`` keys relative to it; the committed fingerprints use
    repo-relative keys, so hashing must run from the project root to match.
    """
    prev = Path.cwd()
    os.chdir(root)
    try:
        yield
    finally:
        os.chdir(prev)


# --- Repo layout -------------------------------------------------------------


@dataclass(frozen=True)
class _Layout:  # pylint: disable=too-many-instance-attributes
    """Resolved repo paths a reconcile run operates on."""

    root: Path
    prompts_root: Path
    meta_dir: Path
    context_root: Path
    tests_root: Path
    code_root: Path
    architecture_file: Path
    waivers_file: Path


def _layout_for(root: Path) -> _Layout:
    """Derive the repo layout from ``root`` (the PDD project root).

    Prompts live under ``pdd/prompts`` in a PDD-managed repo; a ``prompts``
    symlink/dir at the root (the repo's ``prompts -> pdd/prompts`` shim, or a
    consumer whose prompts sit at the top level) is accepted as a fallback.
    """
    root = root.resolve()
    prompts_root = root / "pdd" / "prompts"
    if not prompts_root.exists() and (root / "prompts").exists():
        prompts_root = root / "prompts"
    return _Layout(
        root=root,
        prompts_root=prompts_root,
        meta_dir=root / ".pdd" / "meta",
        context_root=root / "context",
        tests_root=root / "tests",
        code_root=root / "pdd",
        architecture_file=root / "architecture.json",
        waivers_file=root / "scripts" / "fingerprint_waivers.json",
    )


# --- architecture.json resolution --------------------------------------------
# pdd's get_pdd_file_paths consults architecture.json FIRST for a module's code
# filepath (issue #225) and disambiguates the example/test stem for a bare leaf
# that maps to more than one module (issue #1677). Both are pure JSON+path logic;
# they are mirrored here (matching scripts/stamp_fingerprints.py byte-for-byte)
# because get_pdd_file_paths otherwise flattens a subdir'd basename without an
# architecture entry (commands/firecrawl -> pdd/firecrawl.py instead of the real
# pdd/commands/firecrawl.py).

_ArchMaps = Tuple[Dict[str, set], Dict[str, set], frozenset]
_ARCH_CACHE: Dict[Path, _ArchMaps] = {}


def _load_architecture(architecture_file: Path) -> _ArchMaps:
    """Return ``(by_filename, by_leaf, ambiguous_leaves)`` from architecture.json."""
    cached = _ARCH_CACHE.get(architecture_file)
    if cached is not None:
        return cached
    by_filename: Dict[str, set] = {}
    by_leaf: Dict[str, set] = {}
    if not architecture_file.is_file():
        result: _ArchMaps = (by_filename, by_leaf, frozenset())
        _ARCH_CACHE[architecture_file] = result
        return result
    try:
        data = json.loads(architecture_file.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        result = (by_filename, by_leaf, frozenset())
        _ARCH_CACHE[architecture_file] = result
        return result
    if isinstance(data, list):
        modules = data
    elif isinstance(data, dict):
        modules = data.get("modules", [])
    else:
        modules = []
    for module in modules:
        if not isinstance(module, dict):
            continue
        filename = str(module.get("filename") or "").strip()
        filepath = str(module.get("filepath") or "").strip()
        if not filename or not filepath or filename.endswith("_LLM.prompt"):
            continue
        fp = Path(filepath).as_posix()
        by_filename.setdefault(filename.lower(), set()).add(fp)
        by_leaf.setdefault(Path(filename).name.lower(), set()).add(fp)
    ambiguous = frozenset(
        leaf[: -len(f"_{LANGUAGE}.prompt")]
        for leaf, fps in by_leaf.items()
        if leaf.endswith(f"_{LANGUAGE}.prompt") and len(fps) > 1
    )
    result = (by_filename, by_leaf, ambiguous)
    _ARCH_CACHE[architecture_file] = result
    return result


def _resolve_code_and_stem(
    basename: str, layout: _Layout, arch_maps: _ArchMaps
) -> Tuple[Path, str]:
    """Return ``(code_path, artifact_stem)`` mirroring pdd's resolution.

    ``code_path`` is the architecture.json filepath when the prompt is listed
    there, else ``pdd/<basename>.py`` (subdirectory preserved). ``artifact_stem``
    is the example/test stem: the code file's stem, replaced by a disambiguated
    ``_safe_basename(<filepath sans suffix>)`` when the bare leaf is ambiguous.
    """
    by_filename, by_leaf, ambiguous = arch_maps
    leaf = basename.rsplit("/", 1)[-1]
    pf_full = f"{basename}_{LANGUAGE}.prompt".lower()
    pf_leaf = f"{leaf}_{LANGUAGE}.prompt".lower()

    arch_fp: Optional[str] = None
    full_fps = by_filename.get(pf_full)
    if full_fps and len(full_fps) == 1:
        arch_fp = next(iter(full_fps))
    if arch_fp is None:
        leaf_fps = by_leaf.get(pf_leaf, set())
        if len(leaf_fps) == 1:
            arch_fp = next(iter(leaf_fps))
        elif len(leaf_fps) > 1:
            aligned = [
                fp
                for fp in leaf_fps
                if Path(fp).with_suffix("").as_posix().endswith(basename)
            ]
            if len(aligned) == 1:
                arch_fp = aligned[0]

    if arch_fp:
        code = layout.root / arch_fp
        if leaf in ambiguous:
            stem = _safe_basename(Path(arch_fp).with_suffix("").as_posix())
        else:
            stem = Path(arch_fp).stem
    else:
        code = layout.code_root / f"{basename}.py"
        stem = leaf
    return code, stem


# --- Unit enumeration & path resolution --------------------------------------


@dataclass(frozen=True)
class Unit:  # pylint: disable=too-many-instance-attributes
    """A single PDD dev unit resolved from a ``*_python.prompt`` file."""

    basename: str
    language: str
    prompt: Path
    code: Path
    example: Path
    test: Path
    test_files: Tuple[Path, ...]
    meta: Path


def _discover_test_files(test_dir: Path, stem: str) -> List[Path]:
    """Mirror pdd's Bug #156 globbing: sorted ``test_<stem>*.py`` in ``test_dir``."""
    primary = test_dir / f"test_{stem}.py"
    if test_dir.is_dir():
        pattern = glob.escape(f"test_{stem}")
        matches = sorted(test_dir.glob(f"{pattern}*.py"))
    else:
        matches = [primary] if primary.exists() else []
    return matches or [primary]


def _build_unit(basename: str, prompt: Path, layout: _Layout, arch_maps: _ArchMaps) -> Unit:
    """Resolve every artifact path for ``basename`` (stamper-parity resolution)."""
    subdir = str(Path(basename).parent) if "/" in basename else ""
    code, stem = _resolve_code_and_stem(basename, layout, arch_maps)
    example_dir = layout.context_root / subdir if subdir else layout.context_root
    test_dir = layout.tests_root / subdir if subdir else layout.tests_root
    return Unit(
        basename=basename,
        language=LANGUAGE,
        prompt=prompt,
        code=code,
        example=example_dir / f"{stem}_example.py",
        test=test_dir / f"test_{stem}.py",
        test_files=tuple(_discover_test_files(test_dir, stem)),
        meta=layout.meta_dir / f"{_safe_basename(basename)}_{LANGUAGE}.json",
    )


def infer_basename(prompt_path: Path, prompts_root: Path) -> Optional[str]:
    """Return the unit basename for a ``*_python.prompt`` file, or None.

    Basename is the path relative to ``prompts_root`` with the ``_python.prompt``
    suffix dropped and subdirectories preserved (e.g. ``commands/which``).
    """
    name = prompt_path.name
    if not name.endswith(PROMPT_SUFFIX):
        return None
    try:
        rel = prompt_path.relative_to(prompts_root)
    except ValueError:
        return None
    stem = rel.name[: -len(PROMPT_SUFFIX)]
    subdir = rel.parent
    if str(subdir) == ".":
        return stem
    return (subdir / stem).as_posix()


def enumerate_units(
    layout: _Layout,
    arch_maps: _ArchMaps,
    modules: Optional[Iterable[str]] = None,
) -> List[Unit]:
    """Return every python unit under the prompts root, sorted by basename.

    ``modules`` (a set of basenames, safe-basenames or prompt stems) filters the
    result; ``None`` returns all units.
    """
    wanted = set(modules or [])
    units: List[Unit] = []
    if not layout.prompts_root.exists():
        return units
    for prompt in sorted(layout.prompts_root.rglob(f"*{PROMPT_SUFFIX}")):
        basename = infer_basename(prompt, layout.prompts_root)
        if basename is None:
            continue
        if wanted and not _unit_wanted(basename, prompt, wanted):
            continue
        units.append(_build_unit(basename, prompt, layout, arch_maps))
    return units


def _unit_wanted(basename: str, prompt: Path, wanted: set) -> bool:
    """Match a unit against ``--module`` / ``[BASENAME]`` selectors."""
    return (
        basename in wanted
        or _safe_basename(basename) in wanted
        or prompt.stem in wanted
        or basename.rsplit("/", 1)[-1] in wanted
    )


def resolve_units(
    root: Path, modules: Optional[Iterable[str]] = None
) -> List[Unit]:
    """Public: resolve every python unit under ``root`` (stamper-parity paths)."""
    layout = _layout_for(Path(root))
    arch_maps = _load_architecture(layout.architecture_file)
    return enumerate_units(layout, arch_maps, modules=modules)


def resolve_unit(basename: str, root: Path, prompt: Optional[Path] = None) -> Unit:
    """Public: resolve one unit's artifact paths against ``root``.

    ``prompt`` defaults to ``<prompts_root>/<basename>_python.prompt``.
    """
    layout = _layout_for(Path(root))
    arch_maps = _load_architecture(layout.architecture_file)
    if prompt is None:
        prompt = layout.prompts_root / f"{basename}{PROMPT_SUFFIX}"
    return _build_unit(basename, Path(prompt), layout, arch_maps)


# --- .pddignore & waivers ----------------------------------------------------


def load_pddignore(root: Path) -> List[str]:
    """Load ``.pddignore`` patterns from ``root`` (comments/blank stripped)."""
    path = root / ".pddignore"
    patterns: List[str] = []
    if not path.is_file():
        return patterns
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        patterns.append(line)
    return patterns


def is_pddignored(code_path: Path, patterns: List[str], root: Path) -> bool:
    """Mirror update_main._is_pddignored against the repo-relative code path."""
    try:
        rel_path = code_path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return False
    basename = code_path.name
    for pat in patterns:
        if pat.endswith("/"):
            dir_name = pat.rstrip("/")
            parts = rel_path.split("/")
            if dir_name in parts[:-1]:
                return True
        else:
            if fnmatch.fnmatch(rel_path, pat):
                return True
            if fnmatch.fnmatch(basename, pat):
                return True
    return False


def load_waivers(waivers_file: Path) -> Dict[str, str]:
    """Return ``{basename: reason}`` from the committed waiver file."""
    if not waivers_file.is_file():
        return {}
    try:
        data = json.loads(waivers_file.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    waivers: Dict[str, str] = {}
    for entry in data.get("waivers", []):
        if isinstance(entry, dict) and entry.get("basename"):
            waivers[entry["basename"]] = entry.get("reason", "")
    return waivers


def partition_units(
    units: List[Unit], pddignore: List[str], waivers: Dict[str, str], root: Path
) -> Tuple[List[Unit], List[Unit], List[Unit], List[Unit]]:
    """Split units into ``(stampable, ignored, waived, no_code)`` buckets.

    * ignored: code path matches ``.pddignore`` (pdd never tracks these).
    * waived: basename appears in the committed waiver file.
    * no_code: code file absent and not waived (nothing to hash).
    * stampable: everything else.
    """
    stampable: List[Unit] = []
    ignored: List[Unit] = []
    waived: List[Unit] = []
    no_code: List[Unit] = []
    for unit in units:
        if is_pddignored(unit.code, pddignore, root):
            ignored.append(unit)
        elif unit.basename in waivers:
            waived.append(unit)
        elif not unit.code.exists():
            no_code.append(unit)
        else:
            stampable.append(unit)
    return stampable, ignored, waived, no_code


# --- Hashing (pdd's real functions) ------------------------------------------


def _paths_for_hashing(unit: Unit) -> Dict[str, Any]:
    """Build the ``paths`` dict pdd's ``calculate_current_hashes`` expects."""
    return {
        "prompt": unit.prompt,
        "code": unit.code,
        "example": unit.example,
        "test": unit.test,
        "test_files": list(unit.test_files),
    }


def compute_current_hashes(
    unit: Unit, stored_deps: Optional[Dict[str, str]] = None
) -> Dict[str, Any]:
    """Recompute all fingerprint hash fields for ``unit`` via pdd's real hasher.

    Must run under ``_chdir(root)`` so <include> resolution matches the committed
    fingerprints (see the public ``hashes_for`` for a self-contained variant).
    """
    return calculate_current_hashes(
        _paths_for_hashing(unit), stored_include_deps=stored_deps
    )


def hashes_for(
    unit: Unit, root: Path, stored_deps: Optional[Dict[str, str]] = None
) -> Dict[str, Any]:
    """Public: recompute ``unit``'s hashes with cwd anchored at ``root``."""
    with _chdir(Path(root)):
        return compute_current_hashes(unit, stored_deps)


def _read_fingerprint_obj(unit: Unit) -> Optional[Fingerprint]:
    """Read ``unit``'s committed fingerprint, or None if missing/invalid.

    ``get_fingerprint_path(basename, paths=...)`` resolves to ``unit.meta`` (pinned
    by the resolution parity check), so read_fingerprint reads the same file the
    stamper writes.
    """
    return read_fingerprint(unit.basename, unit.language, paths=_paths_for_hashing(unit))


def _load_fingerprint_json(path: Path) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    """Return ``(data, error)`` distinguishing a missing vs unparseable meta."""
    if not path.exists():
        return None, "missing"
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None, "invalid"
    if not isinstance(data, dict):
        return None, "invalid"
    return data, None


def _hashes_equal(stored: Fingerprint, current: Dict[str, Any]) -> bool:
    """True iff every content hash field matches (the currency test)."""
    return all(
        _norm(getattr(stored, field_name, None)) == _norm(current.get(field_name))
        for field_name in HASH_FIELDS
    )


# --- Classification ----------------------------------------------------------


def _changed_artifacts(
    fingerprint: Fingerprint, paths: Dict[str, Any], current_hashes: Dict[str, Any]
) -> List[str]:
    """Return the changed artifact labels (doc/prompt/code/example/test)."""
    changes: List[str] = []
    if _norm(current_hashes.get("prompt_hash")) != _norm(fingerprint.prompt_hash):
        if _norm(current_hashes.get("include_deps")) != _norm(fingerprint.include_deps):
            changes.append("doc")
        else:
            changes.append("prompt")
    if (
        paths.get("code")
        and paths["code"].exists()
        and _norm(current_hashes.get("code_hash")) != _norm(fingerprint.code_hash)
    ):
        changes.append("code")
    if (
        paths.get("example")
        and paths["example"].exists()
        and _norm(current_hashes.get("example_hash")) != _norm(fingerprint.example_hash)
    ):
        changes.append("example")
    if (
        paths.get("test")
        and paths["test"].exists()
        and _norm(current_hashes.get("test_hash")) != _norm(fingerprint.test_hash)
    ):
        changes.append("test")
    return changes


def _classification_for_changes(changes: List[str]) -> str:
    """Map changed artifacts to a classification.

    CONFLICT is prompt-side (prompt/doc) AND code/derived-side both moved — the
    same definition the sync decision path uses (issue #1929 owns that path; this
    keeps the two aligned).
    """
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
    return IN_SYNC_CLASSIFICATION


def _operation_for(classification: str, changes: List[str]) -> str:
    """Map a classification to the pdd operation that would resolve it."""
    mapping = {
        IN_SYNC_CLASSIFICATION: "nothing",
        "DOC_CHANGED": "reconcile",
        "PROMPT_CHANGED": "generate",
        "CODE_CHANGED": "update",
        "TEST_CHANGED": "test",
        "EXAMPLE_CHANGED": "verify",
        CONFLICT_CLASSIFICATION: "conflict",
        UNBASELINED_CLASSIFICATION: "none",
        FAILURE_CLASSIFICATION: "none",
    }
    if classification in mapping:
        return mapping[classification]
    if "code" in changes or "example" in changes:
        return "verify"
    if "test" in changes:
        return "test"
    return "reconcile"


def _status_for(classification: str) -> str:
    """Map a classification to the coarse issue #884 status."""
    if classification == IN_SYNC_CLASSIFICATION:
        return STATUS_CURRENT
    if classification in DRIFT_CLASSIFICATIONS:
        return STATUS_STALE
    if classification == CONFLICT_CLASSIFICATION:
        return STATUS_CONFLICT
    if classification == UNBASELINED_CLASSIFICATION:
        return STATUS_UNBASELINED
    return STATUS_FAILURE


def _remediation_for(basename: str, classification: str) -> str:
    """Suggested next command for a non-current unit."""
    if classification in (IN_SYNC_CLASSIFICATION, FAILURE_CLASSIFICATION):
        return ""
    if classification == "PROMPT_CHANGED":
        return f"pdd sync {basename}"
    if classification == "CODE_CHANGED":
        return f"pdd update {basename}"
    if classification == CONFLICT_CLASSIFICATION:
        return f"pdd reconcile {basename} --accept-current  # or resolve the conflict"
    if classification == UNBASELINED_CLASSIFICATION:
        return f"pdd reconcile {basename} --backfill"
    # DOC/TEST/EXAMPLE/DERIVED — a plain reconcile stamp is the fix.
    return f"pdd reconcile {basename}"


def _rel(path: Path, root: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except (OSError, ValueError):
        return str(path)


def _verdict(
    unit: Unit,
    layout: _Layout,
    *,
    classification: str,
    changes: List[str],
    reason: str,
    metadata_valid: bool,
    current_hashes: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    # pylint: disable=too-many-arguments
    """Assemble one unit's report entry (legacy fields + issue #884 shape)."""
    entry: Dict[str, Any] = {
        "basename": unit.basename,
        "language": unit.language,
        "classification": classification,
        "status": _status_for(classification),
        "operation": _operation_for(classification, changes),
        "reason": reason,
        "reasons": [reason] if reason else [],
        "changed_files": changes,
        "affected_artifacts": changes,
        "remediation": _remediation_for(unit.basename, classification),
        "metadata_valid": metadata_valid,
        "fingerprint_path": _rel(unit.meta, layout.root),
        "paths": {
            "prompt": _rel(unit.prompt, layout.root),
            "code": _rel(unit.code, layout.root),
            "example": _rel(unit.example, layout.root),
            "test": _rel(unit.test, layout.root),
            "test_files": [_rel(p, layout.root) for p in unit.test_files],
        },
    }
    if current_hashes is not None:
        entry["hashes"] = {
            "prompt_hash": current_hashes.get("prompt_hash"),
            "code_hash": current_hashes.get("code_hash"),
            "example_hash": current_hashes.get("example_hash"),
            "test_hash": current_hashes.get("test_hash"),
        }
    return entry


def classify_unit(unit: Unit, layout: _Layout) -> Dict[str, Any]:
    """Classify one unit without mutating files. Runs under ``_chdir(root)``."""
    _raw, raw_error = _load_fingerprint_json(unit.meta)
    if raw_error is not None:
        return _verdict(
            unit,
            layout,
            classification=UNBASELINED_CLASSIFICATION,
            changes=[],
            reason=f"fingerprint {raw_error}",
            metadata_valid=False,
        )
    fingerprint = _read_fingerprint_obj(unit)
    if fingerprint is None:
        return _verdict(
            unit,
            layout,
            classification=UNBASELINED_CLASSIFICATION,
            changes=[],
            reason="fingerprint invalid",
            metadata_valid=False,
        )
    current = compute_current_hashes(unit, fingerprint.include_deps)
    changes = _changed_artifacts(fingerprint, _paths_for_hashing(unit), current)
    classification = _classification_for_changes(changes)
    reason = (
        "all hashes match fingerprint"
        if classification == IN_SYNC_CLASSIFICATION
        else f"{', '.join(changes)} changed since fingerprint"
    )
    return _verdict(
        unit,
        layout,
        classification=classification,
        changes=changes,
        reason=reason,
        metadata_valid=True,
        current_hashes=current,
    )


# --- Stamping (idempotent, byte-identical to pdd sync) -----------------------


def stamp_unit(unit: Unit) -> bool:
    """Stamp ``unit``'s fingerprint to the current tree iff its hashes changed.

    Idempotent by construction: a unit whose content hashes already match the
    stored fingerprint is NOT rewritten (its timestamp is preserved and no file is
    written), so a second consecutive run is a no-op and unchanged units never
    churn (issue #1932 / pdd_cloud restamp-churn addendum). Returns True iff a
    file was written. Must run under ``_chdir(root)``.
    """
    stored = _read_fingerprint_obj(unit)
    current = compute_current_hashes(
        unit, stored.include_deps if stored is not None else None
    )
    if stored is not None and _hashes_equal(stored, current):
        return False
    command = NEW_UNIT_COMMAND
    if stored is not None and stored.command:
        command = stored.command
    save_fingerprint(unit.basename, unit.language, command, paths=_paths_for_hashing(unit))
    return True


def stamp_units(units: Iterable[Unit], root: Path) -> List[str]:
    """Public: idempotently stamp each unit with cwd anchored at ``root``.

    Returns the basenames actually written (unchanged units are skipped).
    """
    written: List[str] = []
    with _chdir(Path(root)):
        for unit in units:
            if stamp_unit(unit):
                written.append(unit.basename)
    return written


# --- Reporting ---------------------------------------------------------------


def _build_summary(units: List[Dict[str, Any]]) -> Dict[str, int]:
    return {
        "metadata_stale": sum(
            1 for u in units if u["classification"] in DRIFT_CLASSIFICATIONS
        ),
        "conflicts": sum(
            1 for u in units if u["classification"] == CONFLICT_CLASSIFICATION
        ),
        "unbaselined": sum(
            1 for u in units if u["classification"] == UNBASELINED_CLASSIFICATION
        ),
        "failures": sum(
            1 for u in units if u["classification"] == FAILURE_CLASSIFICATION
        ),
        "synced": sum(1 for u in units if u["classification"] == IN_SYNC_CLASSIFICATION),
        "stamped": sum(1 for u in units if u.get("status") == STATUS_STAMPED),
        "total": len(units),
    }


def _append_ledger(root: Path, consumer: str, units: List[Dict[str, Any]]) -> Optional[str]:
    ledger_path = root / ".pdd" / "drift-ledger.jsonl"
    ledger_path.parent.mkdir(parents=True, exist_ok=True)
    wrote = False
    with ledger_path.open("a", encoding="utf-8") as handle:
        for unit in units:
            if unit["classification"] == IN_SYNC_CLASSIFICATION:
                continue
            entry = {
                "timestamp": datetime.now(timezone.utc).isoformat(),
                "consumer": consumer,
                "basename": unit["basename"],
                "language": unit["language"],
                "classification": unit["classification"],
                "status": unit.get("status"),
                "operation": unit["operation"],
                "changed_files": unit.get("changed_files", []),
                "reason": unit.get("reason", ""),
            }
            handle.write(json.dumps(entry, sort_keys=True) + "\n")
            wrote = True
    return str(ledger_path) if wrote else None


def _stampable_now(
    classification: str, *, heal: bool, accept_current: bool, backfill: bool
) -> bool:
    """Should a unit with this classification be stamped this run?

    ``heal`` stamps single-sided drift (the safe cases). CONFLICT (both sides
    moved) is stamped only with an explicit ``--accept-current`` (the human
    declares the current tree the agreed state); UNBASELINED only with
    ``--backfill``. Each flag is scoped to exactly its class.
    """
    if classification in DRIFT_CLASSIFICATIONS:
        return heal
    if classification == CONFLICT_CLASSIFICATION:
        return accept_current
    if classification == UNBASELINED_CLASSIFICATION:
        return backfill
    return False


def build_report(
    *,
    consumer: str,
    root: Optional[Path] = None,
    modules: Optional[Iterable[str]] = None,
    heal: bool = False,
    ledger: bool = False,
    accept_current: bool = False,
    backfill: bool = False,
) -> Dict[str, Any]:
    # pylint: disable=too-many-arguments,too-many-locals
    """Build the shared continuous-sync report, optionally stamping safe cases.

    ``heal`` stamps single-sided drift; ``accept_current`` additionally stamps
    CONFLICT units; ``backfill`` additionally stamps UNBASELINED units. Stamping
    is idempotent and re-classifies afterwards so the reported status reflects the
    post-stamp tree (a stamped unit becomes ``current`` with ``status=stamped``).
    """
    base = project_root(root)
    layout = _layout_for(base)
    arch_maps = _load_architecture(layout.architecture_file)
    units = enumerate_units(layout, arch_maps, modules=modules)
    pddignore = load_pddignore(layout.root)
    waivers = load_waivers(layout.waivers_file)
    stampable, _ignored, _waived, _no_code = partition_units(
        units, pddignore, waivers, layout.root
    )

    do_stamp = heal or accept_current or backfill
    stamped: List[str] = []
    with _chdir(layout.root):
        classified = [classify_unit(u, layout) for u in stampable]
        if do_stamp:
            by_name = {u.basename: u for u in stampable}
            for entry in classified:
                if _stampable_now(
                    entry["classification"],
                    heal=heal,
                    accept_current=accept_current,
                    backfill=backfill,
                ):
                    unit = by_name.get(entry["basename"])
                    if unit is not None and stamp_unit(unit):
                        stamped.append(unit.basename)
            if stamped:
                stamped_set = set(stamped)
                classified = [classify_unit(u, layout) for u in stampable]
                for entry in classified:
                    if entry["basename"] in stamped_set:
                        entry["status"] = STATUS_STAMPED

    summary = _build_summary(classified)
    ledger_path = _append_ledger(layout.root, consumer, classified) if ledger else None
    ok = (
        summary["metadata_stale"] == 0
        and summary["conflicts"] == 0
        and summary["unbaselined"] == 0
        and summary["failures"] == 0
    )
    report: Dict[str, Any] = {
        "ok": ok,
        "consumer": consumer,
        "project_root": str(layout.root),
        "summary": summary,
        "metadata_stale": summary["metadata_stale"],
        "units": classified,
        "drift": [u for u in classified if u["classification"] in DRIFT_CLASSIFICATIONS],
        "conflicts": [
            u for u in classified if u["classification"] == CONFLICT_CLASSIFICATION
        ],
        "unbaselined": [
            u for u in classified if u["classification"] == UNBASELINED_CLASSIFICATION
        ],
        "failures": [
            u for u in classified if u["classification"] == FAILURE_CLASSIFICATION
        ],
        "healed": stamped,
        "stamped": stamped,
    }
    if ledger_path:
        report["ledger_path"] = ledger_path
    return report


# --- Verification (--check) --------------------------------------------------


@dataclass
class CheckResult:
    """Outcome of a read-only ``--check`` verification."""

    ok: bool
    stampable: int
    ignored: int
    waived: int
    missing: List[str] = field(default_factory=list)
    stale: List[Tuple[str, List[str]]] = field(default_factory=list)
    no_code: List[str] = field(default_factory=list)


def run_check(
    root: Optional[Path] = None, modules: Optional[Iterable[str]] = None
) -> CheckResult:
    # pylint: disable=too-many-locals
    """Verify committed fingerprints are current (read-only, no writes).

    Contract mirrors ``scripts/stamp_fingerprints.py --check``: waived/ignored
    units are excluded; a stampable unit with a missing/invalid fingerprint or any
    stale hash field, or an unwaived unit with no code file, makes the result not
    ``ok``.
    """
    base = project_root(root)
    layout = _layout_for(base)
    arch_maps = _load_architecture(layout.architecture_file)
    units = enumerate_units(layout, arch_maps, modules=modules)
    pddignore = load_pddignore(layout.root)
    waivers = load_waivers(layout.waivers_file)
    stampable, ignored, waived, no_code = partition_units(
        units, pddignore, waivers, layout.root
    )

    missing: List[str] = []
    stale: List[Tuple[str, List[str]]] = []
    with _chdir(layout.root):
        for unit in stampable:
            stored = _read_fingerprint_obj(unit)
            if stored is None:
                missing.append(unit.basename)
                continue
            current = compute_current_hashes(unit, stored.include_deps)
            diffs = [
                field_name
                for field_name in HASH_FIELDS
                if _norm(getattr(stored, field_name, None)) != _norm(current.get(field_name))
            ]
            if diffs:
                stale.append((unit.basename, diffs))
    unwaived_no_code = [u.basename for u in no_code]
    ok = not (missing or stale or unwaived_no_code)
    return CheckResult(
        ok=ok,
        stampable=len(stampable),
        ignored=len(ignored),
        waived=len(waived),
        missing=sorted(missing),
        stale=sorted(stale),
        no_code=sorted(unwaived_no_code),
    )
