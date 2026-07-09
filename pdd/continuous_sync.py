"""Deterministic continuous-sync classification and reconciliation reports."""
from __future__ import annotations

import json
import subprocess
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional

from .operation_log import get_fingerprint_path, infer_module_identity, save_fingerprint
from .sync_determine_operation import (
    Fingerprint,
    calculate_current_hashes,
    get_pdd_file_paths,
    read_fingerprint,
)


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


def _prompts_dir_for(prompt_path: Path) -> Path:
    """Return the concrete prompts directory to pass into path resolution."""
    return prompt_path.parent


def discover_units(
    root: Optional[Path] = None,
    modules: Optional[Iterable[str]] = None,
) -> List[SyncUnit]:
    """Discover prompt-backed units under ``root``."""
    base = project_root(root)
    wanted = set(modules or [])
    prompt_root = base / "prompts"
    if not prompt_root.exists():
        return []

    units: List[SyncUnit] = []
    for prompt_path in sorted(prompt_root.rglob("*_*.prompt")):
        basename, language = infer_module_identity(prompt_path)
        if basename is None or language is None:
            continue
        if wanted and basename not in wanted and prompt_path.stem not in wanted:
            continue
        units.append(
            SyncUnit(
                basename=basename,
                language=language,
                prompt_path=prompt_path,
                prompts_dir=_prompts_dir_for(prompt_path),
            )
        )
    return units


def _load_fingerprint_json(path: Path) -> tuple[Optional[Dict[str, Any]], Optional[str]]:
    if not path.exists():
        return None, "missing"
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None, "invalid"
    if not isinstance(data, dict):
        return None, "invalid"
    return data, None


def _paths_as_json(paths: Dict[str, Any], root: Path) -> Dict[str, Any]:
    payload: Dict[str, Any] = {}
    for key, value in paths.items():
        if isinstance(value, Path):
            try:
                payload[key] = value.resolve().relative_to(root.resolve()).as_posix()
            except (OSError, ValueError):
                payload[key] = str(value)
        elif isinstance(value, list):
            payload[key] = [str(item) for item in value]
        else:
            payload[key] = str(value)
    return payload


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
    # pylint: disable=broad-exception-caught
    """Classify one sync unit without mutating files."""
    base = project_root(root)
    try:
        paths = get_pdd_file_paths(
            unit.basename,
            unit.language,
            prompts_dir=str(unit.prompts_dir),
        )
    except Exception as exc:  # pragma: no cover - surfaced in JSON report
        return {
            "basename": unit.basename,
            "language": unit.language,
            "classification": FAILURE_CLASSIFICATION,
            "operation": "none",
            "reason": f"path resolution failed: {exc}",
            "changed_files": [],
            "metadata_valid": False,
            "paths": {"prompt": str(unit.prompt_path)},
        }

    fp_path = get_fingerprint_path(unit.basename, unit.language, paths=paths)
    _raw_fp, raw_error = _load_fingerprint_json(fp_path)
    if raw_error is not None:
        return {
            "basename": unit.basename,
            "language": unit.language,
            "classification": UNBASELINED_CLASSIFICATION,
            "operation": "none",
            "reason": f"fingerprint {raw_error}",
            "changed_files": [],
            "metadata_valid": False,
            "fingerprint_path": str(fp_path),
            "paths": _paths_as_json(paths, base),
        }

    fingerprint = read_fingerprint(unit.basename, unit.language, paths=paths)
    if fingerprint is None:
        return {
            "basename": unit.basename,
            "language": unit.language,
            "classification": UNBASELINED_CLASSIFICATION,
            "operation": "none",
            "reason": "fingerprint invalid",
            "changed_files": [],
            "metadata_valid": False,
            "fingerprint_path": str(fp_path),
            "paths": _paths_as_json(paths, base),
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


def _heal_units(
    units: List[SyncUnit],
    classified: List[Dict[str, Any]],
) -> List[str]:
    healed: List[str] = []
    by_key = {(unit.basename, unit.language): unit for unit in units}
    for item in classified:
        if item["classification"] not in DRIFT_CLASSIFICATIONS:
            continue
        unit = by_key.get((item["basename"], item["language"]))
        if unit is None:
            continue
        paths = get_pdd_file_paths(
            unit.basename,
            unit.language,
            prompts_dir=str(unit.prompts_dir),
        )
        fingerprint = read_fingerprint(unit.basename, unit.language, paths=paths)
        operation = "fix"
        if fingerprint and fingerprint.command in {"verify", "test", "fix", "update"}:
            operation = fingerprint.command
        save_fingerprint(unit.basename, unit.language, operation, paths, 0.0, "reconcile")
        healed.append(unit.basename)
    return healed


def build_report(
    *,
    consumer: str,
    root: Optional[Path] = None,
    modules: Optional[Iterable[str]] = None,
    heal: bool = False,
    ledger: bool = False,
) -> Dict[str, Any]:
    """Build a shared continuous-sync JSON report."""
    base = project_root(root)
    units = discover_units(base, modules=modules)
    classified = [classify_unit(unit, base) for unit in units]
    healed = _heal_units(units, classified) if heal else []
    if healed:
        classified = [classify_unit(unit, base) for unit in units]
    summary = _build_summary(classified)
    ledger_path = _append_ledger(base, consumer, classified) if ledger else None
    ok = (
        summary["metadata_stale"] == 0
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
        "healed": healed,
    }
    if ledger_path:
        report["ledger_path"] = ledger_path
    return report
