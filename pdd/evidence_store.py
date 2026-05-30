"""Load and inspect PDD evidence manifests under ``.pdd/evidence/``."""
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def devunits_dir(project_root: Path) -> Path:
    return project_root / ".pdd" / "evidence" / "devunits"


def list_latest_manifests(project_root: Path) -> list[Path]:
    directory = devunits_dir(project_root)
    if not directory.is_dir():
        return []
    return sorted(directory.glob("*.latest.json"))


def basename_from_manifest_path(path: Path) -> str:
    name = path.name
    if name.endswith(".latest.json"):
        return name[: -len(".latest.json")]
    return path.stem


def resolve_prompt_path(
    project_root: Path,
    basename: str,
    manifest: Optional[dict[str, Any]] = None,
) -> Optional[Path]:
    if manifest:
        routine_prompt = (manifest.get("prompt") or {}).get("path")
        if routine_prompt:
            candidate = Path(routine_prompt)
            if not candidate.is_absolute():
                candidate = project_root / candidate
            if candidate.is_file():
                return candidate.resolve()
        rule_prompt = manifest.get("prompt_path")
        if rule_prompt:
            candidate = Path(rule_prompt)
            if not candidate.is_absolute():
                candidate = project_root / candidate
            if candidate.is_file():
                return candidate.resolve()

    prompts_root = project_root / "prompts"
    direct = list(prompts_root.glob(f"{basename}_*.prompt"))
    if len(direct) == 1:
        return direct[0].resolve()
    nested = list(prompts_root.rglob(f"*{basename}*.prompt"))
    if len(nested) == 1:
        return nested[0].resolve()
    return None


@dataclass
class OutputFreshness:
    path: str
    expected_sha256: str
    current_sha256: str
    fresh: bool


@dataclass
class ManifestView:
    path: Path
    basename: str
    schema: str
    raw: dict[str, Any]
    prompt_path: Optional[Path] = None
    validation: dict[str, str] = field(default_factory=dict)
    outputs: list[dict[str, str]] = field(default_factory=list)
    generation: dict[str, Any] = field(default_factory=dict)
    contracts: dict[str, Any] = field(default_factory=dict)
    gap_count: int = 0
    rule_manifest: bool = False

    @classmethod
    def from_file(cls, path: Path, project_root: Path) -> ManifestView:
        data = load_json(path)
        basename = basename_from_manifest_path(path)
        schema = str(data.get("schema") or data.get("schema_version") or "unknown")
        view = cls(path=path, basename=basename, schema=schema, raw=data)
        if data.get("schema") == "pdd.evidence.manifest.v1":
            view.rule_manifest = True
            view.gap_count = int(data.get("gap_count") or 0)
            prompt = data.get("prompt_path")
            if prompt:
                candidate = Path(prompt)
                if not candidate.is_absolute():
                    candidate = project_root / candidate
                if candidate.is_file():
                    view.prompt_path = candidate.resolve()
            return view

        view.validation = {
            str(key): str(value)
            for key, value in (data.get("validation") or {}).items()
        }
        view.outputs = list(data.get("outputs") or [])
        view.generation = dict(data.get("generation") or {})
        view.contracts = dict(data.get("contracts") or {})
        view.prompt_path = resolve_prompt_path(project_root, basename, data)
        return view


def output_freshness(
    manifest: ManifestView,
    project_root: Path,
) -> list[OutputFreshness]:
    results: list[OutputFreshness] = []
    for record in manifest.outputs:
        rel = record.get("path")
        expected = record.get("sha256", "")
        if not rel:
            continue
        candidate = Path(rel)
        if not candidate.is_absolute():
            candidate = project_root / candidate
        if not candidate.is_file():
            results.append(
                OutputFreshness(
                    path=str(rel),
                    expected_sha256=expected,
                    current_sha256="",
                    fresh=False,
                )
            )
            continue
        current = sha256_file(candidate)
        results.append(
            OutputFreshness(
                path=str(rel),
                expected_sha256=expected,
                current_sha256=current,
                fresh=bool(expected) and current == expected,
            )
        )
    return results


def prompt_freshness(manifest: ManifestView, project_root: Path) -> bool:
    if not manifest.rule_manifest or manifest.prompt_path is None:
        return True
    expected = str(manifest.raw.get("prompt_sha256") or "")
    if not expected:
        return True
    return sha256_file(manifest.prompt_path) == expected
