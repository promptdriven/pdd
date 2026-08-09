"""Manifest persistence + freeze enforcement (design.md §5.5).

The manifest is the *secret label key*: it lives out-of-tree (harness side),
is committed before any model run, and is consulted only by post-hoc
analysis. ``manifests.lock`` aggregates the sha256 of every committed
manifest; the runner refuses to execute a (scenario, size) whose manifest
hash is not in the lock.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath


def validate_relative_path(raw_path: str, *, field_name: str) -> Path:
    path = PurePosixPath(str(raw_path))
    if path.is_absolute():
        raise ValueError(f"{field_name} must be relative: {raw_path}")
    if any(part == ".." for part in path.parts):
        raise ValueError(f"{field_name} must not contain '..': {raw_path}")
    if not path.parts:
        raise ValueError(f"{field_name} must not be empty")
    return Path(*path.parts)


def resolve_within_root(root: str | Path, relative_path: str | Path, *, field_name: str) -> Path:
    resolved_root = Path(root).resolve()
    resolved_candidate = (resolved_root / relative_path).resolve()
    if resolved_candidate != resolved_root and resolved_root not in resolved_candidate.parents:
        raise ValueError(f"{field_name} escapes its root: {relative_path}")
    return resolved_candidate


class ManifestWriter:
    """Persist a generated manifest + the contents of generated files."""

    def __init__(self, out_dir: str | Path) -> None:
        self.out_dir = Path(out_dir)
        self.manifest_dir = self.out_dir / "manifests"
        self.generated_dir = self.out_dir / "generated"

    def write(self, manifest: dict) -> Path:
        """Write ``<scenario>.<size>.json`` and generated file contents.

        The ``generated_contents`` map is split out of the manifest document:
        contents go under ``generated/<scenario>/<size>/<dest>`` and the
        manifest gains per-file ``content_path`` pointers instead.
        """
        scenario = manifest["scenario_id"]
        size = manifest["size"]
        generated: dict[str, str] = manifest.pop("generated_contents", {})
        content_root = self.generated_dir / scenario / size
        for entry in manifest["files"]:
            destination = entry["upstream_path"]
            destination_rel = validate_relative_path(
                destination, field_name="upstream_path"
            )
            if entry["mode"] == "regrow":
                entry["content_path"] = None
                continue
            content = generated[destination]
            content_path = resolve_within_root(
                content_root, destination_rel, field_name="content_path"
            )
            content_path.parent.mkdir(parents=True, exist_ok=True)
            content_path.write_text(content, encoding="utf-8")
            entry["content_path"] = str(
                content_path.relative_to(self.out_dir.resolve()).as_posix()
            )

        self.manifest_dir.mkdir(parents=True, exist_ok=True)
        path = self.manifest_dir / f"{scenario}.{size}.json"
        path.write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        return path


def manifest_sha256(path: str | Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load_manifest(path: str | Path) -> dict:
    return json.loads(Path(path).read_text(encoding="utf-8"))


def write_lockfile(manifest_paths: list[str | Path], lock_path: str | Path) -> None:
    """Freeze the committed manifests (design §3.3, §5.5)."""
    entries = {
        Path(p).name: manifest_sha256(p) for p in sorted(manifest_paths, key=str)
    }
    Path(lock_path).write_text(
        json.dumps({"schema_version": 1, "manifests": entries}, indent=2, sort_keys=True)
        + "\n",
        encoding="utf-8",
    )


def verify_lockfile(manifest_path: str | Path, lock_path: str | Path) -> bool:
    """True iff the manifest's current bytes match its locked hash."""
    lock = json.loads(Path(lock_path).read_text(encoding="utf-8"))
    expected = lock.get("manifests", {}).get(Path(manifest_path).name)
    return expected is not None and expected == manifest_sha256(manifest_path)
