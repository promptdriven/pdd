"""Materialize a per-(scenario, size) working repo (design.md §3.2 stage 3).

Pure function of ``(core, manifest)``: copy the core, then place each manifest
file — verbatim pool files (``regrow``) from the pool root, generated files
(``mutate``/``template``) from the persisted content store. Every placed file
is sha256-verified against the manifest, and the resulting tree is hashed so
byte-identical rebuilds are checkable.

The manifest itself, the pool, and anything under the scenario's ``hidden/``
tree are never copied into the variant (design §3.3).
"""

from __future__ import annotations

import hashlib
import shutil
from pathlib import Path

from harness.distractors.manifest import resolve_within_root, validate_relative_path


class VariantIntegrityError(RuntimeError):
    pass


def _hash_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tree_sha256(root: str | Path) -> str:
    """Order-stable content hash of a tree (paths + bytes)."""
    root = Path(root)
    digest = hashlib.sha256()
    for path in sorted(p for p in root.rglob("*") if p.is_file()):
        digest.update(path.relative_to(root).as_posix().encode())
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def materialize_variant(
    core_root: str | Path,
    manifest: dict,
    destination: str | Path,
    pool_root: str | Path | None = None,
    distractors_dir: str | Path | None = None,
) -> str:
    """Build the working repo; returns the materialized tree's sha256.

    ``distractors_dir`` is the ManifestWriter output dir holding
    ``generated/<scenario>/<size>/...`` content for non-regrow files.
    """
    core_root = Path(core_root)
    destination = Path(destination)
    if destination.exists():
        raise VariantIntegrityError(f"destination already exists: {destination}")
    shutil.copytree(core_root, destination)

    for entry in manifest.get("files", []):
        rel = entry["upstream_path"]
        try:
            rel_path = validate_relative_path(rel, field_name="upstream_path")
            target_path = resolve_within_root(
                destination, rel_path, field_name="upstream_path"
            )
        except ValueError as exc:
            raise VariantIntegrityError(str(exc)) from exc
        if target_path.exists():
            raise VariantIntegrityError(f"manifest path collides with core: {rel}")
        if entry["mode"] == "regrow":
            if pool_root is None:
                raise VariantIntegrityError(f"regrow file {rel} but no pool_root given")
            try:
                source_path = validate_relative_path(
                    entry["source_path"], field_name="source_path"
                )
                source = resolve_within_root(
                    pool_root, source_path, field_name="source_path"
                )
            except ValueError as exc:
                raise VariantIntegrityError(str(exc)) from exc
        else:
            if distractors_dir is None or not entry.get("content_path"):
                raise VariantIntegrityError(
                    f"generated file {rel} but no content store given"
                )
            try:
                content_path = validate_relative_path(
                    entry["content_path"], field_name="content_path"
                )
                source = resolve_within_root(
                    distractors_dir, content_path, field_name="content_path"
                )
            except ValueError as exc:
                raise VariantIntegrityError(str(exc)) from exc
        if not source.is_file():
            raise VariantIntegrityError(f"missing distractor source: {source}")
        actual = _hash_file(source)
        if actual != entry["sha256"]:
            raise VariantIntegrityError(
                f"sha256 mismatch for {rel}: manifest {entry['sha256'][:12]}…, "
                f"source {actual[:12]}…"
            )
        target_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target_path)

    return tree_sha256(destination)
