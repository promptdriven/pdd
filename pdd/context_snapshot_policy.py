"""Policy checks for snapshotted nondeterministic prompt context."""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Any, Mapping, Optional

from .context_snapshot import redact_snapshot_text, replay_snapshot
from .evidence_manifest import _has_active_tag, _NONDETERMINISTIC_TAG_RE

_QUERY_INCLUDE_RE = re.compile(r"<include[^>]*\bquery\s*=", re.IGNORECASE)


def declared_nondeterministic_tags(prompt_text: str) -> list[str]:
    """Tags present in executable prompt regions (not documentation fences)."""

    tags: set[str] = set()
    if _has_active_tag(re.compile(r"<shell(?:\s[^>]*)?>", re.IGNORECASE), prompt_text):
        tags.add("shell")
    if _has_active_tag(re.compile(r"<web(?:\s[^>]*)?>", re.IGNORECASE), prompt_text):
        tags.add("web")
    if _has_active_tag(_QUERY_INCLUDE_RE, prompt_text):
        tags.add("query_include")
    return sorted(tags)


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _prompt_sha256(prompt_text: str) -> str:
    """Hash prompt text the same way snapshot manifests record ``prompt_sha256``."""
    safe_text, _, _ = redact_snapshot_text(prompt_text)
    return hashlib.sha256(safe_text.encode("utf-8")).hexdigest()


def _manifest_prompt_sha256(manifest: Mapping[str, Any]) -> Optional[str]:
    recorded = manifest.get("prompt_sha256")
    if isinstance(recorded, str) and recorded:
        return recorded
    prompt_section = manifest.get("prompt")
    if isinstance(prompt_section, Mapping):
        sha = prompt_section.get("sha256")
        if isinstance(sha, str) and sha:
            return sha
    return None


def _snapshot_matches_current_prompt(
    manifest_path: Path,
    prompt_text: str,
) -> bool:
    """Return True when *manifest_path* was captured from the current prompt body."""
    try:
        payload = _load_json(manifest_path)
    except (OSError, json.JSONDecodeError):
        return False
    recorded = _manifest_prompt_sha256(payload)
    if not recorded:
        return False
    return recorded == _prompt_sha256(prompt_text)


def _prompt_matches(manifest: Mapping[str, Any], prompt_path: Path, project_root: Path) -> bool:
    recorded = manifest.get("prompt_path")
    if not isinstance(recorded, str):
        prompt_section = manifest.get("prompt")
        if isinstance(prompt_section, Mapping):
            recorded = prompt_section.get("path")
    if not isinstance(recorded, str):
        return False
    try:
        return prompt_path.resolve() == (project_root / recorded).resolve()
    except (OSError, ValueError):
        return str(prompt_path.resolve()) == str((project_root / recorded).resolve())


def _snapshot_is_replayable(manifest_path: Path) -> bool:
    try:
        replay_snapshot(manifest_path)
    except (OSError, ValueError, json.JSONDecodeError):
        return False
    return True


def _snapshot_from_evidence(payload: Mapping[str, Any]) -> Optional[Path]:
    section = payload.get("context_snapshot")
    if not isinstance(section, Mapping) or not section.get("enabled"):
        return None
    manifest_path = section.get("manifest_path")
    if isinstance(manifest_path, str) and manifest_path:
        candidate = Path(manifest_path)
        if not candidate.is_absolute():
            candidate = Path.cwd() / candidate
        if candidate.is_file():
            return candidate.resolve()
    return None


def find_latest_snapshot_manifest(
    prompt_path: Path,
    project_root: Path,
    *,
    prompt_text: Optional[str] = None,
    require_matching_prompt_hash: bool = True,
) -> Optional[Path]:
    """Return the newest replayable snapshot manifest for ``prompt_path``.

    When ``require_matching_prompt_hash`` is True (default), only manifests whose
    recorded ``prompt_sha256`` matches the current prompt body are considered.
    """

    evidence_root = project_root / ".pdd" / "evidence"
    latest: Optional[tuple[str, Path]] = None

    resolved_prompt = prompt_path if prompt_path.is_absolute() else project_root / prompt_path
    if prompt_text is None:
        try:
            prompt_text = resolved_prompt.read_text(encoding="utf-8")
        except OSError:
            prompt_text = ""

    def _consider(run_id: str, manifest_path: Path) -> None:
        nonlocal latest
        if not _snapshot_is_replayable(manifest_path):
            return
        if require_matching_prompt_hash and not _snapshot_matches_current_prompt(
            manifest_path, prompt_text
        ):
            return
        candidate = (run_id, manifest_path.resolve())
        latest = max(latest, candidate) if latest else candidate

    latest_devunit = evidence_root / "devunits"
    if latest_devunit.is_dir():
        for path in sorted(latest_devunit.glob("*.latest.json")):
            try:
                payload = _load_json(path)
            except (OSError, json.JSONDecodeError):
                continue
            if not _prompt_matches(payload, prompt_path, project_root):
                continue
            snapshot_path = _snapshot_from_evidence(payload)
            if snapshot_path:
                run_id = str(payload.get("run", {}).get("id") or path.stem)
                _consider(run_id, snapshot_path)

    runs_dir = evidence_root / "runs"
    if runs_dir.is_dir():
        for path in sorted(runs_dir.glob("*.json"), reverse=True):
            try:
                payload = _load_json(path)
            except (OSError, json.JSONDecodeError):
                continue
            if payload.get("schema_version") != 1:
                continue
            if not _prompt_matches(payload, prompt_path, project_root):
                continue
            run_id = str(payload.get("run_id") or payload.get("run", {}).get("id") or path.stem)
            _consider(run_id, path)

    return latest[1] if latest else None


def check_snapshot_policy(
    prompt_path: Path,
    project_root: Optional[Path] = None,
) -> tuple[bool, str]:
    """Fail when a prompt declares nondeterministic tags without a replayable snapshot."""

    root = (project_root or Path.cwd()).resolve()
    path = prompt_path if prompt_path.is_absolute() else root / prompt_path
    if not path.is_file():
        return False, f"Prompt not found: {path}"

    prompt_text = path.read_text(encoding="utf-8")
    declared = declared_nondeterministic_tags(prompt_text)
    if not declared:
        return True, "Prompt has no active nondeterministic tags."

    snapshot_manifest = find_latest_snapshot_manifest(
        path, root, prompt_text=prompt_text, require_matching_prompt_hash=True
    )
    if snapshot_manifest is not None:
        return True, f"Replayable snapshot found: {snapshot_manifest}"

    stale_manifest = find_latest_snapshot_manifest(
        path, root, prompt_text=prompt_text, require_matching_prompt_hash=False
    )
    if stale_manifest is not None:
        return (
            False,
            "Prompt content changed since the latest snapshot was captured. "
            "Re-run with --snapshot or --snapshot-context to refresh .pdd/evidence/.",
        )

    tags = ", ".join(declared)
    return (
        False,
        "Prompt declares nondeterministic context "
        f"({tags}) but no replayable snapshot was found under .pdd/evidence/. "
        "Re-run with --snapshot or --snapshot-context.",
    )
