"""Replayable expanded-prompt context snapshots."""
from __future__ import annotations

import hashlib
import json
import os
import re
import uuid
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional


_DYNAMIC_TAG_PATTERNS = {
    "shell": re.compile(r"<shell(?:\s[^>]*)?>", re.IGNORECASE),
    "web": re.compile(r"<web(?:\s[^>]*)?>", re.IGNORECASE),
    "query_include": re.compile(r"<include\b[^>]*\bquery\s*=", re.IGNORECASE),
}
_SECRET_PATTERNS = [
    ("authorization_header", re.compile(r"(?im)\b(authorization)\s*:\s*[^\r\n]+")),
    ("api_key_header", re.compile(r"(?im)\b(x-api-key)\s*:\s*[^\r\n]+")),
    ("bearer_token", re.compile(r"(?i)\b(bearer|basic)\s+[A-Za-z0-9._~+/=-]+")),
    ("url_userinfo", re.compile(r"([a-z][a-z0-9+.-]*://)[^/@\s]+@")),
    ("github_token", re.compile(r"\b(?:ghp|gho|ghu|ghs|ghr)_[A-Za-z0-9_]{20,}\b|github_pat_[A-Za-z0-9_]+")),
    ("openai_key", re.compile(r"\bsk-[A-Za-z0-9_-]{20,}\b")),
    ("google_key", re.compile(r"\bAIza[A-Za-z0-9_-]{20,}\b")),
    ("xai_key", re.compile(r"\bxai-[A-Za-z0-9_-]{20,}\b")),
    ("groq_key", re.compile(r"\bgsk_[A-Za-z0-9_-]{20,}\b")),
    ("aws_access_key", re.compile(r"\b(?:AKIA|ASIA)[A-Z0-9]{16}\b")),
    ("slack_token", re.compile(r"\bxox[baprs]-[A-Za-z0-9-]{10,}\b")),
    (
        "secret_assignment",
        re.compile(
            r"(?i)\b([A-Z0-9_]*(?:TOKEN|SECRET|API_KEY|PASSWORD|PRIVATE_KEY)|api[_-]?key|access[_-]?token|secret|password)\b\s*[:=]\s*['\"]?[^'\"\s]+"
        ),
    ),
]
_SECRET_ENV_NAME = re.compile(r"(?i)(TOKEN|SECRET|PASSWORD|API[_-]?KEY|AUTH|BEARER)")


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _safe_name(value: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9_.-]+", "-", value.strip()).strip("-")
    return slug[:80] or "artifact"


def _portable_path(path: Path, base: Path) -> tuple[str, bool]:
    """Return a stable relative path when possible, else an explicit absolute path."""

    try:
        return path.resolve().relative_to(base.resolve()).as_posix(), False
    except (OSError, ValueError):
        return str(path.resolve()), True


def detect_dynamic_tags(prompt_text: str) -> List[str]:
    """Return nondeterministic prompt directives visible in the raw prompt."""

    return [
        name
        for name, pattern in _DYNAMIC_TAG_PATTERNS.items()
        if pattern.search(prompt_text)
    ]


def redact_snapshot_text(value: str) -> tuple[str, bool, List[str]]:
    """Redact common secret forms before snapshot hashing or persistence."""

    redacted = value
    applied: List[str] = []
    for name, pattern in _SECRET_PATTERNS:
        updated = pattern.sub("[REDACTED]", redacted)
        if updated != redacted:
            applied.append(name)
            redacted = updated

    for name, env_value in os.environ.items():
        if not env_value or len(env_value) < 8 or not _SECRET_ENV_NAME.search(name):
            continue
        updated = redacted.replace(env_value, "[REDACTED]")
        if updated != redacted:
            applied.append(f"environment:{name}")
            redacted = updated

    return redacted, redacted != value, sorted(set(applied))


def _read_json(path: Path) -> Dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise FileNotFoundError(f"Snapshot artifact not readable: {path}") from exc
    except json.JSONDecodeError as exc:
        raise ValueError(f"Snapshot artifact is not valid JSON: {path}") from exc
    if not isinstance(data, dict):
        raise ValueError(f"Snapshot artifact must contain a JSON object: {path}")
    return data


def _safe_resolve(snapshot_dir: Path, raw_path: str, *, manifest_parent: Optional[Path] = None) -> Path:
    candidate = Path(raw_path)
    root = snapshot_dir.resolve()
    if not candidate.is_absolute():
        primary = (root / candidate).resolve()
        fallback = (
            (manifest_parent / candidate).resolve()
            if manifest_parent is not None
            else primary
        )
        candidate = primary if primary.exists() else fallback
    resolved = candidate.resolve()
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise ValueError(f"Snapshot path escapes snapshot directory: {raw_path}") from exc
    return resolved


def _snapshot_dir_for_manifest(artifact_path: Path, payload: Mapping[str, Any]) -> Path:
    raw_snapshot_dir = payload.get("snapshot_dir")
    if isinstance(raw_snapshot_dir, str) and raw_snapshot_dir:
        candidate = Path(raw_snapshot_dir)
        if not candidate.is_absolute():
            if artifact_path.parent.name == "runs" and candidate.parts[:1] == ("runs",):
                candidate = artifact_path.parent.parent / candidate
            else:
                candidate = artifact_path.parent / candidate
        return candidate.resolve()

    run_id = payload.get("run_id")
    if isinstance(run_id, str) and run_id:
        return (artifact_path.parent / run_id).resolve()

    return artifact_path.with_suffix("").resolve()


def _find_snapshot_manifest(run_artifact: Path, payload: Mapping[str, Any]) -> Optional[Path]:
    candidates: List[str] = []
    for key in ("snapshot_manifest_path", "manifest_path"):
        value = payload.get(key)
        if isinstance(value, str):
            candidates.append(value)

    for section_name in ("context_snapshot", "snapshot", "context"):
        section = payload.get(section_name)
        if isinstance(section, Mapping):
            for key in ("manifest_path", "snapshot_manifest_path"):
                value = section.get(key)
                if isinstance(value, str):
                    candidates.append(value)

    if not candidates:
        return None

    bases = [run_artifact.parent]
    if run_artifact.parent.name == "runs":
        bases.append(run_artifact.parent.parent)
    for candidate in candidates:
        path = Path(candidate)
        paths = [path] if path.is_absolute() else [base / path for base in bases]
        for resolved_candidate in paths:
            if resolved_candidate.exists():
                return resolved_candidate.resolve()
    fallback = Path(candidates[0])
    if fallback.is_absolute():
        return fallback.resolve()
    return (bases[-1] / fallback).resolve()


@dataclass
class ContextSnapshotRecorder:
    """Small recorder for callers that need to persist expanded prompt text."""

    prompt_path: Path
    evidence_root: Path
    command: str = ""
    run_id: str = ""
    artifacts: List[Dict[str, Any]] = field(default_factory=list)
    dynamic_tags: List[str] = field(default_factory=list)
    declared_dynamic_tags: List[str] = field(default_factory=list)
    redaction_applied: bool = False
    prompt_sha256: Optional[str] = None
    expanded_sha256: Optional[str] = None
    output_hashes: List[Dict[str, Any]] = field(default_factory=list)
    grounding_examples: List[Dict[str, Any]] = field(default_factory=list)
    redaction_patterns: List[str] = field(default_factory=list)

    def __post_init__(self) -> None:
        if not self.run_id:
            timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
            self.run_id = f"{timestamp}-{uuid.uuid4().hex[:8]}"
        self.run_dir.mkdir(parents=True, exist_ok=True)

    @property
    def run_dir(self) -> Path:
        return self.evidence_root / "runs" / self.run_id

    @property
    def run_artifact(self) -> Path:
        return self.evidence_root / "runs" / f"{self.run_id}.json"

    @property
    def project_root(self) -> Path:
        if self.evidence_root.name == "evidence" and self.evidence_root.parent.name == ".pdd":
            return self.evidence_root.parent.parent
        return Path.cwd()

    def _project_path(self, path: Path) -> tuple[str, bool]:
        return _portable_path(path, self.project_root)

    def _evidence_path(self, path: Path) -> tuple[str, bool]:
        return _portable_path(path, self.evidence_root)

    def _write_text_artifact(
        self,
        *,
        artifact_type: str,
        name: str,
        text: str,
        metadata: Optional[Mapping[str, Any]] = None,
    ) -> Dict[str, Any]:
        safe_text, redacted, patterns = redact_snapshot_text(text)
        self.redaction_applied = self.redaction_applied or redacted
        self.redaction_patterns = sorted(set(self.redaction_patterns) | set(patterns))
        digest = _sha256_text(safe_text)
        path = self.run_dir / f"{_safe_name(name)}.txt"
        path.write_text(safe_text, encoding="utf-8")
        portable_path, external = _portable_path(path, self.run_dir)
        record = {
            "type": artifact_type,
            "path": portable_path,
            "sha256": digest,
            "redaction_applied": redacted,
            "redaction_patterns": patterns,
        }
        if external:
            record["path_external"] = True
        if metadata:
            record["metadata"] = dict(metadata)
        self.artifacts.append(record)
        return record

    def record_prompt_source(self, prompt_text: str) -> Dict[str, Any]:
        """Record raw prompt metadata and declared nondeterministic directives."""

        safe_text, redacted, patterns = redact_snapshot_text(prompt_text)
        self.redaction_applied = self.redaction_applied or redacted
        self.redaction_patterns = sorted(set(self.redaction_patterns) | set(patterns))
        self.prompt_sha256 = _sha256_text(safe_text)
        self.declared_dynamic_tags = sorted(
            set(self.declared_dynamic_tags) | set(detect_dynamic_tags(prompt_text))
        )
        prompt_path, external = self._project_path(self.prompt_path)
        record = {
            "path": prompt_path,
            "sha256": self.prompt_sha256,
            "declared_dynamic_tags": self.declared_dynamic_tags,
            "dynamic_tags": sorted(set(self.dynamic_tags)),
            "redaction_applied": redacted,
            "redaction_patterns": patterns,
        }
        if external:
            record["path_external"] = True
        return {
            **record,
        }

    def record_expanded_prompt(self, expanded_prompt: str) -> Dict[str, Any]:
        record = self._write_text_artifact(
            artifact_type="expanded_prompt",
            name="expanded_prompt",
            text=expanded_prompt,
        )
        self.expanded_sha256 = record["sha256"]
        return record

    def record_include(
        self,
        *,
        source_path: str | Path,
        content: str,
        query: Optional[str] = None,
        output: Optional[str] = None,
    ) -> Dict[str, Any]:
        """Record deterministic include or semantic query extraction output."""

        artifact_type = "query_include" if query else "include"
        if query and "query_include" not in self.dynamic_tags:
            self.dynamic_tags.append("query_include")
        source = Path(source_path)
        source_value, source_external = self._project_path(source)
        metadata: Dict[str, Any] = {"source_path": source_value}
        if source_external:
            metadata["source_path_external"] = True
        if source.exists():
            metadata["source_sha256"] = _sha256_file(source)
        meta_redacted = False
        meta_patterns: List[str] = []
        if query:
            safe_query, q_redacted, q_patterns = redact_snapshot_text(query)
            metadata["query"] = safe_query
            if q_redacted:
                meta_redacted = True
                meta_patterns = sorted(set(meta_patterns) | set(q_patterns))
        if meta_redacted:
            self.redaction_applied = True
            self.redaction_patterns = sorted(set(self.redaction_patterns) | set(meta_patterns))
        record = self._write_text_artifact(
            artifact_type=artifact_type,
            name=f"{artifact_type}-{len(self.artifacts) + 1}-{source.name}",
            text=output if output is not None else content,
            metadata=metadata,
        )
        if meta_redacted:
            record["redaction_applied"] = True
            record["redaction_patterns"] = sorted(set(record["redaction_patterns"]) | set(meta_patterns))
        return record

    def record_shell(
        self,
        *,
        command: str,
        stdout: str = "",
        stderr: str = "",
        exit_code: int = 0,
        cwd: Optional[str] = None,
        timeout: Optional[float] = None,
    ) -> Dict[str, Any]:
        """Record shell output without persisting raw environment dumps."""

        if "shell" not in self.dynamic_tags:
            self.dynamic_tags.append("shell")
        safe_command, cmd_redacted, cmd_patterns = redact_snapshot_text(command)
        safe_cwd, cwd_redacted, cwd_patterns = redact_snapshot_text(cwd) if cwd else (None, False, [])
        meta_redacted = cmd_redacted or cwd_redacted
        meta_patterns: List[str] = sorted(set(cmd_patterns) | set(cwd_patterns))
        if meta_redacted:
            self.redaction_applied = True
            self.redaction_patterns = sorted(set(self.redaction_patterns) | set(meta_patterns))
        record = self._write_text_artifact(
            artifact_type="shell",
            name=f"shell-{len(self.artifacts) + 1}",
            text=f"STDOUT:\n{stdout}\nSTDERR:\n{stderr}",
            metadata={
                "command": safe_command,
                "cwd": safe_cwd,
                "exit_code": exit_code,
                "timeout": timeout,
                "environment": "not_persisted",
            },
        )
        if meta_redacted:
            record["redaction_applied"] = True
            record["redaction_patterns"] = sorted(set(record["redaction_patterns"]) | set(meta_patterns))
        return record

    def record_web(
        self,
        *,
        url: str,
        content: str,
        fetcher: str = "unknown",
        status: Optional[int] = None,
    ) -> Dict[str, Any]:
        """Record fetched web content with redaction metadata."""

        if "web" not in self.dynamic_tags:
            self.dynamic_tags.append("web")
        safe_url, url_redacted, url_patterns = redact_snapshot_text(url)
        if url_redacted:
            self.redaction_applied = True
            self.redaction_patterns = sorted(set(self.redaction_patterns) | set(url_patterns))
        record = self._write_text_artifact(
            artifact_type="web",
            name=f"web-{len(self.artifacts) + 1}",
            text=content,
            metadata={"url": safe_url, "fetcher": fetcher, "status": status},
        )
        if url_redacted:
            record["redaction_applied"] = True
            record["redaction_patterns"] = sorted(set(record["redaction_patterns"]) | set(url_patterns))
        return record

    def record_grounding_examples(
        self, examples: Iterable[Mapping[str, Any]]
    ) -> List[Dict[str, Any]]:
        self.grounding_examples = [dict(example) for example in examples]
        return self.grounding_examples

    def record_grounding_unavailable(self, reason: str) -> List[Dict[str, Any]]:
        """Record why grounding/few-shot examples are unavailable for this run."""

        self.grounding_examples = [{"status": "unavailable", "reason": reason}]
        return self.grounding_examples

    def record_output_hashes(self, output_files: Iterable[str | Path]) -> List[Dict[str, Any]]:
        records: List[Dict[str, Any]] = []
        for raw_path in output_files:
            path = Path(raw_path)
            if not path.exists() or not path.is_file():
                continue
            output_path, external = self._project_path(path)
            record: Dict[str, Any] = {"path": output_path, "sha256": _sha256_file(path)}
            if external:
                record["path_external"] = True
            records.append(record)
        self.output_hashes = records
        return records

    def finalize(
        self,
        expanded_prompt: Optional[str] = None,
        *,
        prompt_text: Optional[str] = None,
        output_files: Iterable[str | Path] = (),
        model: Optional[str] = None,
        provider: Optional[str] = None,
        grounding_examples: Iterable[Mapping[str, Any]] = (),
    ) -> Dict[str, Any]:
        prompt_record = self.record_prompt_source(prompt_text) if prompt_text is not None else None
        expanded = self.record_expanded_prompt(expanded_prompt) if expanded_prompt is not None else None
        if output_files:
            self.record_output_hashes(output_files)
        if grounding_examples:
            self.record_grounding_examples(grounding_examples)
        elif not self.grounding_examples:
            self.record_grounding_unavailable("not_provided_by_caller")
        prompt_path, prompt_external = self._project_path(self.prompt_path)
        manifest_path, manifest_external = self._evidence_path(self.run_artifact)
        snapshot_dir, snapshot_external = self._evidence_path(self.run_dir)
        manifest = {
            "schema_version": 1,
            "command": self.command,
            "prompt_path": prompt_path,
            "run_id": self.run_id,
            "manifest_path": manifest_path,
            "snapshot_dir": snapshot_dir,
            "uses_nondeterministic_context": bool(self.dynamic_tags),
            "dynamic_tags": sorted(set(self.dynamic_tags)),
            "declared_dynamic_tags": self.declared_dynamic_tags,
            "redaction": {
                "applied": self.redaction_applied,
                "patterns": self.redaction_patterns,
                "policy": "authorization headers, bearer/basic tokens, URL userinfo credentials, provider tokens/keys, secret assignments, and secret-like environment values are redacted before hashing and storage",
                "raw_environment_persisted": False,
                "pre_redaction_hashes_persisted": False,
            },
            "prompt": prompt_record,
            "expanded_prompt": expanded,
            "prompt_sha256": self.prompt_sha256,
            "expanded_sha256": self.expanded_sha256,
            "outputs": self.output_hashes,
            "generation": {
                "model": model,
                "provider": provider,
                "grounding_examples": self.grounding_examples,
            },
            "artifacts": self.artifacts,
        }
        if prompt_external:
            manifest["prompt_path_external"] = True
        if manifest_external:
            manifest["manifest_path_external"] = True
        if snapshot_external:
            manifest["snapshot_dir_external"] = True
        self.run_artifact.parent.mkdir(parents=True, exist_ok=True)
        self.run_artifact.write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        return manifest


def start_snapshot_run(
    prompt_path: str | Path,
    *,
    evidence_root: str | Path | None = None,
    command: str = "",
) -> ContextSnapshotRecorder:
    """Start a snapshot run rooted in `.pdd/evidence` by default."""

    root = Path(evidence_root) if evidence_root is not None else Path.cwd() / ".pdd" / "evidence"
    return ContextSnapshotRecorder(Path(prompt_path), root, command=command)


def replay_snapshot(run_artifact: str | Path) -> Dict[str, Any]:
    """Load a run artifact or snapshot manifest and verify expanded prompt hash."""

    artifact_path = Path(run_artifact).resolve()
    payload = _read_json(artifact_path)
    snapshot_manifest = _find_snapshot_manifest(artifact_path, payload)
    if snapshot_manifest and snapshot_manifest != artifact_path:
        payload = _read_json(snapshot_manifest)
        artifact_path = snapshot_manifest

    schema_version = payload.get("schema_version")
    if schema_version != 1:
        raise ValueError(f"Unsupported snapshot schema_version: {schema_version!r}")

    expanded = payload.get("expanded_prompt")
    if not isinstance(expanded, Mapping):
        context = payload.get("context_snapshot")
        if isinstance(context, Mapping):
            expanded = context.get("expanded_prompt")
    if not isinstance(expanded, Mapping):
        raise ValueError("Artifact does not contain replayable expanded prompt metadata.")

    expanded_path_value = expanded.get("path")
    expected_hash = expanded.get("sha256") or payload.get("expanded_sha256")
    if not isinstance(expanded_path_value, str) or not isinstance(expected_hash, str):
        raise ValueError("Expanded prompt metadata requires path and sha256.")

    snapshot_dir = _snapshot_dir_for_manifest(artifact_path, payload)
    expanded_path = _safe_resolve(
        snapshot_dir,
        expanded_path_value,
        manifest_parent=artifact_path.parent,
    )
    expanded_text = expanded_path.read_text(encoding="utf-8")
    actual_hash = _sha256_text(expanded_text)
    verified = actual_hash == expected_hash
    if not verified:
        raise ValueError(
            f"Expanded prompt hash mismatch: expected {expected_hash}, got {actual_hash}"
        )

    return {
        "success": True,
        "verified": True,
        "expanded_prompt": expanded_text,
        "expanded_sha256": actual_hash,
        "run_artifact": str(Path(run_artifact)),
        "snapshot_manifest_path": str(artifact_path),
        "expanded_prompt_path": str(expanded_path),
    }
