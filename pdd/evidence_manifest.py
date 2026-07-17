"""Routine, machine-readable audit receipts for PDD command runs."""
from __future__ import annotations

import hashlib
import json
import math
import os
import re
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Iterator, Mapping, Optional

from . import get_version
from .preprocess import (
    _extract_code_spans,
    _intersects_any_span,
    _parse_attrs,
    compute_user_intent_paths,
    preprocess,
)
from .contract_ir import parse_prompt_contracts
from .grounding_provenance import grounding_reviewed_for_manifest, normalize_grounding
from .sync_order import extract_includes_from_file

SCHEMA_VERSION = 2
_NONDETERMINISTIC_TAG_RE = re.compile(
    r"<(?:shell|web)\b|<include[^>]*\bquery\s*=",
    re.IGNORECASE,
)
_UNSUPPORTED_EXPANSION_RE = re.compile(
    r"<(?:shell|web|include-many)\b|<include[^>]*(?:query|select)\s*=|\$\{",
    re.IGNORECASE,
)
_INCLUDE_BODY_RE = re.compile(
    r"<include(?:\s+([^>]*?))?(?<!/)>(.*?)</include>",
    re.DOTALL | re.IGNORECASE,
)
_INCLUDE_SELF_CLOSING_RE = re.compile(
    r"<include\s+([^>]*?)\s*/>",
    re.DOTALL | re.IGNORECASE,
)
_BACKTICK_INCLUDE_RE = re.compile(r"```<([^>]*?)>```", re.DOTALL)
_CONTRACT_RULES_RE = re.compile(r"<contract_rules\b", re.IGNORECASE)


def _has_active_tag(pattern: re.Pattern[str], content: str) -> bool:
    """Return True only when *pattern* matches outside fenced/inline code spans."""
    code_spans = _extract_code_spans(content)
    for m in pattern.finditer(content):
        if not _intersects_any_span(m.start(), m.end(), code_spans):
            return True
    return False


@contextmanager
def _project_cwd(project_root: Path) -> Iterator[None]:
    previous = os.getcwd()
    os.chdir(project_root)
    try:
        yield
    finally:
        os.chdir(previous)


def _sha256_bytes(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def _sha256_file(path: Path) -> str:
    return _sha256_bytes(path.read_bytes())


def _display_path(path: Path, project_root: Path) -> str:
    try:
        return str(path.resolve().relative_to(project_root.resolve()))
    except ValueError:
        return str(path.resolve())


def _resolve_include_path(raw_include: str, parent_file: Path, project_root: Path) -> Path:
    """Resolve a local include relative to the file that referenced it."""
    candidate = Path(raw_include.strip())
    if candidate.is_absolute():
        return candidate.resolve()
    beside_parent = (parent_file.parent / candidate).resolve()
    if beside_parent.is_file():
        return beside_parent
    from_root = (project_root / candidate).resolve()
    if from_root.is_file():
        return from_root
    return beside_parent


def _include_path_literals_in_text(content: str) -> set[str]:  # pylint: disable=too-many-branches
    """Paths the preprocessor would treat as user-intent includes (not in code spans)."""
    paths: set[str] = set()
    code_spans = _extract_code_spans(content)

    for match in _INCLUDE_BODY_RE.finditer(content):
        if _intersects_any_span(match.start(), match.end(), code_spans):
            continue
        attrs_str = match.group(1) or ""
        body = match.group(2) or ""
        attrs = _parse_attrs(attrs_str)
        path_value = (attrs.get("path") or body).strip()
        if path_value and "${" not in path_value:
            paths.add(path_value)

    for match in _INCLUDE_SELF_CLOSING_RE.finditer(content):
        if _intersects_any_span(match.start(), match.end(), code_spans):
            continue
        attrs = _parse_attrs(match.group(1) or "")
        path_value = (attrs.get("path") or "").strip()
        if path_value and "${" not in path_value:
            paths.add(path_value)

    for match in _BACKTICK_INCLUDE_RE.finditer(content):
        if _intersects_any_span(match.start(), match.end(), code_spans):
            continue
        path_value = match.group(1).strip()
        if path_value and "${" not in path_value:
            paths.add(path_value)

    for match in re.finditer(
        r"<include-many(?:\s+[^>]*?)?>(.*?)</include-many>",
        content,
        flags=re.DOTALL,
    ):
        if _intersects_any_span(match.start(), match.end(), code_spans):
            continue
        inner = match.group(1)
        for part in inner.splitlines():
            for item in part.split(","):
                stripped = item.strip()
                if stripped and "${" not in stripped:
                    paths.add(stripped)

    return paths


def _include_paths_for_file(file_path: Path) -> set[str]:
    """Union sync_order XML grammar with backtick/include-many user-intent paths."""
    try:
        content = file_path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return set()
    paths = set(extract_includes_from_file(file_path))
    paths |= _include_path_literals_in_text(content)
    paths |= compute_user_intent_paths(content)
    return paths


def _existing_file_records(
    paths: Iterable[str | Path],
    project_root: Path,
) -> list[dict[str, str]]:
    records: list[dict[str, str]] = []
    seen: set[Path] = set()
    for raw_path in paths:
        candidate = Path(raw_path)
        if not candidate.is_absolute():
            candidate = project_root / candidate
        candidate = candidate.resolve()
        if candidate in seen or not candidate.is_file():
            continue
        seen.add(candidate)
        records.append(
            {
                "path": _display_path(candidate, project_root),
                "sha256": _sha256_file(candidate),
            }
        )
    return records


def _include_tag_requests_compression(
    attrs: Mapping[str, str],
    include_path: Path,
    *,
    global_compress: bool,
) -> bool:
    """True when an include tag should be treated as compressed for evidence."""
    mode = (attrs.get("mode") or "").strip().lower()
    if mode == "compressed":
        return True
    if mode in ("full", "interface"):
        return False
    if global_compress and include_path.suffix.lower() == ".py":
        return True
    return False


def _include_uses_compressed_mode(
    parent_content: str,
    include_path: Path,
    parent_file: Path,
    project_root: Path,
    *,
    global_compress: bool = False,
) -> bool:
    """True when *parent_content* references *include_path* with compression active."""
    parent_text = parent_content
    code_spans = _extract_code_spans(parent_text)
    for match in _INCLUDE_BODY_RE.finditer(parent_text):
        if _intersects_any_span(match.start(), match.end(), code_spans):
            continue
        attrs = _parse_attrs(match.group(1) or "")
        body = (match.group(2) or "").strip()
        path_value = (attrs.get("path") or body).strip()
        if not path_value:
            continue
        resolved = _resolve_include_path(path_value, parent_file, project_root)
        if resolved.resolve() != include_path.resolve():
            continue
        if _include_tag_requests_compression(
            attrs, include_path, global_compress=global_compress
        ):
            return True
    for match in _INCLUDE_SELF_CLOSING_RE.finditer(parent_text):
        if _intersects_any_span(match.start(), match.end(), code_spans):
            continue
        attrs = _parse_attrs(match.group(1) or "")
        path_value = (attrs.get("path") or "").strip()
        if not path_value:
            continue
        resolved = _resolve_include_path(path_value, parent_file, project_root)
        if resolved.resolve() != include_path.resolve():
            continue
        if _include_tag_requests_compression(
            attrs, include_path, global_compress=global_compress
        ):
            return True
    return False


def _compressed_include_evidence_text(source_text: str, include_path: Path) -> str:
    """Compressed bytes for evidence metadata (matches preprocess compression)."""
    from pdd.content_selector import apply_compressed_include_with_fallback

    return apply_compressed_include_with_fallback(
        source_text,
        file_path=str(include_path),
    )


def _prompt_include_records(
    prompt_path: Path,
    project_root: Path,
    *,
    global_compress: bool = False,
) -> list[dict[str, Any]]:
    """Collect hashes for reachable local includes using production include grammar."""
    records: list[dict[str, Any]] = []
    seen: set[Path] = set()

    def walk(file_path: Path) -> None:
        try:
            parent_content = file_path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            parent_content = ""
        for raw_include in sorted(_include_paths_for_file(file_path)):
            include_path = _resolve_include_path(raw_include, file_path, project_root)
            if include_path in seen or not include_path.is_file():
                continue
            seen.add(include_path)
            source_hash = _sha256_file(include_path)
            record: dict[str, Any] = {
                "path": _display_path(include_path, project_root),
                "sha256": source_hash,
            }
            if _include_uses_compressed_mode(
                parent_content,
                include_path,
                file_path,
                project_root,
                global_compress=global_compress,
            ):
                try:
                    source_text = include_path.read_text(encoding="utf-8")
                    compressed_text = _compressed_include_evidence_text(
                        source_text,
                        include_path,
                    )
                    record["source_sha256"] = source_hash
                    record["compressed_sha256"] = _sha256_bytes(
                        compressed_text.encode("utf-8")
                    )
                    record["estimated_tokens"] = math.ceil(len(compressed_text) / 4)
                except Exception:  # pylint: disable=broad-exception-caught
                    record["source_sha256"] = source_hash
            records.append(record)
            walk(include_path)

    walk(prompt_path)
    return records


def _preprocessed_expanded_sha256(
    content: str,
    project_root: Path,
    *,
    compress: bool = False,
) -> Optional[str]:
    """Hash of prompt text after the same deterministic include expansion as generation."""
    if _has_active_tag(_UNSUPPORTED_EXPANSION_RE, content) or _has_active_tag(
        _NONDETERMINISTIC_TAG_RE, content
    ):
        return None
    try:
        with _project_cwd(project_root):
            expanded = preprocess(
                content,
                recursive=True,
                double_curly_brackets=False,
                compress=compress,
            )
    except Exception:  # pylint: disable=broad-exception-caught
        return None
    return _sha256_bytes(expanded.encode("utf-8"))


def _prompt_record(
    prompt_file: Optional[str | Path],
    project_root: Path,
    *,
    compress: bool = False,
) -> dict[str, Any]:
    if not prompt_file:
        return {
            "path": None,
            "sha256": None,
            "expanded_sha256": None,
            "uses_nondeterministic_tags": False,
        }
    path = Path(prompt_file)
    if not path.is_absolute():
        path = project_root / path
    if not path.is_file():
        return {
            "path": _display_path(path, project_root),
            "sha256": None,
            "expanded_sha256": None,
            "uses_nondeterministic_tags": False,
        }
    content = path.read_text(encoding="utf-8")
    nondeterministic = _has_active_tag(_NONDETERMINISTIC_TAG_RE, content)
    return {
        "path": _display_path(path, project_root),
        "sha256": _sha256_bytes(content.encode("utf-8")),
        "expanded_sha256": _preprocessed_expanded_sha256(
            content, project_root, compress=compress
        ),
        "uses_nondeterministic_tags": nondeterministic,
    }


def _prompt_has_contract_rules(prompt_path: Path) -> bool:
    """True when the prompt file declares a contract_rules section."""
    try:
        content = prompt_path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return False
    return bool(_CONTRACT_RULES_RE.search(content))


def _contract_statuses(  # pylint: disable=too-many-return-statements
    prompt_file: Optional[str | Path],
) -> dict[str, Any]:
    if not prompt_file:
        return {"status": "not_applicable", "rules": {}}
    path = Path(prompt_file)
    if not path.is_file():
        return {"status": "not_available", "rules": {}}
    if not _prompt_has_contract_rules(path):
        return {"status": "not_applicable", "rules": {}}
    try:
        from .coverage_contracts import build_coverage  # pylint: disable=import-outside-toplevel
    except ImportError:
        return {"status": "not_available", "rules": {}}
    try:
        result = build_coverage(path)
    except Exception:  # pylint: disable=broad-exception-caught
        return {"status": "not_available", "rules": {}}
    if not result.has_contract_rules:
        return {"status": "not_applicable", "rules": {}}
    return {
        "status": "available",
        "rules": {
            rule.rule_id: {
                "status": rule.status,
                "stories": rule.stories,
                "tests": rule.tests,
                "waiver": rule.waiver,
                "waiver_status": getattr(rule, "waiver_status", None),
                "waiver_expires": getattr(rule, "waiver_expires", None),
            }
            for rule in result.rules
        },
        "waivers": [
            {
                "id": waiver.raw_id,
                "rule_id": waiver.rule_id,
                "reason": waiver.reason,
                "approved_by": waiver.approved_by,
                "expires": waiver.expires.isoformat() if waiver.expires else None,
            }
            for waiver in parse_prompt_contracts(path).waivers
        ],
    }


def resolve_generate_output_paths(
    prompt_file: str | Path,
    *,
    output: Optional[str] = None,
    context_override: Optional[str] = None,
    force: bool = True,
    quiet: bool = True,
) -> list[str]:
    """Resolve default or explicit generate output paths via construct_paths."""
    from .construct_paths import construct_paths  # pylint: disable=import-outside-toplevel

    command_options: dict[str, Any] = {}
    if output is not None:
        command_options["output"] = output
    _, _, output_file_paths, _language = construct_paths(
        input_file_paths={"prompt_file": str(prompt_file)},
        force=force,
        quiet=quiet,
        command="generate",
        command_options=command_options or None,
        context_override=context_override,
    )
    resolved = output_file_paths.get("output")
    return [str(resolved)] if resolved else []


def resolve_test_output_paths(  # pylint: disable=too-many-arguments
    prompt_file: str | Path,
    code_file: str | Path,
    *,
    output: Optional[str] = None,
    language: Optional[str] = None,
    context_override: Optional[str] = None,
    force: bool = True,
    quiet: bool = True,
) -> list[str]:
    """Resolve manual test output paths the same way cmd_test_main does."""
    from .construct_paths import construct_paths  # pylint: disable=import-outside-toplevel

    command_options: dict[str, Any] = {}
    if output is not None:
        command_options["output"] = output
    if language is not None:
        command_options["language"] = language
    _, _, output_file_paths, _language = construct_paths(
        input_file_paths={
            "prompt_file": str(prompt_file),
            "code_file": str(code_file),
        },
        force=force,
        quiet=quiet,
        command="test",
        command_options=command_options or None,
        context_override=context_override,
    )
    resolved = output_file_paths.get("output")
    return [str(resolved)] if resolved else []


def _safe_slug(value: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9_.-]+", "-", value).strip("-")
    return slug or "run"


def _dynamic_artifact_records(
    artifacts: Iterable[Mapping[str, Any]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    """Summarize captured shell, web, and query-include snapshot artifacts."""

    shell_records: list[dict[str, Any]] = []
    web_records: list[dict[str, Any]] = []
    query_records: list[dict[str, Any]] = []
    for artifact in artifacts:
        artifact_type = str(artifact.get("type") or "")
        path = artifact.get("path")
        digest = artifact.get("sha256")
        if not isinstance(path, str) or not isinstance(digest, str):
            continue
        record: dict[str, Any] = {"path": path, "sha256": digest}
        metadata = artifact.get("metadata")
        if isinstance(metadata, Mapping):
            record["metadata"] = dict(metadata)
        if artifact.get("redaction_applied"):
            record["redaction_applied"] = True
        if artifact_type == "shell":
            shell_records.append(record)
        elif artifact_type == "web":
            web_records.append(record)
        elif artifact_type == "query_include":
            query_records.append(record)
    return shell_records, web_records, query_records


def devunit_slug_for_prompt(prompt_path: str | Path) -> Optional[str]:
    """Return the devunit evidence filename slug for a prompt (matches latest manifests).

    Uses :func:`infer_module_identity` for path-qualified basenames (e.g.
    ``frontend/page`` for ``prompts/frontend/page_python.prompt``), then applies
    the same :func:`_safe_slug` normalization as :func:`write_evidence_manifest`.
    """
    path = Path(prompt_path)
    from .operation_log import infer_module_identity  # pylint: disable=import-outside-toplevel

    basename, _language = infer_module_identity(path)
    if not basename:
        basename = path.stem or None
    if not basename:
        return None
    return _safe_slug(basename)


def validation_from_sync(
    sync_result: Mapping[str, Any],
    *,
    skip_tests: bool,
    skip_verify: bool,
    dry_run: bool = False,
) -> dict[str, str]:
    """Map ``sync_main`` results to manifest validation fields without inventing outcomes."""
    validation: dict[str, str] = {
        "detect_stories": "not_applicable",
        "unit_tests": "not_applicable" if skip_tests else "not_available",
        "verify": "not_applicable" if skip_verify else "not_available",
    }
    if dry_run:
        return validation

    by_language = sync_result.get("results_by_language")
    if not isinstance(by_language, dict):
        by_language = {"_": sync_result}

    operations: set[str] = set()
    for lang_result in by_language.values():
        if not isinstance(lang_result, dict):
            continue
        for operation in lang_result.get("operations_completed") or []:
            operations.add(str(operation))

    lang_successes = [
        bool(lang_result.get("success"))
        for lang_result in by_language.values()
        if isinstance(lang_result, dict) and "success" in lang_result
    ]
    if lang_successes:
        # Prefer per-language outcomes over a stale top-level overall_success flag.
        overall_success = all(lang_successes)
    elif sync_result.get("overall_success") is not None:
        overall_success = bool(sync_result.get("overall_success"))
    else:
        overall_success = False

    test_operations = {"test", "crash", "fix", "test_extend"}
    if not skip_tests and operations & test_operations:
        validation["unit_tests"] = "passed" if overall_success else "failed"

    if not skip_verify:
        if "verify" in operations:
            validation["verify"] = "passed" if overall_success else "failed"
        elif any(operation.startswith("skip:verify") for operation in operations):
            validation["verify"] = "not_applicable"

    return validation


def collect_sync_evidence_paths(
    basename: str,
    sync_result: Mapping[str, Any],
    *,
    project_root: Path | str | None = None,
) -> tuple[Optional[Path], list[Path]]:
    """Resolve prompt and generated output paths for a completed ``pdd sync`` run."""
    from .sync_determine_operation import get_pdd_file_paths  # pylint: disable=import-outside-toplevel

    root = Path(project_root or Path.cwd()).resolve()
    by_language = sync_result.get("results_by_language")
    if not isinstance(by_language, dict):
        by_language = {"python": sync_result}

    languages = [lang for lang in by_language if lang != "_"]
    language = languages[0] if len(languages) == 1 else "python"

    try:
        pdd_files = get_pdd_file_paths(basename, language, str(root / "prompts"))
    except Exception:  # pylint: disable=broad-except
        return None, []

    prompt = pdd_files.get("prompt")
    outputs: list[Path] = []
    for key in ("code", "test", "example"):
        candidate = pdd_files.get(key)
        if candidate is not None and candidate.is_file():
            outputs.append(candidate.resolve())
    prompt_path = prompt.resolve() if prompt is not None and prompt.is_file() else None
    return prompt_path, outputs



def grounding_kwargs_from_ctx(
    ctx_obj: Optional[Mapping[str, Any]] = None,
) -> dict[str, Any]:
    """Build write_evidence_manifest grounding kwargs from a Click ctx.obj mapping."""
    obj = dict(ctx_obj or {})
    grounding = obj.get("last_grounding")
    examples_used = None
    if isinstance(grounding, Mapping):
        examples_used = grounding.get("selected_examples")
    reviewed = grounding_reviewed_for_manifest(obj, examples_used)
    return {"grounding": grounding, "reviewed": reviewed}


_SENSITIVE_METADATA_KEYS = {
    "content",
    "compressed_content",
    "compressed_context",
    "context",
    "prompt",
    "raw",
    "raw_context",
    "rendered",
    "rendered_context",
    "text",
}


def _safe_generation_metadata(value: Any) -> Any:
    """Copy generation metadata while omitting raw prompt/context payload fields."""
    if isinstance(value, Mapping):
        safe: dict[str, Any] = {}
        for key, item in value.items():
            key_str = str(key)
            if key_str.lower() in _SENSITIVE_METADATA_KEYS:
                continue
            safe[key_str] = _safe_generation_metadata(item)
        return safe
    if isinstance(value, (list, tuple)):
        return [_safe_generation_metadata(item) for item in value]
    if isinstance(value, (str, int, float, bool)) or value is None:
        return value
    return str(value)



def write_evidence_manifest(  # pylint: disable=too-many-arguments,too-many-locals
    *,
    command: str,
    prompt_file: Optional[str | Path] = None,
    output_files: Iterable[str | Path] = (),
    model: str = "",
    cost_usd: float = 0.0,
    temperature: Optional[float] = None,
    validation: Optional[Mapping[str, str]] = None,
    logs: Optional[Mapping[str, Optional[str]]] = None,
    basename: Optional[str] = None,
    project_root: Optional[str | Path] = None,
    context_snapshot: Optional[Mapping[str, Any]] = None,
    grounding: Optional[Mapping[str, Any]] = None,
    reviewed: bool = False,
    compression: Optional[Mapping[str, Any]] = None,
    agentic_fallback: Optional[Mapping[str, Any]] = None,
    story_detection: Optional[Mapping[str, Any]] = None,
    compress: bool = False,
) -> Path:
    """Write a versioned evidence manifest and the dev-unit latest copy."""
    root = Path(project_root or Path.cwd()).resolve()
    if not prompt_file and basename:
        prompts_root = root / "prompts"
        direct = list(prompts_root.glob(f"{basename}_*.prompt"))
        fallback = list(prompts_root.rglob(f"{Path(basename).name}_*.prompt"))
        candidates = direct or fallback
        if len(candidates) == 1:
            prompt_file = candidates[0]
    prompt = _prompt_record(prompt_file, root, compress=compress)
    prompt_path = None
    if prompt_file:
        prompt_path = Path(prompt_file)
        if not prompt_path.is_absolute():
            prompt_path = root / prompt_path
    resolved_from_prompt = False
    if basename is None and prompt_path is not None:
        slug = devunit_slug_for_prompt(prompt_path)
        if slug:
            basename = slug
            resolved_from_prompt = True
    if basename is None:
        basename = _safe_slug(command.replace("pdd ", "", 1))
    elif not resolved_from_prompt:
        basename = _safe_slug(basename)

    timestamp = datetime.now(timezone.utc)
    run_id = f"{timestamp.strftime('%Y%m%dT%H%M%S%fZ')}-{basename}"
    log_values: dict[str, Optional[str]] = {
        "core_dump": None,
        "verify_results": None,
        "cost_csv": None,
    }
    if logs:
        log_values.update(logs)

    snapshot_context = dict(context_snapshot or {})
    snapshot_expanded = snapshot_context.get("expanded_prompt")
    if isinstance(snapshot_expanded, Mapping) and isinstance(snapshot_expanded.get("sha256"), str):
        prompt["expanded_sha256"] = snapshot_expanded["sha256"]
    if snapshot_context.get("uses_nondeterministic_context") is not None:
        prompt["uses_nondeterministic_tags"] = bool(
            snapshot_context.get("uses_nondeterministic_context")
        )

    artifacts = list(snapshot_context.get("artifacts") or [])
    shell_snapshots, web_snapshots, query_snapshots = _dynamic_artifact_records(artifacts)
    grounding_block = normalize_grounding(grounding, reviewed=reviewed)
    snapshot_grounding = list(snapshot_context.get("grounding_examples") or [])
    grounding_examples = list(grounding_block.get("selected_examples") or []) or snapshot_grounding

    manifest: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "run": {
            "id": run_id,
            "command": command,
            "pdd_version": get_version(),
            "timestamp": timestamp.isoformat().replace("+00:00", "Z"),
        },
        "prompt": prompt,
        "context": {
            "includes": (
                _prompt_include_records(prompt_path, root, global_compress=compress)
                if prompt_path
                else []
            ),
            "web_snapshots": web_snapshots,
            "shell_snapshots": shell_snapshots,
            "query_snapshots": query_snapshots,
        },
        "generation": {
            "model": model or None,
            "temperature": temperature,
            "cost_usd": float(cost_usd),
            "grounding": grounding_block,
            "grounding_examples": grounding_examples,
        },
        "outputs": _existing_file_records(output_files, root),
        "contracts": _contract_statuses(prompt_path),
        "validation": {
            "detect_stories": "not_available",
            "unit_tests": "not_available",
            "verify": "not_available",
            **dict(validation or {}),
        },
        "logs": log_values,
    }
    if compression is not None:
        manifest["generation"]["compression"] = _safe_generation_metadata(compression)
    if agentic_fallback is not None:
        manifest["generation"]["agentic_fallback"] = _safe_generation_metadata(agentic_fallback)
    if story_detection is not None:
        # The structured detector document is the single source for story status,
        # scope, cost, and invocation binding. Evidence embeds it verbatim rather
        # than independently reconstructing those semantics.
        manifest["story_detection"] = dict(story_detection)
    if snapshot_context:
        manifest["context_snapshot"] = {
            "enabled": True,
            "manifest_path": snapshot_context.get("manifest_path"),
            "snapshot_dir": snapshot_context.get("snapshot_dir"),
            "expanded_prompt": snapshot_expanded,
            "expanded_prompt_path": (
                snapshot_expanded.get("path")
                if isinstance(snapshot_expanded, Mapping)
                else None
            ),
            "expanded_sha256": (
                snapshot_expanded.get("sha256")
                if isinstance(snapshot_expanded, Mapping)
                else None
            ),
            "uses_nondeterministic_context": bool(
                snapshot_context.get("uses_nondeterministic_context")
            ),
            "dynamic_tags": list(snapshot_context.get("dynamic_tags") or []),
            "declared_dynamic_tags": list(snapshot_context.get("declared_dynamic_tags") or []),
            "redaction_applied": bool(snapshot_context.get("redaction_applied")),
            "redaction": snapshot_context.get("redaction"),
            "artifacts": artifacts,
            "run_id": snapshot_context.get("run_id"),
        }

    runs_dir = root / ".pdd" / "evidence" / "runs"
    latest_dir = root / ".pdd" / "evidence" / "devunits"
    runs_dir.mkdir(parents=True, exist_ok=True)
    latest_dir.mkdir(parents=True, exist_ok=True)
    run_path = runs_dir / f"{run_id}.json"
    latest_path = latest_dir / f"{basename}.latest.json"
    payload = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    run_path.write_text(payload, encoding="utf-8")
    latest_path.write_text(payload, encoding="utf-8")
    return run_path
