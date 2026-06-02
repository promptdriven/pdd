"""Routine, machine-readable audit receipts for PDD command runs."""
from __future__ import annotations

import hashlib
import json
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
from .sync_order import extract_includes_from_file

SCHEMA_VERSION = 1
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


def _prompt_include_records(prompt_path: Path, project_root: Path) -> list[dict[str, str]]:
    """Collect hashes for reachable local includes using production include grammar."""
    records: list[dict[str, str]] = []
    seen: set[Path] = set()

    def walk(file_path: Path) -> None:
        for raw_include in sorted(_include_paths_for_file(file_path)):
            include_path = _resolve_include_path(raw_include, file_path, project_root)
            if include_path in seen or not include_path.is_file():
                continue
            seen.add(include_path)
            records.append(
                {
                    "path": _display_path(include_path, project_root),
                    "sha256": _sha256_file(include_path),
                }
            )
            walk(include_path)

    walk(prompt_path)
    return records


def _preprocessed_expanded_sha256(content: str, project_root: Path) -> Optional[str]:
    """Hash of prompt text after the same deterministic include expansion as generation."""
    if _has_active_tag(_UNSUPPORTED_EXPANSION_RE, content) or _has_active_tag(
        _NONDETERMINISTIC_TAG_RE, content
    ):
        return None
    try:
        with _project_cwd(project_root):
            expanded = preprocess(content, recursive=True, double_curly_brackets=False)
    except Exception:  # pylint: disable=broad-exception-caught
        return None
    return _sha256_bytes(expanded.encode("utf-8"))


def _prompt_record(prompt_file: Optional[str | Path], project_root: Path) -> dict[str, Any]:
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
        "expanded_sha256": _preprocessed_expanded_sha256(content, project_root),
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
            }
            for rule in result.rules
        },
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

    overall_success = sync_result.get("overall_success")
    if overall_success is None:
        successes = [
            bool(lang_result.get("success"))
            for lang_result in by_language.values()
            if isinstance(lang_result, dict)
        ]
        overall_success = bool(successes) and all(successes)

    test_operations = {"test", "crash", "fix", "test_extend"}
    if not skip_tests and operations & test_operations:
        validation["unit_tests"] = "passed" if overall_success else "failed"

    if not skip_verify:
        if "verify" in operations:
            validation["verify"] = "passed" if overall_success else "failed"
        elif any(operation.startswith("skip:verify") for operation in operations):
            validation["verify"] = "not_applicable"

    return validation


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
    prompt = _prompt_record(prompt_file, root)
    prompt_path = None
    if prompt_file:
        prompt_path = Path(prompt_file)
        if not prompt_path.is_absolute():
            prompt_path = root / prompt_path
    if basename is None and prompt_path:
        from .operation_log import infer_module_identity  # pylint: disable=import-outside-toplevel

        basename, _ = infer_module_identity(prompt_path)
        basename = basename or prompt_path.stem
    basename = _safe_slug(basename or command.replace("pdd ", "", 1))

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
    grounding_examples = list(snapshot_context.get("grounding_examples") or [])

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
            "includes": _prompt_include_records(prompt_path, root) if prompt_path else [],
            "web_snapshots": web_snapshots,
            "shell_snapshots": shell_snapshots,
            "query_snapshots": query_snapshots,
        },
        "generation": {
            "model": model or None,
            "temperature": temperature,
            "cost_usd": float(cost_usd),
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
