"""Routine, machine-readable audit receipts for PDD command runs."""
from __future__ import annotations

import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping, Optional

from . import get_version
from .coverage_contracts import build_coverage
from .operation_log import infer_module_identity

SCHEMA_VERSION = 1
_NONDETERMINISTIC_TAG_RE = re.compile(r"<(?:shell|web)\b", re.IGNORECASE)
_UNSUPPORTED_EXPANSION_RE = re.compile(
    r"<(?:shell|web|include-many)\b|<include[^>]*(?:query|select)\s*=|\$\{",
    re.IGNORECASE,
)
_INCLUDE_RE = re.compile(
    r"<include(?:\s+[^>]*?)?>(.*?)</include>|```<([^>\n]+)>```",
    re.DOTALL | re.IGNORECASE,
)
_CONTRACT_RULES_RE = re.compile(r"<contract_rules\b", re.IGNORECASE)


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
    """Collect hashes for all reachable local includes (nested), without executing tags."""
    try:
        content = prompt_path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return []

    records: list[dict[str, str]] = []
    seen: set[Path] = set()

    def walk(file_path: Path, file_content: str) -> None:
        for match in _INCLUDE_RE.finditer(file_content):
            raw_include = (match.group(1) or match.group(2) or "").strip()
            if not raw_include or "${" in raw_include:
                continue
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
            try:
                nested_content = include_path.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError):
                continue
            walk(include_path, nested_content)

    walk(prompt_path, content)
    return records


def _deterministic_expanded_hash(
    content: str,
    prompt_path: Path,
    project_root: Path,
) -> Optional[str]:
    """Expand plain local includes only; resolve each include from its parent file."""

    def expand_file(file_content: str, file_path: Path) -> Optional[str]:
        if _UNSUPPORTED_EXPANSION_RE.search(file_content):
            return None
        expanded = file_content
        for _ in range(25):
            changed = False

            def replace(match: re.Match[str]) -> str:
                nonlocal changed
                raw_include = (match.group(1) or match.group(2) or "").strip()
                if not raw_include or "${" in raw_include:
                    return match.group(0)
                include_path = _resolve_include_path(raw_include, file_path, project_root)
                if not include_path.is_file():
                    return match.group(0)
                try:
                    nested_content = include_path.read_text(encoding="utf-8")
                except (OSError, UnicodeDecodeError):
                    return match.group(0)
                nested_expanded = expand_file(nested_content, include_path)
                if nested_expanded is None:
                    return match.group(0)
                changed = True
                return nested_expanded

            expanded = _INCLUDE_RE.sub(replace, expanded)
            if not changed:
                return expanded
        return None

    expanded_text = expand_file(content, prompt_path)
    if expanded_text is None:
        return None
    return _sha256_bytes(expanded_text.encode("utf-8"))


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
    nondeterministic = bool(_NONDETERMINISTIC_TAG_RE.search(content))
    return {
        "path": _display_path(path, project_root),
        "sha256": _sha256_bytes(content.encode("utf-8")),
        "expanded_sha256": _deterministic_expanded_hash(content, path, project_root),
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
        result = build_coverage(path)
    except Exception:  # pylint: disable=broad-exception-caught
        # Evidence enrichment must not make an otherwise valid run fail.
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


def _safe_slug(value: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9_.-]+", "-", value).strip("-")
    return slug or "run"


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
            "web_snapshots": [],
            "shell_snapshots": [],
        },
        "generation": {
            "model": model or None,
            "temperature": temperature,
            "cost_usd": float(cost_usd),
            "grounding_examples": [],
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
