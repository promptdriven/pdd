from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional

from rich.console import Console

_console = Console()


@dataclass
class MetadataReport:
    basename: str
    language: str
    paths: Dict[str, Any]
    files_present: Dict[str, bool]
    fingerprint_state: str
    run_report_state: str
    stale_components: List[str] = field(default_factory=list)
    wrote_fingerprint: bool = False
    cleared_run_report: bool = False
    warnings: List[str] = field(default_factory=list)
    dry_run: bool = False


def _infer_basename_and_language(
    target: str,
    language: Optional[str],
    prompts_dir: str,
) -> tuple[str, str]:
    """Infer basename and language from a target string.

    target may be: a bare basename, a prompt path (e.g. prompts/foo_python.prompt),
    or a code/example/test file path.
    """
    from .sync_determine_operation import get_extension  # noqa: F401

    p = Path(target)
    name = p.name

    # Try prompt file pattern: <basename>_<language>.prompt
    if name.endswith(".prompt"):
        stem = name[: -len(".prompt")]
        if "_" in stem:
            base, lang = stem.rsplit("_", 1)
            return base, language or lang
        # No language suffix; use language arg or fallback
        if language:
            return stem, language
        return stem, _default_language_from_pddrc()

    # Code / example / test file: try to strip extension and known prefixes/suffixes.
    if p.suffix:
        stem = p.stem
        # Strip example_ / test_ prefixes
        basename = stem
        if basename.startswith("test_"):
            basename = basename[len("test_") :]
        elif basename.startswith("example_"):
            basename = basename[len("example_") :]
        # Infer language from extension if not given
        lang = language or _language_from_extension(p.suffix.lstrip("."))
        if not lang:
            lang = _default_language_from_pddrc()
        return basename, lang

    # Bare basename
    lang = language or _default_language_from_pddrc()
    return target, lang


def _language_from_extension(ext: str) -> Optional[str]:
    """Best-effort reverse mapping from file extension to language."""
    from .sync_determine_operation import get_extension

    # Try common languages
    candidates = [
        "python", "javascript", "typescript", "java", "cpp", "c",
        "go", "rust", "ruby", "php", "csharp", "swift", "kotlin",
        "scala", "bash", "shell", "html", "css", "sql",
    ]
    target_ext = "." + ext
    for lang in candidates:
        try:
            if get_extension(lang) == target_ext:
                return lang
        except Exception:
            continue
    return None


def _default_language_from_pddrc() -> str:
    """Fall back to .pddrc default_language or 'python'."""
    try:
        from .pddrc_loader import load_pddrc  # type: ignore
        cfg = load_pddrc()
        if isinstance(cfg, dict):
            lang = cfg.get("default_language")
            if lang:
                return str(lang)
    except Exception:
        pass
    # Try construct_paths-based resolution
    try:
        from . import construct_paths  # noqa: F401
    except Exception:
        pass
    return "python"


def _check_files_present(paths: Dict[str, Any]) -> Dict[str, bool]:
    present: Dict[str, bool] = {}
    for key, val in paths.items():
        if val is None:
            present[key] = False
            continue
        if key == "test_files" and isinstance(val, list):
            if not val:
                present[key] = False
            else:
                present[key] = all(Path(p).exists() for p in val)
        elif isinstance(val, (list, tuple)):
            present[key] = bool(val) and all(Path(p).exists() for p in val)
        else:
            try:
                present[key] = Path(val).exists()
            except TypeError:
                present[key] = False
    return present


def _compute_stale_components(
    fingerprint: Any,
    current_hashes: Dict[str, Any],
    files_present: Dict[str, bool],
) -> List[str]:
    """Determine which components have hashes that diverge from the fingerprint."""
    if fingerprint is None:
        return []

    stale: List[str] = []

    hash_field_map = {
        "prompt": "prompt_hash",
        "code": "code_hash",
        "example": "example_hash",
        "test": "test_hash",
    }

    for component, fp_field in hash_field_map.items():
        # Skip if file isn't present (missing != stale)
        present_key = component if component in files_present else (
            "test_files" if component == "test" else component
        )
        if not files_present.get(present_key, False) and component != "test":
            continue
        stored = getattr(fingerprint, fp_field, None)
        current = current_hashes.get(fp_field)
        if component == "test" and not files_present.get("test", files_present.get("test_files", False)):
            # No tests present; skip
            continue
        if stored is None and current is None:
            continue
        if stored != current:
            stale.append(component)

    # Compare test_files dict (Bug #156)
    stored_test_files = getattr(fingerprint, "test_files", None) or {}
    current_test_files = current_hashes.get("test_files") or {}
    if stored_test_files or current_test_files:
        if stored_test_files != current_test_files:
            if "test" not in stale:
                stale.append("test")

    return stale


def _compute_run_report_state(
    fingerprint: Any,
    run_report: Any,
    current_hashes: Dict[str, Any],
    stale_components: List[str],
) -> str:
    # Bug #23: skip: commands mean the user opted out of tests — supersedes "missing".
    if fingerprint is not None:
        cmd = getattr(fingerprint, "command", "") or ""
        if cmd.startswith("skip:"):
            return "skipped"

    if run_report is None:
        return "missing"

    # If prompt/code/example are stale, run report no longer reflects current sources
    for comp in ("prompt", "code", "example"):
        if comp in stale_components:
            return "stale"

    # Compare test hashes
    rr_test_hash = getattr(run_report, "test_hash", None)
    rr_test_files = getattr(run_report, "test_files", None) or {}
    cur_test_hash = current_hashes.get("test_hash")
    cur_test_files = current_hashes.get("test_files") or {}

    if rr_test_files or cur_test_files:
        if rr_test_files != cur_test_files:
            return "stale"
    elif rr_test_hash is not None or cur_test_hash is not None:
        if rr_test_hash != cur_test_hash:
            return "stale"

    return "current"


def finalize_metadata(
    target: str,
    language: Optional[str] = None,
    prompts_dir: str = "prompts",
    context_override: Optional[str] = None,
    dry_run: bool = False,
) -> MetadataReport:
    """Finalize and audit `.pdd/meta/` fingerprint and run-report state for a dev unit."""
    # Lazy imports to avoid circulars and heavy deps at import time.
    from .sync_determine_operation import (
        SyncLock,
        calculate_current_hashes,
        get_pdd_file_paths,
        read_fingerprint,
        read_run_report,
    )
    from . import operation_log

    if not target or not isinstance(target, str):
        raise ValueError("finalize_metadata: 'target' must be a non-empty string")

    try:
        basename, resolved_language = _infer_basename_and_language(
            target, language, prompts_dir
        )
    except Exception as e:
        raise ValueError(f"Could not resolve basename/language from target '{target}': {e}") from e

    if not basename:
        raise ValueError(f"Could not resolve basename from target '{target}'")
    if not resolved_language:
        raise ValueError(f"Could not detect language for target '{target}'")

    warnings: List[str] = []

    # Resolve PDD paths
    try:
        paths = get_pdd_file_paths(
            basename, resolved_language, prompts_dir, context_override=context_override
        )
    except Exception as e:
        raise ValueError(
            f"Failed to resolve PDD file paths for '{basename}' ({resolved_language}): {e}"
        ) from e

    # Read fingerprint (handle malformed JSON gracefully)
    fingerprint = None
    try:
        fingerprint = read_fingerprint(basename, resolved_language)
    except (json.JSONDecodeError, ValueError) as e:
        warnings.append(f"Fingerprint unreadable: {e}")
    except Exception as e:
        warnings.append(f"Error reading fingerprint: {e}")

    # Read run report
    run_report = None
    try:
        run_report = read_run_report(basename, resolved_language)
    except (json.JSONDecodeError, ValueError) as e:
        warnings.append(f"Run report unreadable: {e}")
    except Exception as e:
        warnings.append(f"Error reading run report: {e}")

    # Compute current hashes
    stored_include_deps = (
        getattr(fingerprint, "include_deps", None) if fingerprint else None
    )
    try:
        current_hashes = calculate_current_hashes(
            paths, stored_include_deps=stored_include_deps
        )
    except Exception as e:
        warnings.append(f"Error computing current hashes: {e}")
        current_hashes = {}

    files_present = _check_files_present(paths)

    # Note missing files in warnings (informational)
    for key, present in files_present.items():
        if not present and key in ("prompt", "code"):
            warnings.append(f"Missing file: {key}")

    # Compute stale components
    stale_components = _compute_stale_components(fingerprint, current_hashes, files_present)

    # Determine fingerprint state
    if fingerprint is None:
        fingerprint_state = "missing"
    elif not stale_components:
        fingerprint_state = "current"
    else:
        fingerprint_state = "stale"

    # Determine run report state
    run_report_state = _compute_run_report_state(
        fingerprint, run_report, current_hashes, stale_components
    )

    report = MetadataReport(
        basename=basename,
        language=resolved_language,
        paths={k: (str(v) if isinstance(v, Path) else v) for k, v in paths.items()},
        files_present=files_present,
        fingerprint_state=fingerprint_state,
        run_report_state=run_report_state,
        stale_components=stale_components,
        wrote_fingerprint=False,
        cleared_run_report=False,
        warnings=warnings,
        dry_run=dry_run,
    )

    if dry_run:
        # Read-only audit: never touch disk. SyncLock does not currently support
        # log_mode=True, so we simply skip locking — the report is purely an
        # in-memory snapshot.
        return report

    # Non-dry-run: acquire lock and perform writes.
    lock = SyncLock(basename, resolved_language)
    with lock:
        prompt_present = files_present.get("prompt", False)
        if not prompt_present:
            report.warnings.append(
                "Skipping fingerprint write because prompt file is missing"
            )
        else:
            try:
                operation_log.save_fingerprint(
                    basename=basename,
                    language=resolved_language,
                    operation="metadata-finalize",
                    paths=paths,
                )
                report.wrote_fingerprint = True
            except Exception as e:
                report.warnings.append(f"Failed to write fingerprint: {e}")

        if run_report_state == "stale":
            try:
                operation_log.clear_run_report(basename, resolved_language)
                report.cleared_run_report = True
            except Exception as e:
                report.warnings.append(f"Failed to clear stale run report: {e}")

    return report