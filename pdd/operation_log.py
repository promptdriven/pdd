from __future__ import annotations

import functools
import json
import logging
import os
import re

import time
from datetime import datetime
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple, Union

from rich.console import Console

logger = logging.getLogger(__name__)

# We assume standard paths relative to the project root
PDD_DIR = ".pdd"
META_DIR = os.path.join(PDD_DIR, "meta")


def _detect_project_root(start: Optional[Path] = None) -> Optional[Path]:
    """Walk up from `start` (or CWD) to find the nearest .pddrc.

    Returns the directory containing the .pddrc, or None if no .pddrc is
    reachable upward. Used by the metadata helpers to anchor .pdd/meta at
    the subproject root rather than the run CWD when the two diverge.
    """
    base = (start or Path.cwd()).resolve()
    if base.is_file():
        base = base.parent
    for candidate in [base] + list(base.parents):
        if (candidate / ".pddrc").is_file():
            return candidate
    return None


def _detect_project_root_from_paths(
    paths: Optional[Dict[str, Any]],
) -> Optional[Path]:
    """Find a project root by walking up from each candidate file path.

    `paths` is the dict that flows through save_fingerprint / sync (keys
    like 'prompt', 'code', 'example', 'test'). When the .pddrc lives
    *below* the run CWD (a subproject), upward-from-CWD detection fails;
    walking up from a known file path inside the subproject succeeds.
    Returns the first reachable .pddrc directory.
    """
    if not paths:
        return None
    for candidate in paths.values():
        if not candidate:
            continue
        try:
            hint = Path(candidate)
        except TypeError:
            continue
        if not hint.exists():
            continue
        detected = _detect_project_root(hint)
        if detected is not None:
            return detected
    return None


def _resolve_meta_dir(
    project_root: Optional[Path] = None,
    paths: Optional[Dict[str, Any]] = None,
) -> Path:
    """Return the .pdd/meta directory.

    Resolution order:
      1. Explicit `project_root` argument
      2. .pddrc reachable upward from any path in `paths`
         (handles the case where the subproject lives BELOW run CWD)
      3. .pddrc reachable upward from CWD
      4. Run CWD (legacy)
    """
    if project_root is not None:
        return Path(project_root) / PDD_DIR / "meta"
    detected = _detect_project_root_from_paths(paths)
    if detected is None:
        detected = _detect_project_root()
        if detected is not None and detected == Path.cwd().resolve():
            detected = None
    if detected is not None:
        return detected / PDD_DIR / "meta"
    return Path(META_DIR)


def ensure_meta_dir(
    project_root: Optional[Path] = None,
    paths: Optional[Dict[str, Any]] = None,
) -> None:
    """Ensure the .pdd/meta directory exists.

    When project_root is supplied, creates .pdd/meta under that root.
    Otherwise auto-detects via `_resolve_meta_dir` (Issue #1211): tries
    upward from each path in `paths` first (so a subproject .pddrc BELOW
    run CWD is found), then walks up from CWD, then falls back to CWD.
    """
    os.makedirs(_resolve_meta_dir(project_root, paths=paths), exist_ok=True)


def _safe_basename(basename: str) -> str:
    """Sanitize basename for use in metadata filenames.

    Replaces '/' with '_' to prevent path interpretation when the basename
    contains subdirectory components (e.g., 'core/cloud' -> 'core_cloud').
    """
    return basename.replace('/', '_')


def get_log_path(
    basename: str,
    language: str,
    project_root: Optional[Path] = None,
    paths: Optional[Dict[str, Any]] = None,
) -> Path:
    """Get the path to the sync log for a specific module.

    Honors `project_root` if given; otherwise resolves the meta dir via
    upward .pddrc detection seeded by `paths` (Issue #1211).
    """
    ensure_meta_dir(project_root=project_root, paths=paths)
    return _resolve_meta_dir(project_root, paths=paths) / f"{_safe_basename(basename)}_{language}_sync.log"


def get_fingerprint_path(
    basename: str,
    language: str,
    project_root: Optional[Path] = None,
    paths: Optional[Dict[str, Any]] = None,
) -> Path:
    """Get the path to the fingerprint JSON file for a specific module.

    When `project_root` is supplied, returns a path under that root. When
    omitted, auto-detects via `_resolve_meta_dir` (Issue #1211): walks up
    from any file path in `paths` first (so a subproject .pddrc BELOW
    run CWD is found), then up from CWD, then falls back to CWD.
    """
    ensure_meta_dir(project_root=project_root, paths=paths)
    return _resolve_meta_dir(project_root, paths=paths) / f"{_safe_basename(basename)}_{language}.json"


def get_run_report_path(
    basename: str,
    language: str,
    project_root: Optional[Path] = None,
    paths: Optional[Dict[str, Any]] = None,
) -> Path:
    """Get the path to the run report file for a specific module.

    Same project-root resolution as get_fingerprint_path (Issue #1211).
    """
    ensure_meta_dir(project_root=project_root, paths=paths)
    return _resolve_meta_dir(project_root, paths=paths) / f"{_safe_basename(basename)}_{language}_run.json"


def infer_module_identity(prompt_file_path: Union[str, Path]) -> Tuple[Optional[str], Optional[str]]:
    """
    Infer basename and language from a prompt file path.

    Expected pattern: prompts/[subdir/...]/{filestem}_{language}.prompt

    Reconstructs directory context from the prompt path's position relative
    to the nearest ``prompts/`` ancestor directory so that basenames include
    subdirectory prefixes (e.g., ``frontend/page`` instead of just ``page``).
    This avoids fingerprint collisions when multiple files share the same
    filename stem.

    Args:
        prompt_file_path: Path to the prompt file.

    Returns:
        Tuple of (basename, language) or (None, None) if inference fails.
    """
    path_obj = Path(prompt_file_path)
    filename = path_obj.stem  # e.g., "my_module_python" from "my_module_python.prompt"

    # Try to split by the last underscore to separate language
    # This is a heuristic; strict naming conventions are assumed
    match = re.match(r"^(.*)_([^_]+)$", filename)
    if not match:
        return None, None

    file_basename = match.group(1)
    language = match.group(2).lower()

    # Reconstruct directory context from prompt path.
    # Prompt paths look like: .../prompts/frontend/src/app/settings/page_typescriptreact.prompt
    # We need to extract "frontend/src/app/settings/page" (not just "page").
    # Issue #1211: when a .pddrc near the prompt defines a non-default
    # `prompts_dir` (e.g. "prompts/backend"), anchor the subdir extraction
    # on that configured root. Without this, `infer_module_identity` would
    # emit a basename like "backend/services/foo" while construct_paths
    # / sync would emit "services/foo", silently splitting the fingerprint
    # filename into two ("backend_services_foo_*.json" vs "services_foo_*.json").
    parts = path_obj.parts
    configured_prompts_dir = _prompts_dir_for_prompt(path_obj)
    anchor_parts: Tuple[str, ...] = ()
    if configured_prompts_dir:
        normalized = str(configured_prompts_dir).replace("\\", "/").rstrip("/")
        anchor_parts = tuple(p for p in normalized.split("/") if p and p != ".")

    subdir_parts: Tuple[str, ...] = ()
    matched = False
    if anchor_parts:
        for start in range(len(parts) - len(anchor_parts), -1, -1):
            if start < 0:
                break
            if tuple(parts[start : start + len(anchor_parts)]) == anchor_parts:
                subdir_parts = parts[start + len(anchor_parts) : -1]
                matched = True
                break

    if not matched:
        try:
            prompts_idx = len(parts) - 1 - list(reversed(parts)).index("prompts")
            subdir_parts = parts[prompts_idx + 1 : -1]
        except ValueError:
            # No "prompts" directory in path — fall back to filename-only
            subdir_parts = ()

    if subdir_parts:
        basename = str(Path(*subdir_parts) / file_basename)
    else:
        basename = file_basename

    return basename, language


def _prompts_dir_for_prompt(prompt_path: Path) -> Optional[str]:
    """Return the configured `prompts_dir` from the .pddrc nearest the
    prompt file, or None if no .pddrc is reachable / no `prompts_dir`
    is set. Used by `infer_module_identity` (Issue #1211) to keep
    decorator-emitted basenames aligned with construct_paths/sync.
    """
    try:
        from .construct_paths import (
            _find_nearest_pddrc_for_file,
            _load_pddrc_config,
            _detect_context,
            _get_context_config,
            detect_context_for_file,
        )
    except ImportError:
        return None

    pddrc_path, _ = _find_nearest_pddrc_for_file(prompt_path)
    if pddrc_path is None:
        return None
    try:
        config = _load_pddrc_config(pddrc_path)
    except Exception:
        return None

    context_name = None
    try:
        if prompt_path.exists():
            detected, _ = detect_context_for_file(str(prompt_path))
            context_name = detected
    except Exception:
        context_name = None
    if context_name is None:
        try:
            context_name = _detect_context(prompt_path.parent, config, None)
        except Exception:
            context_name = None

    context_config = _get_context_config(config, context_name)
    return context_config.get("prompts_dir") or None


def _prompts_root_for_fingerprint(prompt_file: Union[str, Path]) -> Path:
    """Return the absolute base ``prompts`` root directory containing ``prompt_file``.

    Issue #1305 / #1211: ``get_pdd_file_paths`` re-resolves the prompts root from
    the run CWD (via ``_find_pddrc_file()``), so a decorated command run from a
    PARENT CWD for a nested subproject resolves to the parent — the prompt is not
    found, code/example/test paths point at non-existent parent files (every hash
    null), and the fingerprint is written to the parent ``.pdd/meta`` instead of
    the subproject, splitting it from the sync log / run report. Passing this
    value as ``prompts_dir`` re-anchors that resolution at the prompt file's
    subproject.

    This must be the *base* prompts directory (e.g. ``<subproject>/prompts``) —
    the same root ``get_pdd_file_paths`` uses by default — NOT a deeper,
    context-configured ``prompts_dir`` such as ``prompts/commands``.
    ``get_pdd_file_paths`` searches for the prompt recursively under this root and
    computes ``architecture.json`` lookup keys *relative to it*, so a deeper root
    changes that key (``checkup_python.prompt`` instead of
    ``commands/checkup_python.prompt``) and silently breaks filepath resolution.
    The ``prompts`` component nearest the file is that base root (using the
    outermost match would mis-anchor when the repo itself is checked out under an
    ancestor directory literally named ``prompts``, e.g. ``~/prompts/myrepo``);
    fall back to the prompt's own directory when the path has no ``prompts``
    component.
    """
    prompt_path = Path(prompt_file).resolve()
    parts = prompt_path.parts
    for index in range(len(parts) - 1, -1, -1):
        if parts[index] == "prompts":
            return Path(*parts[: index + 1])
    return prompt_path.parent


def load_operation_log(
    basename: str,
    language: str,
    paths: Optional[Dict[str, Any]] = None,
) -> List[Dict[str, Any]]:
    """
    Load all log entries for a module.

    Args:
        basename: Module basename.
        language: Module language.
        paths: Optional path hints (Issue #1211) so the log file is
            resolved under the subproject's .pdd/meta when run CWD lives
            above the subproject.

    Returns:
        List of log entries (dictionaries).
    """
    log_path = get_log_path(basename, language, paths=paths)
    entries = []
    
    if log_path.exists():
        try:
            with open(log_path, 'r', encoding='utf-8') as f:
                for line in f:
                    if line.strip():
                        try:
                            entry = json.loads(line)
                            # Backwards compatibility: defaulting invocation_mode to "sync"
                            if "invocation_mode" not in entry:
                                entry["invocation_mode"] = "sync"
                            entries.append(entry)
                        except json.JSONDecodeError:
                            continue
        except Exception:
            # If log is corrupt or unreadable, return empty list rather than crashing
            pass
            
    return entries


def append_log_entry(
    basename: str,
    language: str,
    entry: Dict[str, Any],
    paths: Optional[Dict[str, Any]] = None,
) -> None:
    """
    Append a single entry to the module's sync log.

    Args:
        basename: Module basename.
        language: Module language.
        entry: Dictionary of data to log.
        paths: Optional path hints (issue #1211); when given, the log file
            is anchored at the subproject's .pdd/meta even if cwd is above it.
    """
    log_path = get_log_path(basename, language, paths=paths)
    
    # Ensure standard fields exist
    if "timestamp" not in entry:
        entry["timestamp"] = datetime.now().isoformat()
    
    try:
        with open(log_path, 'a', encoding='utf-8') as f:
            f.write(json.dumps(entry) + "\n")
    except Exception as e:
        # Fallback console warning if logging fails
        console = Console()
        console.print(f"[yellow]Warning: Failed to write to log file {log_path}: {e}[/yellow]")


def create_log_entry(
    operation: str,
    reason: str,
    invocation_mode: str = "sync",
    estimated_cost: float = 0.0,
    confidence: float = 0.0,
    decision_type: str = "unknown"
) -> Dict[str, Any]:
    """
    Create a new log entry dictionary structure.
    """
    return {
        "timestamp": datetime.now().isoformat(),
        "operation": operation,
        "reason": reason,
        "invocation_mode": invocation_mode,
        "estimated_cost": estimated_cost,
        "confidence": confidence,
        "decision_type": decision_type,
        "success": False,
        "duration": 0.0,
        "actual_cost": 0.0,
        "model": "unknown",
        "error": None
    }


def create_manual_log_entry(operation: str) -> Dict[str, Any]:
    """
    Convenience function to create a manual invocation log entry dict.
    """
    return create_log_entry(
        operation=operation,
        reason="Manual invocation via CLI",
        invocation_mode="manual"
    )


def update_log_entry(
    entry: Dict[str, Any],
    success: bool,
    cost: float,
    model: str,
    duration: float,
    error: Optional[str] = None
) -> Dict[str, Any]:
    """
    Update a log entry with execution results.
    """
    entry["success"] = success
    entry["actual_cost"] = cost
    entry["model"] = model
    entry["duration"] = duration
    entry["error"] = error
    return entry


def log_event(
    basename: str,
    language: str,
    event_type: str,
    details: Any,
    invocation_mode: str = "manual",
    paths: Optional[Dict[str, Any]] = None,
) -> None:
    """
    Log a special event to the sync log.

    `paths` (Issue #1211) routes the entry through the subproject's
    .pdd/meta when run CWD lives above the subproject.
    """
    entry = {
        "timestamp": datetime.now().isoformat(),
        "type": "event",
        "event_type": event_type,
        "details": details,
        "invocation_mode": invocation_mode
    }
    append_log_entry(basename, language, entry, paths=paths)


def save_fingerprint(
    basename: str,
    language: str,
    operation: str,
    paths: Optional[Dict[str, Path]] = None,
    cost: float = 0.0,
    model: str = "unknown"
) -> None:
    """
    Save the current fingerprint/state to the state file.

    Writes the full Fingerprint dataclass format compatible with read_fingerprint()
    in sync_determine_operation.py. This ensures manual commands (generate, example)
    don't break sync's fingerprint tracking.
    """
    from dataclasses import asdict
    from datetime import timezone
    from .sync_determine_operation import calculate_current_hashes, Fingerprint, read_fingerprint
    from . import __version__

    # Issue #983: when the caller provides `paths`, use them directly — do
    # NOT call get_pdd_file_paths. Issue #1211: at the same time, use those
    # caller-supplied paths to detect the subproject root so the meta dir
    # anchors at the .pddrc rather than the run CWD.
    if not paths:
        from .sync_determine_operation import get_pdd_file_paths
        try:
            paths = get_pdd_file_paths(basename, language)
        except (ImportError, OSError, ValueError) as e:
            logger.warning("Could not resolve paths for %s/%s: %s", basename, language, e)
            paths = {}

    path = get_fingerprint_path(basename, language, paths=paths)

    # Issue #522: Pass stored include deps for prompt hash calculation
    prev_fp = read_fingerprint(basename, language, paths=paths)
    stored_deps = prev_fp.include_deps if prev_fp else None
    current_hashes = calculate_current_hashes(paths, stored_include_deps=stored_deps) if paths else {}

    # Create Fingerprint with same format as _save_fingerprint_atomic
    fingerprint = Fingerprint(
        pdd_version=__version__,
        timestamp=datetime.now(timezone.utc).isoformat(),
        command=operation,
        prompt_hash=current_hashes.get('prompt_hash'),
        code_hash=current_hashes.get('code_hash'),
        example_hash=current_hashes.get('example_hash'),
        test_hash=current_hashes.get('test_hash'),
        test_files=current_hashes.get('test_files'),
        include_deps=current_hashes.get('include_deps'),  # Issue #522
    )

    try:
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(asdict(fingerprint), f, indent=2)
    except Exception as e:
        console = Console()
        console.print(f"[yellow]Warning: Failed to save fingerprint to {path}: {e}[/yellow]")


def save_run_report(
    basename: str,
    language: str,
    report_data: Dict[str, Any],
    paths: Optional[Dict[str, Any]] = None,
) -> None:
    """
    Save a run report (test results) to the state file.
    `paths` (issue #1211) routes the file under the subproject meta dir.
    """
    path = get_run_report_path(basename, language, paths=paths)
    try:
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(report_data, f, indent=2)
    except Exception as e:
        console = Console()
        console.print(f"[yellow]Warning: Failed to save run report to {path}: {e}[/yellow]")


def clear_run_report(
    basename: str,
    language: str,
    paths: Optional[Dict[str, Any]] = None,
) -> None:
    """
    Remove an existing run report if it exists.
    """
    path = get_run_report_path(basename, language, paths=paths)
    if path.exists():
        try:
            os.remove(path)
        except Exception:
            pass


def _clear_run_report_before_fingerprint(
    basename: str,
    language: str,
    paths: Optional[Dict[str, Any]] = None,
) -> bool:
    """Clear stale run report and verify it is gone before fingerprint update."""
    path = get_run_report_path(basename, language, paths=paths)
    console = Console()

    try:
        had_run_report = path.exists()
    except OSError as e:
        console.print(
            f"[yellow]Warning: Could not inspect run report {path}: {e}. "
            "Skipping fingerprint update.[/yellow]"
        )
        return False

    clear_run_report(basename, language, paths=paths)
    if not had_run_report:
        return True

    try:
        if path.exists():
            console.print(
                f"[yellow]Warning: Run report {path} still exists after clear; "
                "skipping fingerprint update to avoid pairing a fresh "
                "fingerprint with stale runtime state.[/yellow]"
            )
            return False
    except OSError as e:
        console.print(
            f"[yellow]Warning: Could not verify run report deletion for {path}: {e}. "
            "Skipping fingerprint update.[/yellow]"
        )
        return False

    return True


def log_operation(
    operation: str,
    updates_fingerprint: bool = False,
    updates_run_report: bool = False,
    clears_run_report: bool = False
) -> Callable:
    """
    Decorator for Click commands to automatically log operations and manage state.
    """
    def decorator(func: Callable) -> Callable:
        @functools.wraps(func)
        def wrapper(*args: Any, **kwargs: Any) -> Any:
            # Try to get prompt_file from named kwarg first
            prompt_file = kwargs.get('prompt_file')

            # If not found, check if there's an 'args' tuple (for commands using nargs=-1)
            # and the first element looks like a prompt file path
            if not prompt_file:
                cli_args = kwargs.get('args')
                if cli_args and len(cli_args) > 0:
                    first_arg = str(cli_args[0])
                    # Check if it looks like a prompt file (ends with .prompt)
                    if first_arg.endswith('.prompt'):
                        prompt_file = first_arg

            basename, language = (None, None)
            # Issue #1211: track the prompt path so metadata writes anchor at
            # the subproject's .pdd/meta even when the user invoked the
            # command from above the subproject root.
            log_paths: Optional[Dict[str, Any]] = None
            if prompt_file:
                basename, language = infer_module_identity(prompt_file)
                log_paths = {"prompt": prompt_file}

            entry = create_manual_log_entry(operation=operation)
            start_time = time.time()
            success = False
            result = None
            error_msg = None

            try:
                result = func(*args, **kwargs)
                success = True
                return result
            except Exception as e:
                success = False
                error_msg = str(e)
                raise
            finally:
                duration = time.time() - start_time
                cost = 0.0
                model = "unknown"
                if success and result:
                    if isinstance(result, tuple) and len(result) >= 3:
                        from .sync_orchestration import _extract_cost_from_result, _extract_model_from_result
                        cost = _extract_cost_from_result(operation, result)
                        model = _extract_model_from_result(operation, result)

                update_log_entry(entry, success=success, cost=cost, model=model, duration=duration, error=error_msg)
                if basename and language:
                    append_log_entry(basename, language, entry, paths=log_paths)
                    if success:
                        fingerprint_allowed = True
                        # Clear the stale run report only after the command
                        # succeeds, so a failed run cannot erase existing
                        # runtime verification state that still describes the
                        # current code. The clear must happen before
                        # save_fingerprint so a fresh fingerprint never
                        # coexists with a stale per-module run report
                        # (issue #1057).
                        if clears_run_report:
                            fingerprint_allowed = _clear_run_report_before_fingerprint(
                                basename, language, paths=log_paths
                            )
                        if updates_fingerprint and fingerprint_allowed:
                            # Issue #1305 + #1211: save_fingerprint hashes only
                            # Path values, so a bare {"prompt": <str>} hint
                            # yields all-null hashes (the prompt string is
                            # skipped and code/example/test keys are absent) and
                            # the fingerprint never converges (CI auto-heal
                            # loops). Resolve the authoritative, complete Path
                            # set here. get_pdd_file_paths re-resolves the
                            # prompts root from the run CWD, so anchor it at the
                            # prompt file's subproject via an absolute
                            # prompts_dir — otherwise a command run from a PARENT
                            # CWD for a nested subproject resolves to the parent
                            # (null hashes again) and writes the fingerprint
                            # outside the subproject, splitting it from the log /
                            # run report that log_paths anchors. Fall back to a
                            # Path-coerced prompt hint (never a raw string) if
                            # resolution fails, so anchoring still works. The
                            # #983 contract is preserved: the caller resolves the
                            # paths, so save_fingerprint does not.
                            from .sync_determine_operation import get_pdd_file_paths
                            try:
                                prompts_root = _prompts_root_for_fingerprint(
                                    prompt_file
                                )
                                fingerprint_paths: Dict[str, Any] = get_pdd_file_paths(
                                    basename, language, prompts_dir=str(prompts_root)
                                )
                                # Existence-gate the resolution: if it silently
                                # resolved the prompt to a path that is not on
                                # disk (a mis-resolution that did not raise), the
                                # other paths are wrong too, so the fingerprint
                                # would be null and mis-anchored. Fall back to the
                                # real prompt path so prompt_hash is real and the
                                # write still anchors at the subproject.
                                resolved_prompt = fingerprint_paths.get("prompt")
                                if not (
                                    isinstance(resolved_prompt, Path)
                                    and resolved_prompt.exists()
                                ):
                                    fingerprint_paths = {"prompt": Path(prompt_file)}
                            except (ImportError, OSError, ValueError) as e:
                                logger.warning(
                                    "Could not resolve paths for %s/%s: %s",
                                    basename,
                                    language,
                                    e,
                                )
                                fingerprint_paths = {"prompt": Path(prompt_file)}
                            save_fingerprint(
                                basename,
                                language,
                                operation=operation,
                                paths=fingerprint_paths,
                                cost=cost,
                                model=model,
                            )
                        if updates_run_report and isinstance(result, dict):
                            save_run_report(basename, language, result, paths=log_paths)
        return wrapper
    return decorator
