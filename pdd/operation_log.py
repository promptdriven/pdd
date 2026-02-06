from __future__ import annotations

import functools
import json
import os
import re

import time
from datetime import datetime
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple, Union

from rich.console import Console

# We assume standard paths relative to the project root
PDD_DIR = ".pdd"
META_DIR = os.path.join(PDD_DIR, "meta")


def ensure_meta_dir() -> None:
    """Ensure the .pdd/meta directory exists."""
    os.makedirs(META_DIR, exist_ok=True)


def _safe_basename(basename: str) -> str:
    """Sanitize basename for use in metadata filenames.

    Replaces '/' with '_' to prevent path interpretation when the basename
    contains subdirectory components (e.g., 'core/cloud' -> 'core_cloud').
    """
    return basename.replace('/', '_')


def get_log_path(basename: str, language: str) -> Path:
    """Get the path to the sync log for a specific module."""
    ensure_meta_dir()
    return Path(META_DIR) / f"{_safe_basename(basename)}_{language}_sync.log"


def get_fingerprint_path(basename: str, language: str) -> Path:
    """Get the path to the fingerprint JSON file for a specific module."""
    ensure_meta_dir()
    return Path(META_DIR) / f"{_safe_basename(basename)}_{language}.json"


def get_run_report_path(basename: str, language: str) -> Path:
    """Get the path to the run report file for a specific module."""
    ensure_meta_dir()
    return Path(META_DIR) / f"{_safe_basename(basename)}_{language}_run.json"


def infer_module_identity(prompt_file_path: Union[str, Path]) -> Tuple[Optional[str], Optional[str]]:
    """
    Infer basename and language from a prompt file path.
    
    Expected pattern: prompts/{basename}_{language}.prompt
    
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
    if match:
        basename = match.group(1)
        language = match.group(2).lower()
        return basename, language
        
    return None, None


def load_operation_log(basename: str, language: str) -> List[Dict[str, Any]]:
    """
    Load all log entries for a module.
    
    Args:
        basename: Module basename.
        language: Module language.
        
    Returns:
        List of log entries (dictionaries).
    """
    log_path = get_log_path(basename, language)
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
    entry: Dict[str, Any]
) -> None:
    """
    Append a single entry to the module's sync log.
    
    Args:
        basename: Module basename.
        language: Module language.
        entry: Dictionary of data to log.
    """
    log_path = get_log_path(basename, language)
    
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
    invocation_mode: str = "manual"
) -> None:
    """
    Log a special event to the sync log.
    """
    entry = {
        "timestamp": datetime.now().isoformat(),
        "type": "event",
        "event_type": event_type,
        "details": details,
        "invocation_mode": invocation_mode
    }
    append_log_entry(basename, language, entry)


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
    from .sync_determine_operation import calculate_current_hashes, Fingerprint
    from . import __version__

    path = get_fingerprint_path(basename, language)

    # Calculate file hashes from paths (if provided)
    current_hashes = calculate_current_hashes(paths) if paths else {}

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
    )

    try:
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(asdict(fingerprint), f, indent=2)
    except Exception as e:
        console = Console()
        console.print(f"[yellow]Warning: Failed to save fingerprint to {path}: {e}[/yellow]")


def save_run_report(basename: str, language: str, report_data: Dict[str, Any]) -> None:
    """
    Save a run report (test results) to the state file.
    """
    path = get_run_report_path(basename, language)
    try:
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(report_data, f, indent=2)
    except Exception as e:
        console = Console()
        console.print(f"[yellow]Warning: Failed to save run report to {path}: {e}[/yellow]")


def clear_run_report(basename: str, language: str) -> None:
    """
    Remove an existing run report if it exists.
    """
    path = get_run_report_path(basename, language)
    if path.exists():
        try:
            os.remove(path)
        except Exception:
            pass


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
            if prompt_file:
                basename, language = infer_module_identity(prompt_file)

            if basename and language and clears_run_report:
                clear_run_report(basename, language)

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
                        if isinstance(result[1], (int, float)): cost = float(result[1])
                        if isinstance(result[2], str): model = str(result[2])

                update_log_entry(entry, success=success, cost=cost, model=model, duration=duration, error=error_msg)
                if basename and language:
                    append_log_entry(basename, language, entry)
                    if success:
                        if updates_fingerprint:
                            save_fingerprint(basename, language, operation=operation, cost=cost, model=model)
                        if updates_run_report and isinstance(result, dict):
                            save_run_report(basename, language, result)
        return wrapper
    return decorator