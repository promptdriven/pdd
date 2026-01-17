from __future__ import annotations

import functools
import json
import os
import re
import time
from datetime import datetime
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple, Union

import click
from rich.console import Console

# We assume standard paths relative to the project root
PDD_DIR = ".pdd"
META_DIR = os.path.join(PDD_DIR, "meta")


def ensure_meta_dir() -> None:
    """Ensure the .pdd/meta directory exists."""
    os.makedirs(META_DIR, exist_ok=True)


def get_log_path(basename: str, language: str) -> Path:
    """Get the path to the sync log for a specific module."""
    ensure_meta_dir()
    return Path(META_DIR) / f"{basename}_{language}_sync.log"


def get_fingerprint_path(basename: str, language: str) -> Path:
    """Get the path to the fingerprint file for a specific module."""
    ensure_meta_dir()
    return Path(META_DIR) / f"{basename}_{language}.fingerprint"


def get_run_report_path(basename: str, language: str) -> Path:
    """Get the path to the run report file for a specific module."""
    ensure_meta_dir()
    return Path(META_DIR) / f"{basename}_{language}_run_report.json"


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
        language = match.group(2)
        return basename, language
        
    return None, None


def load_log_entries(basename: str, language: str) -> List[Dict[str, Any]]:
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
    entry_data: Dict[str, Any]
) -> None:
    """
    Append a single entry to the module's sync log.
    
    Args:
        basename: Module basename.
        language: Module language.
        entry_data: Dictionary of data to log.
    """
    log_path = get_log_path(basename, language)
    
    # Ensure standard fields exist
    if "timestamp" not in entry_data:
        entry_data["timestamp"] = datetime.now().isoformat()
    
    try:
        with open(log_path, 'a', encoding='utf-8') as f:
            f.write(json.dumps(entry_data) + "\n")
    except Exception as e:
        # Fallback console warning if logging fails
        console = Console()
        console.print(f"[yellow]Warning: Failed to write to log file {log_path}: {e}[/yellow]")


def create_manual_log_entry(
    basename: str,
    language: str,
    operation: str,
    success: bool,
    duration: float,
    cost: float = 0.0,
    model: str = "unknown",
    metadata: Optional[Dict[str, Any]] = None
) -> None:
    """
    Convenience function to create a manual invocation log entry.
    
    Args:
        basename: Module basename.
        language: Module language.
        operation: Name of the operation (e.g., \"generate\", \"verify\").
        success: Whether the operation succeeded.
        duration: Duration in seconds.
        cost: Cost in USD.
        model: Model used.
        metadata: Additional arbitrary metadata.
    """
    entry = {
        "timestamp": datetime.now().isoformat(),
        "operation": operation,
        "invocation_mode": "manual",
        "reason": "Manual invocation via CLI",
        "success": success,
        "duration": duration,
        "cost": cost,
        "model": model,
    }
    
    if metadata:
        entry.update(metadata)
        
    append_log_entry(basename, language, entry)


def log_event(
    basename: str,
    language: str,
    event_type: str,
    details: str,
    invocation_mode: str = "manual"
) -> None:
    """
    Log a special event to the sync log.
    
    Args:
        basename: Module basename.
        language: Module language.
        event_type: Type of event (e.g., \"lock_acquired\", \"budget_warning\").
        details: Human-readable details.
        invocation_mode: \"manual\" or \"sync\".
    """
    entry = {
        "timestamp": datetime.now().isoformat(),
        "type": "event",
        "event_type": event_type,
        "details": details,
        "invocation_mode": invocation_mode
    }
    append_log_entry(basename, language, entry)


def save_fingerprint(basename: str, language: str, fingerprint: str) -> None:
    """
    Save the current fingerprint to the state file.
    
    Args:
        basename: Module basename.
        language: Module language.
        fingerprint: The content hash or fingerprint string.
    """
    path = get_fingerprint_path(basename, language)
    try:
        with open(path, 'w', encoding='utf-8') as f:
            f.write(fingerprint)
    except Exception as e:
        console = Console()
        console.print(f"[yellow]Warning: Failed to save fingerprint to {path}: {e}[/yellow]")


def save_run_report(basename: str, language: str, report_data: Dict[str, Any]) -> None:
    """
    Save a run report (test results) to the state file.
    
    Args:
        basename: Module basename.
        language: Module language.
        report_data: Dictionary containing report data.
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
    
    Used when an operation invalidates previous test results.
    
    Args:
        basename: Module basename.
        language: Module language.
    """
    path = get_run_report_path(basename, language)
    if path.exists():
        try:
            os.remove(path)
        except Exception:
            pass


def log_operation(
    updates_fingerprint: bool = False,
    updates_run_report: bool = False,
    clears_run_report: bool = False
) -> Callable:
    """
    Decorator for Click commands to automatically log operations and manage state.
    
    It wraps the command execution to:
    1. Infer module identity from `prompt_file` argument.
    2. Log the operation start/end time.
    3. Capture success/failure.
    4. Handle state files (fingerprints, run reports) based on configuration.
    
    Args:
        updates_fingerprint: If True, saves fingerprint on success.
        updates_run_report: If True, saves run report on success.
        clears_run_report: If True, deletes existing run report before execution.
        
    Returns:
        Decorated function.
    """
    def decorator(func: Callable) -> Callable:
        @functools.wraps(func)
        def wrapper(*args: Any, **kwargs: Any) -> Any:
            # Try to find prompt_file in arguments to infer identity
            prompt_file = kwargs.get('prompt_file')
            
            basename: Optional[str] = None
            language: Optional[str] = None
            
            if prompt_file:
                basename, language = infer_module_identity(prompt_file)

            # Perform pre-execution cleanup
            if basename and language and clears_run_report:
                clear_run_report(basename, language)

            start_time = time.time()
            success = False
            result = None
            
            try:
                result = func(*args, **kwargs)
                success = True
                return result
            except Exception:
                success = False
                raise
            finally:
                duration = time.time() - start_time
                
                # Only log if we successfully inferred identity
                if basename and language:
                    cost = 0.0
                    model = "unknown"
                    
                    if isinstance(result, tuple) and len(result) >= 3:
                        if isinstance(result[1], (int, float)) and isinstance(result[2], str):
                            cost = float(result[1])
                            model = str(result[2])

                    # Log the operation
                    create_manual_log_entry(
                        basename=basename,
                        language=language,
                        operation=func.__name__,
                        success=success,
                        duration=duration,
                        cost=cost,
                        model=model
                    )
                    
                    if success:
                        if updates_run_report and isinstance(result, dict):
                            save_run_report(basename, language, result)

        return wrapper
    return decorator