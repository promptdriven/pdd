# pdd/sync_orchestration.py
"""
Orchestrates the complete PDD sync workflow by coordinating operations and
animations in parallel, serving as the core engine for the `pdd sync` command.
"""

import threading
import time
import json
import datetime
import subprocess
import re
import os
from pathlib import Path
from typing import Dict, Any, Optional, List, Callable
from dataclasses import asdict, dataclass, field
import tempfile
import sys

from .sync_tui import maybe_steer_operation, DEFAULT_STEER_TIMEOUT_S

import click
import logging

# --- Constants ---
MAX_CONSECUTIVE_TESTS = 3  # Allow up to 3 consecutive test attempts
MAX_TEST_EXTEND_ATTEMPTS = 2  # Allow up to 2 attempts to extend tests for coverage
MAX_CONSECUTIVE_CRASHES = 3  # Allow up to 3 consecutive crash attempts (Bug #157 fix)

# --- Real PDD Component Imports ---
from .sync_tui import SyncApp
from .operation_log import (
    load_operation_log,
    create_log_entry,
    update_log_entry,
    append_log_entry,
    log_event,
    save_fingerprint,
    save_run_report,
    clear_run_report,
)
from .sync_determine_operation import (
    sync_determine_operation,
    get_pdd_file_paths,
    RunReport,
    SyncDecision,
    PDD_DIR,
    META_DIR,
    SyncLock,
    read_run_report,
    calculate_sha256,
    calculate_current_hashes,
    _safe_basename,
)
from .auto_deps_main import auto_deps_main
from .code_generator_main import code_generator_main
from .context_generator_main import context_generator_main
from .crash_main import crash_main
from .fix_verification_main import fix_verification_main
from .cmd_test_main import cmd_test_main
from .fix_main import fix_main
from .update_main import update_main
from .python_env_detector import detect_host_python_executable
from .get_run_command import get_run_command_for_file
from .pytest_output import extract_failing_files_from_output, _find_project_root
from . import DEFAULT_STRENGTH


# --- Helper Functions ---
# Note: _safe_basename is imported from sync_determine_operation


def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Returns True if we should use agentic path (non-Python OR agentic_mode for Python).

    This is used to determine whether to skip iterative LLM loops and delegate
    directly to agentic handlers. When agentic_mode is True, Python behaves
    like TypeScript/other languages.
    """
    return language.lower() != 'python' or agentic_mode


# --- Atomic State Update (Issue #159 Fix) ---

@dataclass
class PendingStateUpdate:
    """Holds pending state updates for atomic commit."""
    run_report: Optional[Dict[str, Any]] = None
    fingerprint: Optional[Dict[str, Any]] = None
    run_report_path: Optional[Path] = None
    fingerprint_path: Optional[Path] = None


class AtomicStateUpdate:
    """
    Context manager for atomic state updates.

    Ensures run_report and fingerprint are both written or neither is written.
    This fixes Issue #159 where non-atomic writes caused state desynchronization.

    Usage:
        with AtomicStateUpdate(basename, language) as state:
            state.set_run_report(report_dict, report_path)
            state.set_fingerprint(fingerprint_dict, fp_path)
        # On successful exit, both files are written atomically
        # On exception, neither file is written (rollback)
    """

    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language
        self.pending = PendingStateUpdate()
        self._temp_files: List[str] = []

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            self._commit()
        else:
            self._rollback()
        return False  # Don't suppress exceptions

    def set_run_report(self, report: Dict[str, Any], path: Path):
        """Buffer a run report for atomic write."""
        self.pending.run_report = report
        self.pending.run_report_path = path

    def set_fingerprint(self, fingerprint: Dict[str, Any], path: Path):
        """Buffer a fingerprint for atomic write."""
        self.pending.fingerprint = fingerprint
        self.pending.fingerprint_path = path

    def _atomic_write(self, data: Dict[str, Any], target_path: Path) -> None:
        """Write data to file atomically using temp file + rename pattern."""
        target_path.parent.mkdir(parents=True, exist_ok=True)

        # Write to temp file in same directory (required for atomic rename)
        fd, temp_path = tempfile.mkstemp(
            dir=target_path.parent,
            prefix=f".{target_path.stem}_",
            suffix=".tmp"
        )
        self._temp_files.append(temp_path)

        try:
            with os.fdopen(fd, 'w') as f:
                json.dump(data, f, indent=2, default=str)

            # Atomic rename - guaranteed atomic on POSIX systems
            os.replace(temp_path, target_path)
            self._temp_files.remove(temp_path)  # Successfully moved, stop tracking
        except Exception:
            # Leave temp file for rollback to clean up
            raise

    def _commit(self):
        """Commit all pending state updates atomically."""
        # Write fingerprint first (checkpoint), then run_report
        if self.pending.fingerprint and self.pending.fingerprint_path:
            self._atomic_write(self.pending.fingerprint, self.pending.fingerprint_path)
        if self.pending.run_report and self.pending.run_report_path:
            self._atomic_write(self.pending.run_report, self.pending.run_report_path)

    def _rollback(self):
        """Clean up any temp files without committing changes."""
        for temp_path in self._temp_files:
            try:
                if os.path.exists(temp_path):
                    os.unlink(temp_path)
            except OSError:
                pass  # Best effort cleanup
        self._temp_files.clear()


# --- State Management Wrappers ---

def _save_run_report_atomic(report: Dict[str, Any], basename: str, language: str,
                    atomic_state: Optional['AtomicStateUpdate'] = None):
    """Save a run report to the metadata directory, supporting atomic updates.

    Args:
        report: The run report dictionary to save.
        basename: The module basename.
        language: The programming language.
        atomic_state: Optional AtomicStateUpdate for atomic writes (Issue #159 fix).
    """
    if atomic_state:
        # Buffer for atomic write
        report_file = META_DIR / f"{_safe_basename(basename)}_{language.lower()}_run.json"
        atomic_state.set_run_report(report, report_file)
    else:
        # Direct write using operation_log
        save_run_report(basename, language, report)

def _save_fingerprint_atomic(basename: str, language: str, operation: str,
                               paths: Dict[str, Path], cost: float, model: str,
                               atomic_state: Optional['AtomicStateUpdate'] = None):
    """Save fingerprint state after successful operation, supporting atomic updates.

    Args:
        basename: The module basename.
        language: The programming language.
        operation: The operation that was performed.
        paths: Dictionary of PDD file paths.
        cost: The cost of the operation.
        model: The model used.
        atomic_state: Optional AtomicStateUpdate for atomic writes (Issue #159 fix).
    """
    if atomic_state:
        # Buffer for atomic write
        from datetime import datetime, timezone
        from .sync_determine_operation import calculate_current_hashes, Fingerprint
        from . import __version__

        current_hashes = calculate_current_hashes(paths)
        fingerprint = Fingerprint(
            pdd_version=__version__,
            timestamp=datetime.now(timezone.utc).isoformat(),
            command=operation,
            prompt_hash=current_hashes.get('prompt_hash'),
            code_hash=current_hashes.get('code_hash'),
            example_hash=current_hashes.get('example_hash'),
            test_hash=current_hashes.get('test_hash'),
            test_files=current_hashes.get('test_files'),  # Bug #156
        )

        fingerprint_file = META_DIR / f"{_safe_basename(basename)}_{language.lower()}.json"
        atomic_state.set_fingerprint(asdict(fingerprint), fingerprint_file)
    else:
        # Direct write using operation_log
        save_fingerprint(basename, language, operation, paths, cost, model)

... (truncated for brevity in explanation)