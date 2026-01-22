# pdd/sync_state_emitter.py
"""
Writes sync state to a temp file for the server to read and forward to the frontend.

This replicates what the TUI does with shared mutable refs, but across process
boundaries (subprocess → server). The server polls the file and includes the
state in job status responses, which flow to the frontend via the cloud.
"""

import json
import os
import tempfile
import time
from typing import Optional, Dict, Any


class SyncStateEmitter:
    """Writes sync state to a temp file for cross-process communication."""

    def __init__(self, basename: str, budget: Optional[float] = None):
        """Initialize the emitter.

        Args:
            basename: The module basename being synced.
            budget: The budget limit for the sync operation.
        """
        self._basename = basename
        self._budget = budget
        self._start_time = time.time()
        self._last_operation: Optional[str] = None

        # Use the file path from env (set by job manager) or a default
        self._state_file = os.environ.get(
            'PDD_SYNC_STATE_FILE',
            os.path.join(tempfile.gettempdir(), f'pdd_sync_state_{os.getpid()}.json')
        )

    def _write_state(self, data: Dict[str, Any]) -> None:
        """Atomically write state to the temp file."""
        tmp_path = self._state_file + '.tmp'
        try:
            with open(tmp_path, 'w') as f:
                json.dump(data, f, separators=(',', ':'))
            os.replace(tmp_path, self._state_file)
        except OSError:
            pass  # Non-fatal: best-effort state reporting

    def emit_sync_start(self, paths: Dict[str, str]) -> None:
        """Write initial sync state.

        Args:
            paths: Dict with keys prompt, code, example, tests mapping to file paths.
        """
        self._write_state({
            "operation": "initializing",
            "cost": 0,
            "budget": self._budget,
            "basename": self._basename,
            "elapsedSeconds": 0,
            "paths": paths,
            "colors": {},
            "status": "running",
        })

    def emit_state_update(
        self,
        operation: str,
        cost: float,
        paths: Dict[str, str],
        colors: Optional[Dict[str, str]] = None,
    ) -> None:
        """Write updated state when operation or cost changes.

        Args:
            operation: Current operation name (generate, fix, test, etc.).
            cost: Current accumulated cost.
            paths: Dict with keys prompt, code, example, tests mapping to file paths.
            colors: Optional dict of box colors keyed by prompt, code, example, tests.
        """
        self._last_operation = operation
        elapsed = time.time() - self._start_time
        self._write_state({
            "operation": operation,
            "cost": round(cost, 4),
            "budget": self._budget,
            "basename": self._basename,
            "elapsedSeconds": round(elapsed, 1),
            "paths": paths,
            "colors": colors or {},
            "status": "running",
        })

    def emit_sync_complete(self, cost: float, success: bool) -> None:
        """Write final state.

        Args:
            cost: Final accumulated cost.
            success: Whether the sync completed successfully.
        """
        elapsed = time.time() - self._start_time
        self._write_state({
            "operation": self._last_operation or "done",
            "cost": round(cost, 4),
            "budget": self._budget,
            "basename": self._basename,
            "elapsedSeconds": round(elapsed, 1),
            "paths": {},
            "colors": {},
            "status": "completed" if success else "failed",
        })

    def cleanup(self) -> None:
        """Remove the state file."""
        try:
            os.unlink(self._state_file)
        except OSError:
            pass
