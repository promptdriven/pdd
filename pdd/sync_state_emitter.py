# pdd/sync_state_emitter.py
"""
Emits structured sync state to stdout with special markers for frontend parsing.

When running in remote/web mode (PDD_WEB_MODE=1), the TUI is not visible.
This emitter writes JSON-encoded state updates to stdout with a unique marker
prefix, allowing the frontend to parse structured data from the text stream
and render the SyncVisualization component.
"""

import json
import time
from typing import Optional, Dict, Any


class SyncStateEmitter:
    """Writes JSON-encoded sync state to stdout with a marker prefix."""

    MARKER = "@@PDD_SYNC_STATE@@"

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

    def _emit(self, data: Dict[str, Any]) -> None:
        """Write a marker line to stdout."""
        line = json.dumps(data, separators=(',', ':'))
        print(f"{self.MARKER}{line}", flush=True)

    def emit_sync_start(self, paths: Dict[str, str]) -> None:
        """Emit the sync_start message at the beginning of sync.

        Args:
            paths: Dict with keys prompt, code, example, tests mapping to file paths.
        """
        self._emit({
            "type": "sync_start",
            "basename": self._basename,
            "budget": self._budget,
            "paths": paths,
            "elapsedSeconds": 0,
        })

    def emit_state_update(
        self,
        operation: str,
        cost: float,
        paths: Dict[str, str],
        colors: Optional[Dict[str, str]] = None,
    ) -> None:
        """Emit a state_update message when operation or cost changes.

        Args:
            operation: Current operation name (generate, fix, test, etc.).
            cost: Current accumulated cost.
            paths: Dict with keys prompt, code, example, tests mapping to file paths.
            colors: Optional dict of box colors keyed by prompt, code, example, tests.
        """
        self._last_operation = operation
        elapsed = time.time() - self._start_time
        self._emit({
            "type": "state_update",
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
        """Emit the sync_complete message at the end of sync.

        Args:
            cost: Final accumulated cost.
            success: Whether the sync completed successfully.
        """
        elapsed = time.time() - self._start_time
        self._emit({
            "type": "sync_complete",
            "cost": round(cost, 4),
            "budget": self._budget,
            "basename": self._basename,
            "elapsedSeconds": round(elapsed, 1),
            "status": "completed" if success else "failed",
            "operation": self._last_operation or "done",
        })
