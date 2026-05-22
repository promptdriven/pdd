"""In-process per-job budget settings store, effective-cap formula, and
``pdd-issue`` defaults for the GitHub App control-comment surface.

This module is the public source of truth for the budget arithmetic the
GitHub App webhook handler and the ``/commands/jobs/{job_id}/budget`` REST
endpoints rely on. It is intentionally I/O-free: it does not persist to disk,
poll the cost CSV, parse comment bodies, or render replies. Those concerns
live in their own modules (see ``cost_budget_watcher.py``,
``slash_command_parser.py``, ``budget_comments.py``).
"""

from __future__ import annotations

import math
import threading
from typing import Any, Optional, Tuple

from .models import BudgetSettings, JobStatus


__all__ = [
    "pdd_issue_defaults",
    "effective_cap",
    "validate_amount",
    "BudgetStore",
    "PDD_ISSUE_DEFAULT_NODE_BUDGET",
    "PDD_ISSUE_DEFAULT_MAX_TOTAL_CAP",
    "BUDGET_HARD_CEILING",
]


PDD_ISSUE_DEFAULT_NODE_BUDGET: float = 80.0
PDD_ISSUE_DEFAULT_MAX_TOTAL_CAP: float = 400.0
BUDGET_HARD_CEILING: float = 10000.0


def pdd_issue_defaults() -> Tuple[float, float]:
    """Return the ``pdd-issue`` budget defaults ``(node_budget, max_total_cap)``.

    Matches the issue's acceptance criteria: ``$80`` per node, ``$400`` total
    cap. Returned as a tuple of floats so callers can unpack directly.
    """
    return (PDD_ISSUE_DEFAULT_NODE_BUDGET, PDD_ISSUE_DEFAULT_MAX_TOTAL_CAP)


def effective_cap(
    command: str,
    *,
    budget_cap: Optional[float] = None,
    node_budget: Optional[float] = None,
    max_total_cap: Optional[float] = None,
    node_count: Optional[int] = None,
) -> Optional[float]:
    """Compute the single effective USD ceiling the watcher enforces.

    For ``command == "issue"``:
      ``n = max(node_count or 1, 1)`` (handles ``node_count is None`` before
      the solving tree has expanded);
      both set → ``min(node_budget * n, max_total_cap)``;
      only ``max_total_cap`` set → ``max_total_cap``;
      only ``node_budget`` set → ``node_budget * n``;
      neither set → ``None`` (no cap).

    For any other command, returns ``budget_cap`` unchanged (which may be
    ``None``).
    """
    if command == "issue":
        n = max(node_count or 1, 1)
        if node_budget is None and max_total_cap is None:
            return None
        if node_budget is None:
            return max_total_cap
        if max_total_cap is None:
            return node_budget * n
        return min(node_budget * n, max_total_cap)
    return budget_cap


def validate_amount(value: Any) -> float:
    """Coerce and validate a budget amount.

    Accepts ``int``, ``float``, or ``str`` (``"$30"``, ``"30.00"``, ``"30"``);
    strips a leading ``$`` and surrounding whitespace; parses as ``float``.
    Raises ``ValueError`` for negatives, zero, NaN, infinity, non-numeric
    strings, and values strictly greater than ``BUDGET_HARD_CEILING``
    (``$10000``).
    """
    if isinstance(value, bool):
        # bool is a subclass of int but is never a sensible budget amount.
        raise ValueError(f"Invalid budget amount: {value!r}")
    if isinstance(value, str):
        stripped = value.strip().lstrip("$").strip()
        if not stripped:
            raise ValueError(f"Empty budget amount: {value!r}")
        try:
            amount = float(stripped)
        except ValueError as exc:
            raise ValueError(f"Non-numeric budget amount: {value!r}") from exc
    elif isinstance(value, (int, float)):
        amount = float(value)
    else:
        raise ValueError(f"Unsupported budget amount type: {type(value).__name__}")

    if not math.isfinite(amount):
        raise ValueError(f"Budget amount must be finite: {value!r}")
    if amount <= 0:
        raise ValueError(f"Budget amount must be > 0: {value!r}")
    if amount > BUDGET_HARD_CEILING:
        raise ValueError(
            f"Budget amount {amount} exceeds hard ceiling ${BUDGET_HARD_CEILING}"
        )
    return amount


_UNSET = object()


class BudgetStore:
    """Thread-safe ``job_id -> BudgetSettings`` mapping.

    Construct one per-server (the FastAPI app holds a singleton); tests may
    create fresh instances. All mutations take a ``threading.Lock`` so the
    store is safe under concurrent access from FastAPI workers and the
    job-manager background tasks.
    """

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._store: dict[str, BudgetSettings] = {}

    def get(self, job_id: str) -> Optional[BudgetSettings]:
        with self._lock:
            return self._store.get(job_id)

    def set(self, job_id: str, settings: BudgetSettings) -> None:
        with self._lock:
            self._store[job_id] = settings

    def delete(self, job_id: str) -> None:
        with self._lock:
            self._store.pop(job_id, None)

    def update(
        self,
        job_id: str,
        *,
        budget_cap: Any = _UNSET,
        node_budget: Any = _UNSET,
        max_total_cap: Any = _UNSET,
        node_count: Any = _UNSET,
        spent_so_far: Any = _UNSET,
        status: Any = _UNSET,
    ) -> BudgetSettings:
        """Update the snapshot for ``job_id`` and return the new value.

        Unset keyword arguments leave the corresponding field unchanged;
        passing an explicit ``None`` clears that field. The returned snapshot
        has ``effective_cap`` recomputed from the post-update values.
        """
        with self._lock:
            current = self._store.get(job_id)
            if current is None:
                raise KeyError(job_id)

            new_node_budget = current.node_budget if node_budget is _UNSET else node_budget
            new_max_total_cap = current.max_total_cap if max_total_cap is _UNSET else max_total_cap
            new_budget_cap = current.budget_cap if budget_cap is _UNSET else budget_cap
            new_node_count = current.node_count if node_count is _UNSET else node_count
            new_spent = current.spent_so_far if spent_so_far is _UNSET else float(spent_so_far)
            new_status = current.status if status is _UNSET else status

            updated = BudgetSettings(
                command=current.command,
                node_budget=new_node_budget,
                max_total_cap=new_max_total_cap,
                budget_cap=new_budget_cap,
                effective_cap=effective_cap(
                    current.command,
                    budget_cap=new_budget_cap,
                    node_budget=new_node_budget,
                    max_total_cap=new_max_total_cap,
                    node_count=new_node_count,
                ),
                spent_so_far=new_spent,
                status=new_status,
                node_count=new_node_count,
            )
            self._store[job_id] = updated
            return updated
