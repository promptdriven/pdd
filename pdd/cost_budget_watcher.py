"""Polling watcher that tails the PDD cost CSV and fires once when per-job
cumulative spend reaches the active cap.

The watcher is a small reusable utility called by ``pdd/server/jobs.py``
around each subprocess and by the GitHub App executor. It does NOT terminate
processes itself; the cancel path is the caller's responsibility (the
``on_exceeded`` callback decides what to do). Enforcement is at the
**subprocess boundary** — ``track_cost`` only appends a row when a PDD
subprocess exits, so the watcher cannot interrupt an in-flight call.
"""

from __future__ import annotations

import csv
import logging
import pathlib
import threading
import time
from dataclasses import dataclass
from datetime import datetime
from typing import Callable, FrozenSet, Iterable, Optional


__all__ = ["watch", "Watcher"]


logger = logging.getLogger(__name__)


def _parse_cost(raw: Optional[str]) -> float:
    """Return ``raw`` as a non-negative float, falling back to ``0.0``.

    Per the CSV reader contract, missing/blank/non-numeric cells must NOT
    raise out of the watcher.
    """
    if raw is None:
        return 0.0
    try:
        value = float(raw)
    except (TypeError, ValueError):
        return 0.0
    if value != value or value < 0:  # NaN check or negative
        return 0.0
    return value


def _parse_timestamp(raw: Optional[str]) -> Optional[datetime]:
    if not raw:
        return None
    try:
        # ISO 8601 like '2026-05-22T18:00:00.123' or '...+00:00'
        return datetime.fromisoformat(raw)
    except (TypeError, ValueError):
        return None


@dataclass
class _State:
    cap: Optional[float]
    fired: bool = False


class Watcher:
    """Daemon-thread watcher returned by :func:`watch`.

    Use :meth:`spent` to read the current accumulated spend, :meth:`update_cap`
    to apply a mid-flight cap change, and :meth:`stop` to terminate the poller
    (idempotent).
    """

    def __init__(
        self,
        csv_path: pathlib.Path,
        cap: Optional[float],
        on_exceeded: Callable[[float], None],
        *,
        commands: Optional[Iterable[str]] = None,
        started_at: Optional[datetime] = None,
        poll_interval: float = 2.0,
    ) -> None:
        self._csv_path = pathlib.Path(csv_path)
        self._on_exceeded = on_exceeded
        self._commands: Optional[FrozenSet[str]] = (
            frozenset(commands) if commands is not None else None
        )
        self._started_at = started_at
        self._poll_interval = max(0.1, float(poll_interval))
        self._stop_event = threading.Event()
        self._lock = threading.Lock()
        self._state = _State(cap=cap)
        self._spent: float = 0.0
        self._thread = threading.Thread(
            target=self._run, name=f"cost-budget-watcher:{self._csv_path.name}", daemon=True
        )
        self._thread.start()

    # ----------------------------------------------------------------- API

    def spent(self) -> float:
        with self._lock:
            return self._spent

    def update_cap(self, new_cap: Optional[float]) -> None:
        with self._lock:
            self._state.cap = new_cap

    def stop(self) -> None:
        self._stop_event.set()

    # -------------------------------------------------------------- internal

    def _read_spent(self) -> float:
        if not self._csv_path.exists():
            return 0.0
        try:
            with self._csv_path.open("r", encoding="utf-8", newline="") as handle:
                reader = csv.DictReader(handle)
                total = 0.0
                for row in reader:
                    if self._commands is not None and row.get("command") not in self._commands:
                        continue
                    if self._started_at is not None:
                        ts = _parse_timestamp(row.get("timestamp"))
                        if ts is None or ts < self._started_at:
                            continue
                    total += _parse_cost(row.get("cost"))
                return total
        except (OSError, csv.Error) as exc:
            logger.debug("cost-budget-watcher: read error on %s: %s", self._csv_path, exc)
            return 0.0

    def _run(self) -> None:
        while not self._stop_event.is_set():
            try:
                spent = self._read_spent()
                with self._lock:
                    self._spent = spent
                    cap = self._state.cap
                    fired = self._state.fired
                if cap is not None and not fired and spent >= cap:
                    with self._lock:
                        self._state.fired = True
                    try:
                        self._on_exceeded(spent)
                    except Exception:  # noqa: BLE001 - callback errors must not kill the thread
                        logger.exception("cost-budget-watcher: on_exceeded raised")
            except Exception:  # noqa: BLE001 - poller must survive arbitrary errors
                logger.exception("cost-budget-watcher: poll error")
            # Sleep via Event.wait so .stop() wakes the loop promptly.
            self._stop_event.wait(self._poll_interval)


def watch(
    csv_path: pathlib.Path,
    cap: Optional[float],
    on_exceeded: Callable[[float], None],
    *,
    commands: Optional[Iterable[str]] = None,
    started_at: Optional[datetime] = None,
    poll_interval: float = 2.0,
) -> Watcher:
    """Start a daemon watcher polling ``csv_path`` and return its handle.

    The watcher fires ``on_exceeded(spent)`` at most once for its lifetime
    (R1). When ``cap is None`` it acts as a read-only poller for
    :meth:`Watcher.spent`. Use the ``commands`` set (e.g. the nested PDD
    command names ``{"change", "sync", "bug", ...}``) to filter the CSV; for a
    single-command job, pass ``{job.command}``. ``time`` here is unused but
    referenced via ``poll_interval``.
    """
    # Silence "imported but unused" — kept so the helper module remains
    # importable even when no caller has invoked watch yet.
    _ = time
    if cap is not None:
        if not isinstance(cap, (int, float)) or cap != cap:  # NaN
            raise ValueError(f"Invalid cap: {cap!r}")
        if cap <= 0 or cap > 10000:
            raise ValueError(f"Cap {cap} outside (0, 10000]")
    return Watcher(
        csv_path=csv_path,
        cap=cap,
        on_exceeded=on_exceeded,
        commands=commands,
        started_at=started_at,
        poll_interval=poll_interval,
    )
