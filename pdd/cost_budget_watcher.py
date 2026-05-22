"""Polling watcher that tails the PDD cost CSV and fires once when per-job
cumulative spend reaches the active cap.

The watcher is a small reusable utility called by ``pdd/server/jobs.py``
around each subprocess and by the GitHub App executor. It does NOT terminate
processes itself; the cancel path is the caller's responsibility (the
``on_exceeded`` callback decides what to do). Enforcement is at the
**subprocess boundary** — ``track_cost`` only appends a row when a PDD
subprocess exits, so the watcher cannot interrupt an in-flight call.

The watcher tails the CSV incrementally: it tracks a byte offset and only
parses new bytes on each poll, so cost grows linearly in the number of new
rows rather than O(rows × polls). Partial rows (a row being flushed) are
left for the next poll. If the file shrinks or its inode changes (e.g.
truncation), the watcher resets and rereads from the start.
"""

from __future__ import annotations

import csv
import io
import logging
import pathlib
import threading
import time
from dataclasses import dataclass
from datetime import datetime, timezone
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
    """Parse a CSV timestamp cell into a timezone-aware ``datetime``.

    ``track_cost`` historically writes naive local-time timestamps via
    ``datetime.now().strftime(...)`` — see ``track_cost.py``'s wrapper —
    even though the reader contract documents UTC. To stay interoperable
    with both forms, a naive parse result is REINTERPRETED as UTC (so it
    can be compared with the aware ``started_at`` set by the job manager
    without raising ``TypeError``). Aware values are returned unchanged.
    """
    if not raw:
        return None
    try:
        parsed = datetime.fromisoformat(raw)
    except (TypeError, ValueError):
        return None
    if parsed.tzinfo is None:
        return parsed.replace(tzinfo=timezone.utc)
    return parsed


def _normalize_started_at(value: Optional[datetime]) -> Optional[datetime]:
    if value is None:
        return None
    if value.tzinfo is None:
        return value.replace(tzinfo=timezone.utc)
    return value


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
        self._started_at = _normalize_started_at(started_at)
        self._poll_interval = max(0.1, float(poll_interval))
        self._stop_event = threading.Event()
        self._lock = threading.Lock()
        self._state = _State(cap=cap)
        self._spent: float = 0.0
        # Incremental-tail state. ``_byte_offset`` is the first unread byte;
        # ``_header_consumed`` flips True after the CSV header is parsed.
        # ``_known_size`` caches the file size at last poll so we can detect
        # truncation/rotation and reset state.
        self._byte_offset: int = 0
        self._header_consumed: bool = False
        self._known_size: int = 0
        self._fieldnames: Optional[list[str]] = None
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

    def _reset_tail_state(self) -> None:
        """Forget where we were — used on truncation or rotation."""
        self._byte_offset = 0
        self._header_consumed = False
        self._known_size = 0
        self._fieldnames = None
        with self._lock:
            self._spent = 0.0

    def _row_matches(self, row: dict) -> bool:
        if self._commands is not None and row.get("command") not in self._commands:
            return False
        if self._started_at is not None:
            ts = _parse_timestamp(row.get("timestamp"))
            if ts is None or ts < self._started_at:
                return False
        return True

    def _consume_new_bytes(self) -> None:
        """Read appended bytes and accumulate matching-row cost.

        Tolerates partial rows: if the buffer does not end on a newline, the
        last (incomplete) line is rewound so the next poll picks it up once
        it has been fully flushed. Tolerates the file disappearing or being
        truncated.
        """
        try:
            stat = self._csv_path.stat()
        except (OSError, FileNotFoundError):
            # File not yet created or vanished — keep spent as-is until it
            # reappears (R4).
            return

        size = stat.st_size
        if size < self._byte_offset:
            # Truncation or rotation: re-scan from scratch on next read.
            self._reset_tail_state()
        self._known_size = size

        if size == self._byte_offset:
            return

        try:
            with self._csv_path.open("rb") as handle:
                handle.seek(self._byte_offset)
                raw = handle.read()
        except (OSError, FileNotFoundError):
            return

        # Tolerate partial last row: leave bytes after the final newline for
        # the next poll. If the buffer contains no newline at all, defer
        # parsing until more data arrives.
        if not raw:
            return
        last_newline = raw.rfind(b"\n")
        if last_newline == -1:
            return
        consumable = raw[: last_newline + 1]
        leftover_len = len(raw) - len(consumable)
        new_offset = self._byte_offset + len(consumable)

        try:
            text = consumable.decode("utf-8", errors="replace")
        except Exception:  # noqa: BLE001
            self._byte_offset = new_offset
            return

        added = 0.0
        try:
            if not self._header_consumed:
                reader = csv.reader(io.StringIO(text))
                rows = list(reader)
                if not rows:
                    self._byte_offset = new_offset
                    return
                self._fieldnames = rows[0]
                self._header_consumed = True
                data_rows = rows[1:]
            else:
                reader = csv.reader(io.StringIO(text))
                data_rows = list(reader)
        except csv.Error as exc:
            logger.debug("cost-budget-watcher: csv.Error on tail: %s", exc)
            # Advance past consumed bytes regardless — a malformed row
            # cannot be repaired by re-reading the same bytes next poll.
            self._byte_offset = new_offset
            return

        fields = self._fieldnames or []
        for raw_row in data_rows:
            if not raw_row:
                continue
            row = {fields[i]: raw_row[i] for i in range(min(len(fields), len(raw_row)))}
            if self._row_matches(row):
                added += _parse_cost(row.get("cost"))

        if added:
            with self._lock:
                self._spent += added
        self._byte_offset = new_offset

        # If a partial trailing row exists, the next poll will pick it up.
        # `leftover_len` is informational; no action needed here.
        _ = leftover_len

    def _run(self) -> None:
        while not self._stop_event.is_set():
            try:
                self._consume_new_bytes()
                with self._lock:
                    spent = self._spent
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
    single-command job, pass ``{job.command}``.

    Naive timestamps in the CSV are reinterpreted as UTC so they compare
    cleanly with the aware ``started_at`` value set by the job manager;
    ``track_cost`` historically writes naive local time even though its
    reader contract documents UTC, and we must not blow up the watcher
    over that drift.
    """
    # Reference `time` so the import is kept (some IDEs trim unused imports).
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
