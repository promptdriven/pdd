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


__all__ = ["watch", "Watcher", "read_spent_now"]


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
    """Parse a CSV timestamp cell into a timezone-aware UTC ``datetime``.

    Current ``track_cost`` writes UTC-aware ISO strings (e.g.
    ``2026-05-22T18:30:00.123+00:00``) — see ``track_cost.py``'s wrapper.
    Legacy CSV files (rows written before the UTC fix) contain NAIVE
    local-time strings; ``datetime.now().strftime(...)`` produces them.
    Naive cells are reinterpreted as LOCAL time and converted to UTC
    (NOT reinterpreted as UTC outright — that would shift every row by
    the local UTC offset and silently misattribute spend to the wrong
    job window). Aware values are converted to UTC for a uniform
    comparison frame.
    """
    if not raw:
        return None
    try:
        parsed = datetime.fromisoformat(raw)
    except (TypeError, ValueError):
        return None
    if parsed.tzinfo is None:
        # naive.astimezone() treats the value as local time and converts
        # to the target timezone — exactly the right interop for legacy
        # naive cells produced by datetime.now().strftime(...).
        return parsed.astimezone(timezone.utc)
    return parsed.astimezone(timezone.utc)


def _normalize_started_at(value: Optional[datetime]) -> Optional[datetime]:
    """Coerce to aware UTC AND truncate to millisecond precision.

    ``track_cost`` writes timestamps via
    ``datetime.now(timezone.utc).isoformat(timespec='milliseconds')``,
    which truncates the microsecond field to multiples of 1000. The
    caller's ``started_at`` (typically ``datetime.now(timezone.utc)``
    from the job manager) has microsecond precision, so a row written
    in the SAME millisecond as ``started_at`` ends up with a timestamp
    strictly less than ``started_at`` and would otherwise be silently
    dropped by the ``ts < started_at`` check. Truncating to ms here
    aligns the two precisions so legitimately-current rows always
    pass the filter.
    """
    if value is None:
        return None
    if value.tzinfo is None:
        value = value.replace(tzinfo=timezone.utc)
    return value.replace(microsecond=(value.microsecond // 1000) * 1000)


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
        job_id: Optional[str] = None,
    ) -> None:
        self._csv_path = pathlib.Path(csv_path)
        self._on_exceeded = on_exceeded
        self._commands: Optional[FrozenSet[str]] = (
            frozenset(commands) if commands is not None else None
        )
        self._started_at = _normalize_started_at(started_at)
        self._poll_interval = max(0.1, float(poll_interval))
        # When set, only count rows whose `job_id` column matches. Rows
        # written by older track_cost (no `job_id` column) are skipped
        # rather than counted, so concurrent same-command jobs sharing
        # a CSV cannot count each other's spend. Pass job_id=None to
        # preserve the legacy command+timestamp filter behaviour.
        self._job_id = job_id
        self._stop_event = threading.Event()
        # RLock so callers that already hold the lock (e.g. internal
        # state read inside _consume_new_bytes) can re-enter without
        # deadlock. Both the daemon thread's poll loop AND inline
        # flush() callers serialise through this single lock to
        # prevent double-counting the same CSV bytes.
        self._lock = threading.RLock()
        self._state = _State(cap=cap)
        self._spent: float = 0.0
        # Incremental-tail state. ``_byte_offset`` is the first unread byte;
        # ``_header_consumed`` flips True after the CSV header is parsed.
        # ``_known_size`` caches the file size at last poll so we can detect
        # truncation/rotation and reset state. ``_known_inode`` lets us
        # detect ``os.replace``-style migrations (track_cost rewrites the
        # cost CSV in place to add the job_id column when the env asks
        # for per-job attribution; the new file gets a new inode even
        # though the path is unchanged). Without inode tracking the
        # watcher would keep its stale fieldnames and never enforce
        # the job_id filter even after migration.
        self._byte_offset: int = 0
        self._header_consumed: bool = False
        self._known_size: int = 0
        self._known_inode: Optional[int] = None
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

    def fired(self) -> bool:
        """Return ``True`` once ``on_exceeded`` has been scheduled by
        any path (daemon poll or inline ``flush``). Callers use this
        to distinguish "this flush() fired" (flush returns True) from
        "the daemon already fired and the handler may still be in
        flight" (``fired()`` True, ``flush()`` returns False). Without
        the second signal a final cleanup that calls flush() right
        after a daemon poll wins the race would see flush=False and
        skip the wait-for-terminal-status loop, letting the job's
        COMPLETED status race past the still-pending BUDGET_EXCEEDED
        handler.
        """
        with self._lock:
            return self._state.fired

    def flush(self) -> bool:
        """Synchronously consume any new bytes and fire ``on_exceeded``
        if the cap is now crossed. Returns ``True`` iff the callback
        fired on this call so the caller can await the resulting
        status change before proceeding.

        Callers use this to close two race windows:
          1. A subprocess writes its final cost row and exits before the
             daemon thread's next 2-second poll, so the cap is never
             observed and ``budget_exceeded`` never fires.
          2. A late ``/pdd budget N`` arrives on a previously-uncapped
             run that already wrote ``> N`` of spend, and the job
             exits before the daemon thread polls — enforcement
             silently misses the existing rows.

        ``flush()`` runs the same consume + check logic the daemon
        thread uses, but inline on the calling thread. The fire-once
        invariant (R1) is preserved by the same ``_state.fired`` flag.

        Note: a return of ``False`` does NOT mean the cap is uncrossed —
        the daemon thread may have already fired between two flush()
        calls. Use :meth:`fired` for that "fired-by-anyone" signal.
        """
        try:
            self._consume_new_bytes()
        except Exception:  # noqa: BLE001 - flush must not raise out
            logger.exception("cost-budget-watcher: flush consume error")
        with self._lock:
            spent = self._spent
            cap = self._state.cap
            fired = self._state.fired
        if cap is not None and not fired and spent >= cap:
            with self._lock:
                self._state.fired = True
            try:
                self._on_exceeded(spent)
            except Exception:  # noqa: BLE001
                logger.exception("cost-budget-watcher: flush on_exceeded raised")
            return True
        return False

    def stop(self) -> None:
        self._stop_event.set()

    # -------------------------------------------------------------- internal

    def _reset_tail_state(self) -> None:
        """Forget where we were — used on truncation or rotation."""
        self._byte_offset = 0
        self._header_consumed = False
        self._known_size = 0
        self._known_inode = None
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
        if self._job_id is not None and self._fieldnames and "job_id" in self._fieldnames:
            # Per-job attribution: only count rows whose `job_id` column
            # matches. We gate on "is `job_id` actually in the CSV
            # header" so legacy / mid-format CSVs (those without the
            # column) keep falling back to the command + timestamp
            # filter rather than dropping every row and freezing spend
            # at $0. Concurrent same-command jobs sharing a NEW-format
            # CSV are still per-job-isolated; concurrent jobs sharing
            # a LEGACY-format CSV are not (the caller opted into the
            # shared file).
            if row.get("job_id") != self._job_id:
                return False
        return True

    def _consume_new_bytes(self) -> None:
        """Read appended bytes and accumulate matching-row cost.

        Holds ``self._lock`` for the ENTIRE consume operation so the
        daemon-thread poll and any inline ``flush()`` caller cannot
        race on the same byte range. Without this serialisation, two
        concurrent calls would each read from the same ``_byte_offset``,
        each parse the same rows, and each increment ``_spent`` — a
        single $5 row could end up as $10 of "spend".

        Tolerates partial rows: if the buffer does not end on a newline, the
        last (incomplete) line is rewound so the next poll picks it up once
        it has been fully flushed. Tolerates the file disappearing or being
        truncated.
        """
        with self._lock:
            self._consume_new_bytes_locked()

    def _consume_new_bytes_locked(self) -> None:
        try:
            stat = self._csv_path.stat()
        except (OSError, FileNotFoundError):
            # File not yet created or vanished — keep spent as-is until it
            # reappears (R4).
            return

        size = stat.st_size
        # Detect file replacement (os.replace from track_cost migration,
        # logrotate-style rotation, etc.) by comparing the inode. A new
        # inode at the same path means a completely new file — discard
        # everything we cached (offset, header, spent) so the new
        # header is reparsed and the job_id filter activates if the
        # post-migration CSV carries the column. Without this, the
        # watcher keeps the pre-migration fieldnames and never enforces
        # job_id filtering even after the file is migrated.
        if (
            self._known_inode is not None
            and stat.st_ino != self._known_inode
        ):
            self._reset_tail_state()
        self._known_inode = stat.st_ino

        if size < self._byte_offset:
            # Truncation or rotation without inode change: re-scan from
            # scratch on next read.
            self._reset_tail_state()
            self._known_inode = stat.st_ino
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
            # Already inside self._lock via _consume_new_bytes; RLock
            # makes the nested acquire a no-op.
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


def read_spent_now(
    csv_path: pathlib.Path,
    *,
    commands: Optional[Iterable[str]] = None,
    started_at: Optional[datetime] = None,
    job_id: Optional[str] = None,
) -> float:
    """One-shot read of cumulative spend from ``csv_path``.

    PURE FUNCTION: no daemon thread, no shared state, no side effects.
    Used by callers that need the current spend without a long-lived
    watcher — notably ``JobManager.get_budget`` for both capless runs
    (no active watcher) and capped runs (where the daemon-thread cache
    can be up to ``poll_interval`` seconds stale and the user expects
    /pdd settings to be fresh).

    Filtering rules (commands set, ``started_at`` lower bound, optional
    ``job_id`` when the column is present in the header) match
    :class:`Watcher` exactly so results are consistent regardless of
    whether a watcher is also running.

    Previously this constructed a real :class:`Watcher`, which spun up a
    background daemon thread per call AND called ``_consume_new_bytes``
    inline; the two would race and double-count the same rows
    (reproduced: a $20,000 CSV reported as $40,000). The pure
    implementation has neither problem.
    """
    if not csv_path:
        return 0.0
    path = pathlib.Path(csv_path)
    if not path.exists():
        return 0.0
    commands_set: Optional[FrozenSet[str]] = (
        frozenset(commands) if commands is not None else None
    )
    started_norm = _normalize_started_at(started_at)
    total = 0.0
    try:
        with path.open("r", encoding="utf-8", newline="") as handle:
            reader = csv.DictReader(handle)
            fieldnames = reader.fieldnames or []
            has_job_id_col = "job_id" in fieldnames
            for row in reader:
                if commands_set is not None and row.get("command") not in commands_set:
                    continue
                if started_norm is not None:
                    ts = _parse_timestamp(row.get("timestamp"))
                    if ts is None or ts < started_norm:
                        continue
                if job_id is not None and has_job_id_col:
                    if row.get("job_id") != job_id:
                        continue
                total += _parse_cost(row.get("cost"))
    except (OSError, csv.Error):
        return total
    return total


def watch(
    csv_path: pathlib.Path,
    cap: Optional[float],
    on_exceeded: Callable[[float], None],
    *,
    commands: Optional[Iterable[str]] = None,
    started_at: Optional[datetime] = None,
    poll_interval: float = 2.0,
    job_id: Optional[str] = None,
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
        job_id=job_id,
    )
