"""Context-snapshot instrumentation (design.md §6.2, tap 1).

The primary instrument of the v2 design: an API-boundary recording proxy that
captures the byte-exact composed context of every model request, plus the
analysis pieces that turn the per-request snapshot series into the metric
families the design pre-registers (penetration, iteration trajectory / H2).
"""

from .attribution import Attribution, TreeIndex
from .iteration_analyzer import IterationPoint, RunTrajectory, analyze_run
from .proxy import RecordingProxy
from .schema import SnapshotRecord, read_snapshots, write_snapshots
from .session_parser import SessionSummary, parse_session_log, reconcile

__all__ = [
    "Attribution",
    "TreeIndex",
    "IterationPoint",
    "RunTrajectory",
    "analyze_run",
    "RecordingProxy",
    "SnapshotRecord",
    "read_snapshots",
    "write_snapshots",
    "SessionSummary",
    "parse_session_log",
    "reconcile",
]
