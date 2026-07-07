"""Experiment runner: variant materialization, orchestration, metrics, report.

Design.md §3.2 stages 3-5. Runs are valid without the optional FS tap
(``fs_tap_enabled: false``); primary evidence comes from the context-snapshot
tap (harness.context_snapshots) per the v2 instrumentation tiering.
"""

from .metrics import build_run_record, classify_failure
from .report import generate_report
from .runner import ExperimentRunner, RunConfig
from .variant_builder import materialize_variant

__all__ = [
    "build_run_record",
    "classify_failure",
    "generate_report",
    "ExperimentRunner",
    "RunConfig",
    "materialize_variant",
]
