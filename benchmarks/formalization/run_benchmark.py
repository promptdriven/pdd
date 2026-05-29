#!/usr/bin/env python3
"""Run the PDD formalization benchmark.

Usage::

    python benchmarks/formalization/run_benchmark.py
    python benchmarks/formalization/run_benchmark.py --report
    python benchmarks/formalization/run_benchmark.py --report-only
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

_BENCH_DIR = Path(__file__).resolve().parent
if str(_BENCH_DIR) not in sys.path:
    sys.path.insert(0, str(_BENCH_DIR))

from _report import load_aggregate, write_summary_artifacts  # pylint: disable=wrong-import-position
from _runner import (  # pylint: disable=wrong-import-position
    benchmark_root,
    finalize_benchmark,
    run_benchmark,
    validate_run_payload,
)


def main(argv: list[str] | None = None) -> int:
    """CLI entry point."""
    root = benchmark_root()
    parser = argparse.ArgumentParser(
        description="Run PDD formalization benchmark (issue #1273).",
    )
    parser.add_argument(
        "--tasks",
        nargs="*",
        default=None,
        help="Task ids to run (default: all under tasks/).",
    )
    parser.add_argument(
        "--arms",
        nargs="*",
        choices=["A0", "A1", "A2"],
        default=None,
        help="Benchmark arms to run (default: A0 A1 A2).",
    )
    parser.add_argument(
        "--results-dir",
        type=Path,
        default=root / "results",
        help="Directory for JSON output (default: benchmarks/formalization/results).",
    )
    parser.add_argument(
        "--validate-only",
        type=Path,
        default=None,
        metavar="RUN_JSON",
        help="Validate an existing run JSON against the schema and exit.",
    )
    parser.add_argument(
        "--report",
        action="store_true",
        help="After run, write summary.json + REPORT.md and print comparison table.",
    )
    parser.add_argument(
        "--report-only",
        action="store_true",
        help="Build report from existing aggregate.json (no benchmark re-run).",
    )
    args = parser.parse_args(argv)

    schema_path = root / "schemas" / "results.schema.json"
    results_dir = args.results_dir.resolve()

    if args.validate_only is not None:
        payload = json.loads(args.validate_only.read_text(encoding="utf-8"))
        validate_run_payload(payload, schema_path)
        print(f"OK: {args.validate_only}")
        return 0

    if args.report_only:
        aggregate = load_aggregate(results_dir)
        write_summary_artifacts(aggregate, results_dir, print_report=True)
        print(f"Wrote {results_dir / 'summary.json'} and {results_dir / 'REPORT.md'}")
        return 0

    aggregate = run_benchmark(
        tasks_dir=root / "tasks",
        results_dir=results_dir,
        task_ids=args.tasks,
        arms=args.arms,
    )
    for run in aggregate["runs"]:
        validate_run_payload(run, schema_path)

    exit_code = 0 if all(run["command_success"] for run in aggregate["runs"]) else 1

    print(
        f"Wrote {len(aggregate['runs'])} run(s) under {results_dir} (aggregate.json)."
    )

    if args.report:
        finalize_benchmark(aggregate, results_dir, emit_report=True)
        print(f"Wrote {results_dir / 'summary.json'} and {results_dir / 'REPORT.md'}")
    else:
        print("Tip: pass --report for A0 vs A1 comparison table and TEF scores.")

    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
