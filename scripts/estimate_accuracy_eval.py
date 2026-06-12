#!/usr/bin/env python3
"""Opt-in live accuracy evaluation for PDD estimate mode.

Each case is a JSON object with:

    {"name": "tiny-generate", "command": ["generate", "--output", "out.py", "prompt.prompt"]}

The command is the PDD subcommand and its arguments, without global flags.
This script runs:

    python -m pdd --estimate-json --no-core-dump <command...>
    python -m pdd --force --no-core-dump --output-cost <csv> <command...>

Live execution is disabled unless --allow-live is passed or
PDD_LIVE_ESTIMATE_EVAL=1 is set. For no-spend accuracy checks, pass
``--actuals recorded_actuals.jsonl``. Each actuals row is keyed by ``name`` and
contains ``actual_input_tokens``, ``actual_output_tokens``, and ``actual_cost``.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import statistics
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _load_cases(path: Path) -> list[dict[str, Any]]:
    cases: list[dict[str, Any]] = []
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        payload = json.loads(stripped)
        if not isinstance(payload, dict):
            raise ValueError(f"{path}:{line_no}: case must be a JSON object")
        if not isinstance(payload.get("command"), list):
            raise ValueError(f"{path}:{line_no}: command must be a list")
        payload.setdefault("name", f"case-{line_no}")
        cases.append(payload)
    return cases


def _load_actuals(path: Path | None) -> dict[str, dict[str, float]]:
    if path is None:
        return {}

    actuals: dict[str, dict[str, float]] = {}
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        payload = json.loads(stripped)
        if not isinstance(payload, dict):
            raise ValueError(f"{path}:{line_no}: actual row must be a JSON object")
        name = payload.get("name")
        if not isinstance(name, str) or not name:
            raise ValueError(f"{path}:{line_no}: actual row requires non-empty name")
        actuals[name] = {
            "input_tokens": float(
                payload.get("actual_input_tokens", payload.get("input_tokens", 0.0))
            ),
            "output_tokens": float(
                payload.get("actual_output_tokens", payload.get("output_tokens", 0.0))
            ),
            "cost": float(payload.get("actual_cost", payload.get("cost", 0.0))),
        }
    return actuals


def _run_pdd(command: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-m", "pdd", *command],
        cwd=cwd,
        text=True,
        capture_output=True,
        check=False,
    )


def _extract_estimate(stdout: str) -> dict[str, Any]:
    for line in stdout.splitlines():
        stripped = line.strip()
        if not stripped.startswith("{"):
            continue
        try:
            payload = json.loads(stripped)
        except json.JSONDecodeError:
            continue
        if isinstance(payload, dict) and payload.get("estimate") is True:
            return payload
    raise ValueError("estimate JSON payload not found in stdout")


def _read_actual_cost_csv(path: Path) -> dict[str, float]:
    totals = {"input_tokens": 0.0, "output_tokens": 0.0, "cost": 0.0}
    if not path.exists():
        return totals
    with path.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            for key in totals:
                raw = row.get(key) or row.get(key.title()) or ""
                try:
                    totals[key] += float(raw)
                except (TypeError, ValueError):
                    pass
    return totals


def _ape(estimate: float | None, actual: float, *, cost: bool = False) -> float | None:
    if estimate is None:
        return None
    denominator = max(abs(actual), 0.000001 if cost else 1.0)
    return abs(float(estimate) - actual) / denominator


def _percentile(values: list[float], pct: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    if len(ordered) == 1:
        return ordered[0]
    rank = (len(ordered) - 1) * pct
    lower = int(rank)
    upper = min(lower + 1, len(ordered) - 1)
    weight = rank - lower
    return ordered[lower] * (1 - weight) + ordered[upper] * weight


def _format_pct(value: float | None) -> str:
    return "unknown" if value is None else f"{value * 100:.1f}%"


def _build_row(
    *,
    name: str,
    estimate: dict[str, Any],
    actual: dict[str, float] | None,
    actual_error: str | None = None,
) -> dict[str, Any]:
    actual_available = actual is not None and actual_error is None
    actual_values = actual or {"input_tokens": 0.0, "output_tokens": 0.0, "cost": 0.0}
    return {
        "name": name,
        "estimate_input_tokens": estimate.get("input_tokens"),
        "actual_input_tokens": actual_values["input_tokens"] if actual_available else None,
        "input_ape": (
            _ape(estimate.get("input_tokens"), actual_values["input_tokens"])
            if actual_available
            else None
        ),
        "estimate_output_tokens": estimate.get("predicted_output_tokens"),
        "actual_output_tokens": actual_values["output_tokens"] if actual_available else None,
        "output_ape": (
            _ape(
                estimate.get("predicted_output_tokens"),
                actual_values["output_tokens"],
            )
            if actual_available
            else None
        ),
        "estimate_cost": estimate.get("estimated_cost"),
        "actual_cost": actual_values["cost"] if actual_available else None,
        "cost_ape": (
            _ape(
                estimate.get("estimated_cost"),
                actual_values["cost"],
                cost=True,
            )
            if actual_available
            else None
        ),
        "unknown_cost": estimate.get("unknown_cost"),
        "actual_error": actual_error,
    }


def _summarize(rows: list[dict[str, Any]], *, live_allowed: bool, replay_actuals: bool) -> dict[str, Any]:
    metric_apes = [
        value
        for row in rows
        for value in (row.get("input_ape"), row.get("output_ape"), row.get("cost_ape"))
        if isinstance(value, float)
    ]
    median_ape = statistics.median(metric_apes) if metric_apes else None
    p80_ape = _percentile(metric_apes, 0.80)
    p95_ape = _percentile(metric_apes, 0.95)
    return {
        "estimate": True,
        "live_actuals": live_allowed,
        "replay_actuals": replay_actuals,
        "rows": rows,
        "median_ape": median_ape,
        "p80_ape": p80_ape,
        "p95_ape": p95_ape,
        "passes_target": (
            bool(metric_apes)
            and median_ape is not None
            and p80_ape is not None
            and p95_ape is not None
            and median_ape <= 0.15
            and p80_ape <= 0.15
            and p95_ape <= 0.25
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cases", required=True, type=Path, help="JSONL case file")
    parser.add_argument(
        "--actuals",
        type=Path,
        default=None,
        help="JSONL recorded actual usage keyed by case name; avoids live provider calls.",
    )
    parser.add_argument("--cwd", type=Path, default=Path.cwd(), help="PDD project cwd")
    parser.add_argument(
        "--allow-live",
        action="store_true",
        help="Allow actual provider executions. Otherwise only estimates are run.",
    )
    parser.add_argument(
        "--fail-on-threshold",
        action="store_true",
        help="Exit 1 when computed APE percentiles do not meet the target.",
    )
    args = parser.parse_args()

    live_allowed = args.allow_live or os.getenv("PDD_LIVE_ESTIMATE_EVAL") == "1"
    cases = _load_cases(args.cases)
    recorded_actuals = _load_actuals(args.actuals)
    if not cases:
        raise SystemExit("no cases found")
    if recorded_actuals:
        live_allowed = False

    rows: list[dict[str, Any]] = []
    with tempfile.TemporaryDirectory(prefix="pdd-estimate-accuracy-") as tmp:
        tmp_path = Path(tmp)
        for case in cases:
            name = str(case["name"])
            command = [str(item) for item in case["command"]]
            estimate_result = _run_pdd(
                ["--estimate-json", "--no-core-dump", *command],
                cwd=args.cwd,
            )
            if estimate_result.returncode != 0:
                rows.append({"name": name, "error": estimate_result.stderr or estimate_result.stdout})
                continue
            estimate = _extract_estimate(estimate_result.stdout)

            actual: dict[str, float] | None = recorded_actuals.get(name)
            actual_error = None
            if actual is None and live_allowed:
                cost_csv = tmp_path / f"{name}.csv"
                actual_result = _run_pdd(
                    [
                        "--force",
                        "--no-core-dump",
                        "--output-cost",
                        str(cost_csv),
                        *command,
                    ],
                    cwd=args.cwd,
                )
                if actual_result.returncode != 0:
                    actual_error = actual_result.stderr or actual_result.stdout
                actual = _read_actual_cost_csv(cost_csv)

            rows.append(
                _build_row(
                    name=name,
                    estimate=estimate,
                    actual=actual,
                    actual_error=actual_error,
                )
            )

    summary = _summarize(
        rows,
        live_allowed=live_allowed,
        replay_actuals=bool(recorded_actuals),
    )

    print(json.dumps(summary, indent=2, sort_keys=True))
    print(
        "summary: "
        f"median={_format_pct(summary['median_ape'])} "
        f"p80={_format_pct(summary['p80_ape'])} "
        f"p95={_format_pct(summary['p95_ape'])} "
        f"passes={summary['passes_target']}",
        file=sys.stderr,
    )
    if not live_allowed:
        if recorded_actuals:
            print("using recorded actuals; no provider executions performed", file=sys.stderr)
        else:
            print(
                "actual provider executions skipped; pass --allow-live, set "
                "PDD_LIVE_ESTIMATE_EVAL=1, or pass --actuals",
                file=sys.stderr,
            )
    if args.fail_on_threshold and not summary["passes_target"]:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
