#!/usr/bin/env python3
"""Run M2 (live or replay generation) then M3 drift in one command."""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Optional

_PIPELINE_DIR = Path(__file__).resolve().parent
_BENCHMARK_ROOT = _PIPELINE_DIR.parent
DEFAULT_M1 = _BENCHMARK_ROOT / "experiments" / "latest"
DEFAULT_M2 = _BENCHMARK_ROOT / "experiments" / "m2_latest"
DEFAULT_M3 = _BENCHMARK_ROOT / "experiments" / "m3_latest"


def _load_m2_manifest(m2_dir: Path) -> dict[str, Any]:
    path = m2_dir / "run_manifest.json"
    if not path.is_file():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def _write_pipeline_summary(
    path: Path,
    *,
    m2_dir: Path,
    m3_dir: Path,
    m2_manifest: dict[str, Any],
    m3_manifest: dict[str, Any],
    live: bool,
) -> None:
    """Merge M2 economics + M3 drift into one evaluation summary."""
    lines = [
        "# M2 → M3 pipeline result",
        "",
        "| Stage | Mode | Output |",
        "|-------|------|--------|",
        f"| M2 generation | {'live LLM' if live else 'harness/replay'} | `{m2_dir}` |",
        f"| M3 drift | {'live regen' if not m3_manifest.get('dry_run') else 'dry-run'} | `{m3_dir}` |",
        "",
        "## M2 generation (A0 vs A1)",
        "",
        "| Task | A0 oracle | A1 oracle | Δ oracle | A0 rounds | A1 rounds |",
        "|------|-----------|-----------|----------|-----------|-----------|",
    ]
    for task in m2_manifest.get("tasks") or []:
        tid = task.get("task_id", "?")
        arms = task.get("arms") or {}
        a0 = (arms.get("A0") or {}).get("economics") or {}
        a1 = (arms.get("A1") or {}).get("economics") or {}
        o0 = a0.get("oracle_test_pass_rate")
        o1 = a1.get("oracle_test_pass_rate")
        delta = (o1 or 0) - (o0 or 0) if o0 is not None and o1 is not None else None
        lines.append(
            f"| {tid} | {o0 if o0 is not None else '—'} | {o1 if o1 is not None else '—'} | "
            f"{delta if delta is not None else '—'} | "
            f"{a0.get('rounds_to_acceptable', '—')} | {a1.get('rounds_to_acceptable', '—')} |"
        )

    lines.extend(
        [
            "",
            "## M3 drift stability",
            "",
            "| Task | Arm | Status | Behavior | Drift score |",
            "|------|-----|--------|----------|-------------|",
        ]
    )
    for task in m3_manifest.get("tasks") or []:
        tid = task.get("task_id", "?")
        for arm, data in (task.get("arms") or {}).items():
            if "error" in data:
                lines.append(f"| {tid} | {arm} | error | — | — |")
                continue
            drift = data.get("drift") or {}
            lines.append(
                f"| {tid} | {arm} | {drift.get('status', '—')} | "
                f"{data.get('behavior_stability', '—')} | {data.get('drift_score', '—')} |"
            )

    m2_cost = m2_manifest.get("total_cost_usd")
    m3_cost = m3_manifest.get("total_cost_usd")
    lines.extend(
        [
            "",
            f"**M2 cost:** ${m2_cost if m2_cost is not None else '—'} · "
            f"**M3 cost:** ${m3_cost if m3_cost is not None else '—'}",
            "",
            "M3 consumes **live or replayed** M2 code under `<task>/<arm>/generated/src/`. "
            "Use `--allow-llm` for real `pdd generate` (M2) and regen drift (M3).",
        ]
    )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _run_step(cmd: list[str], *, as_json: bool) -> None:
    if as_json:
        proc = subprocess.run(cmd, check=True, capture_output=True, text=True)
        if proc.stderr:
            sys.stderr.write(proc.stderr)
    else:
        subprocess.run(cmd, check=True)


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="M2 → M3 pipeline (live generation + drift, or CI replay)",
    )
    parser.add_argument("--m1-dir", type=Path, default=DEFAULT_M1)
    parser.add_argument("--m2-dir", type=Path, default=DEFAULT_M2)
    parser.add_argument("--m3-dir", type=Path, default=DEFAULT_M3)
    parser.add_argument("--tasks", type=str, default=None, help="Comma-separated m3 task ids")
    parser.add_argument(
        "--allow-llm",
        action="store_true",
        help="Live pdd generate (M2) + regen drift (M3)",
    )
    parser.add_argument(
        "--replay-fixtures",
        action="store_true",
        help="M2: replay tier_gold pdd_generated; M3: dry-run drift (CI-safe)",
    )
    parser.add_argument("--dry-run", action="store_true", help="M3 only: compare artifact, no regen")
    parser.add_argument("--runs", type=int, default=1, help="M3 regeneration runs per arm")
    parser.add_argument("--max-rounds", type=int, default=3, help="M2 fix rounds")
    parser.add_argument("--max-cost-usd-m2", type=float, default=50.0, help="M2 budget cap")
    parser.add_argument("--max-cost-usd-m3", type=float, default=20.0, help="M3 budget cap")
    parser.add_argument(
        "--save-fixtures",
        action="store_true",
        help="Persist live M2 outputs to tier_gold",
    )
    parser.add_argument("--skip-m2", action="store_true", help="Use existing M2 output directory")
    parser.add_argument("--skip-m3", action="store_true", help="Run M2 only")
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    if args.runs < 1:
        parser.error("--runs must be at least 1")

    py = sys.executable
    task_args = ["--tasks", args.tasks] if args.tasks else []
    live_m2 = args.allow_llm and not args.replay_fixtures
    m3_dry_run = args.dry_run or args.replay_fixtures or not args.allow_llm

    if args.replay_fixtures and args.allow_llm:
        parser.error("Use --replay-fixtures (CI) OR --allow-llm (live), not both")

    if not args.skip_m2:
        m2_cmd = [
            py,
            str(_PIPELINE_DIR / "run_generation_benchmark.py"),
            "--output-dir",
            str(args.m2_dir),
            "--m1-dir",
            str(args.m1_dir),
            *task_args,
            "--max-rounds",
            str(args.max_rounds),
            "--skip-formalize",
        ]
        if args.replay_fixtures:
            m2_cmd.extend(["--replay-fixtures", "--harness-only"])
        elif args.allow_llm:
            m2_cmd.extend(["--allow-llm", "--max-cost-usd", str(args.max_cost_usd_m2)])
            if args.save_fixtures:
                m2_cmd.append("--save-fixtures")
        else:
            parser.error("M2 requires --allow-llm, --replay-fixtures, or --skip-m2")
        if args.as_json:
            m2_cmd.append("--json")
        _run_step(m2_cmd, as_json=args.as_json)

    m3_manifest: dict[str, Any] = {}
    if not args.skip_m3:
        m3_cmd = [
            py,
            str(_PIPELINE_DIR / "run_drift_benchmark.py"),
            "--output-dir",
            str(args.m3_dir),
            "--m2-dir",
            str(args.m2_dir),
            "--m1-dir",
            str(args.m1_dir),
            *task_args,
            "--runs",
            str(args.runs),
            "--max-cost-usd",
            str(args.max_cost_usd_m3),
        ]
        if m3_dry_run:
            m3_cmd.append("--dry-run")
        else:
            m3_cmd.append("--allow-llm")
        if args.as_json:
            m3_cmd.append("--json")
        _run_step(m3_cmd, as_json=args.as_json)
        m3_manifest = json.loads((args.m3_dir / "run_manifest.json").read_text(encoding="utf-8"))

    m2_manifest = _load_m2_manifest(args.m2_dir)
    summary_path = (
        args.m3_dir / "PIPELINE_RESULT.md"
        if not args.skip_m3
        else args.m2_dir / "PIPELINE_RESULT.md"
    )
    if not args.skip_m3 or not args.skip_m2:
        _write_pipeline_summary(
            summary_path,
            m2_dir=args.m2_dir,
            m3_dir=args.m3_dir,
            m2_manifest=m2_manifest,
            m3_manifest=m3_manifest,
            live=live_m2,
        )

    payload = {
        "m2_dir": str(args.m2_dir),
        "m3_dir": str(args.m3_dir),
        "live_m2": live_m2,
        "m3_dry_run": m3_dry_run,
        "m2_total_cost_usd": m2_manifest.get("total_cost_usd"),
        "m3_total_cost_usd": m3_manifest.get("total_cost_usd"),
        "summary": str(summary_path),
    }
    out_manifest = args.m3_dir if not args.skip_m3 else args.m2_dir
    out_manifest.mkdir(parents=True, exist_ok=True)
    (out_manifest / "pipeline_manifest.json").write_text(
        json.dumps(payload, indent=2) + "\n",
        encoding="utf-8",
    )

    if args.as_json:
        print(json.dumps(payload, indent=2))
    else:
        mode = "live" if live_m2 else "replay"
        print(f"M2 → M3 complete ({mode})")
        print(f"  M2: {args.m2_dir}")
        if not args.skip_m3:
            print(f"  M3: {args.m3_dir}")
        print(f"  Summary: {summary_path}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
