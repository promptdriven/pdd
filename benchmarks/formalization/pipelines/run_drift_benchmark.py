#!/usr/bin/env python3
"""Milestone 3: regeneration drift via ``pdd checkup drift``."""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional

import yaml

_PIPELINE_DIR = Path(__file__).resolve().parent
_BENCHMARK_ROOT = _PIPELINE_DIR.parent
_REPO_ROOT = _BENCHMARK_ROOT.parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
if str(_PIPELINE_DIR) not in sys.path:
    sys.path.insert(0, str(_PIPELINE_DIR))

from command_log import append_jsonl  # noqa: E402
from economics import business_value_block  # noqa: E402


def _invoke_drift(
    *,
    devunit: str,
    project_root: Path,
    runs: int,
    evidence_path: Path,
    code_path: Path,
    dry_run: bool,
    max_cost_usd: Optional[float],
    log_path: Optional[Path],
) -> tuple[dict[str, Any], int]:
    """Call drift in-process (faster and reliable for benchmark harness)."""
    from pdd.drift_main import run_drift  # noqa: WPS433

    try:
        report = run_drift(
            devunit,
            project_root,
            runs=runs,
            from_evidence=evidence_path,
            code_file=code_path,
            dry_run=dry_run,
            max_cost_usd=max_cost_usd,
        )
    except (FileNotFoundError, RuntimeError) as exc:
        entry = {"error": str(exc), "exit_code": 1}
        append_jsonl(log_path, entry)
        return entry, 1

    payload = report.as_dict()
    append_jsonl(log_path, {"drift": payload, "exit_code": report.exit_code})
    return payload, report.exit_code


def _m3_tasks() -> list[dict[str, Any]]:
    raw = yaml.safe_load((_BENCHMARK_ROOT / "corpus" / "manifest.yaml").read_text(encoding="utf-8"))
    return [t for t in (raw.get("tasks") or []) if t.get("m3")]


def _rel_or_abs(path: Path, project_root: Path) -> str:
    try:
        return str(path.resolve().relative_to(project_root.resolve()))
    except ValueError:
        return str(path.resolve())


def _write_evidence_manifest(
    manifest_path: Path,
    *,
    project_root: Path,
    prompt_path: Path,
    code_path: Path,
) -> None:
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "schema_version": 1,
        "prompt": {"path": _rel_or_abs(prompt_path, project_root)},
        "outputs": [
            {
                "path": _rel_or_abs(code_path, project_root),
                "sha256": hashlib.sha256(code_path.read_bytes()).hexdigest(),
            }
        ],
        "validation": {
            "detect_stories": "not_available",
            "verify": "not_available",
            "unit_tests": "not_available",
        },
    }
    manifest_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def run_m3(
    *,
    output_dir: Path,
    m2_dir: Path,
    m1_dir: Path,
    task_ids: Optional[list[str]],
    runs: int,
    dry_run: bool,
    max_cost_usd: Optional[float],
) -> dict[str, Any]:
    tasks = _m3_tasks()
    if task_ids:
        tasks = [t for t in tasks if t["id"] in task_ids]
    output_dir.mkdir(parents=True, exist_ok=True)

    manifest: dict[str, Any] = {
        "milestone": 3,
        "started_at": datetime.now(timezone.utc).isoformat(),
        "business_value": business_value_block(),
        "runs": runs,
        "dry_run": dry_run,
        "m2_dir": str(m2_dir),
        "m1_dir": str(m1_dir),
        "tasks": [],
    }
    total_cost = 0.0

    for entry in tasks:
        task_id = entry["id"]
        module = entry.get("module", task_id)
        task_out = output_dir / task_id
        task_out.mkdir(parents=True, exist_ok=True)
        arms_out: dict[str, Any] = {}

        for arm in ("A0", "A1"):
            code_file = m2_dir / task_id / arm / "generated" / "src" / f"{module}.py"
            prompt_file = (
                (_BENCHMARK_ROOT / "corpus" / entry["a0"]).resolve()
                if arm == "A0"
                else (m1_dir / task_id / "A1.prompt")
            )
            if not code_file.is_file():
                arms_out[arm] = {
                    "error": f"missing code {code_file}; run M2 first",
                    "regen_runs": None,
                    "behavior_stability": None,
                }
                continue
            if not prompt_file.is_file():
                arms_out[arm] = {
                    "error": f"missing prompt {prompt_file}",
                    "regen_runs": None,
                    "behavior_stability": None,
                }
                continue

            evidence_path = task_out / f"evidence_{arm}.json"
            _write_evidence_manifest(
                evidence_path,
                project_root=_REPO_ROOT,
                prompt_path=prompt_file,
                code_path=code_file,
            )

            log_path = task_out / f"drift_{arm}_commands.jsonl"
            drift_json, exit_code = _invoke_drift(
                devunit=module,
                project_root=_REPO_ROOT,
                runs=runs,
                evidence_path=evidence_path,
                code_path=code_file,
                dry_run=dry_run,
                max_cost_usd=max_cost_usd,
                log_path=log_path,
            )

            behavior = drift_json.get("behavior_unchanged")
            stable = drift_json.get("status") == "stable"
            arms_out[arm] = {
                "code_file": str(code_file),
                "prompt_file": str(prompt_file),
                "evidence": str(evidence_path),
                "drift": drift_json,
                "drift_exit_code": exit_code,
                "regen_runs": runs if not dry_run else 0,
                "behavior_stability": 1.0 if behavior else (0.0 if behavior is False else None),
                "drift_score": 1.0 if stable else (0.0 if stable is False else None),
            }
            total_cost += float(drift_json.get("total_cost_usd") or 0)

        (task_out / "result.json").write_text(
            json.dumps({"task_id": task_id, "arms": arms_out}, indent=2) + "\n"
        )
        manifest["tasks"].append({"task_id": task_id, "arms": arms_out})

    manifest["finished_at"] = datetime.now(timezone.utc).isoformat()
    manifest["total_cost_usd"] = round(total_cost, 4)
    summary = _build_m3_summary(manifest["tasks"])
    manifest["summary"] = summary
    (output_dir / "run_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    (output_dir / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    _write_m3_report_md(output_dir / "REPORT.md", summary, manifest)
    return manifest


def _build_m3_summary(task_records: list[dict[str, Any]]) -> dict[str, Any]:
    """Aggregate drift outcomes across tasks and arms."""
    stable_a0 = stable_a1 = 0
    count_a0 = count_a1 = 0
    headlines: list[str] = []

    for task in task_records:
        tid = task.get("task_id", "?")
        arms = task.get("arms") or {}
        parts = [tid]
        for arm in ("A0", "A1"):
            data = arms.get(arm) or {}
            if "error" in data:
                parts.append(f"{arm}=error")
                continue
            drift = data.get("drift") or {}
            status = drift.get("status", "unknown")
            parts.append(f"{arm}={status}")
            if arm == "A0":
                count_a0 += 1
                if status == "stable":
                    stable_a0 += 1
            else:
                count_a1 += 1
                if status == "stable":
                    stable_a1 += 1
        headlines.append(" ".join(parts))

    return {
        "milestone": 3,
        "task_count": len(task_records),
        "a0_stable_count": stable_a0,
        "a1_stable_count": stable_a1,
        "a0_arm_count": count_a0,
        "a1_arm_count": count_a1,
        "headline": "; ".join(headlines),
        "claim": (
            "M3 measures regeneration drift after M2 code exists. "
            "Live runs require --allow-llm; dry-run validates harness only."
        ),
    }


def _write_m3_report_md(path: Path, summary: dict[str, Any], manifest: dict[str, Any]) -> None:
    lines = [
        "# M3 — Regeneration Drift Report",
        "",
        f"**Mode:** {'dry-run' if manifest.get('dry_run') else 'live regen'} · "
        f"**Runs:** {manifest.get('runs')} · **M2:** `{manifest.get('m2_dir')}`",
        "",
        f"**Tasks:** {summary['task_count']} · "
        f"A0 stable: {summary['a0_stable_count']}/{summary['a0_arm_count']} · "
        f"A1 stable: {summary['a1_stable_count']}/{summary['a1_arm_count']}",
        "",
        f"**Headline:** {summary['headline']}",
        "",
        summary.get("claim", ""),
    ]
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="M3 drift stability benchmark")
    parser.add_argument("--output-dir", type=Path, default=_BENCHMARK_ROOT / "experiments" / "m3_latest")
    parser.add_argument("--m2-dir", type=Path, default=_BENCHMARK_ROOT / "experiments" / "m2_latest")
    parser.add_argument("--m1-dir", type=Path, default=_BENCHMARK_ROOT / "experiments" / "latest")
    parser.add_argument("--tasks", type=str, default=None)
    parser.add_argument("--runs", type=int, default=1)
    parser.add_argument("--dry-run", action="store_true", help="Compare current artifact only (no regen)")
    parser.add_argument("--allow-llm", action="store_true", help="Allow paid regeneration runs (not for CI)")
    parser.add_argument("--max-cost-usd", type=float, default=20.0)
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    if args.runs < 1:
        parser.error("--runs must be at least 1")
    if not args.allow_llm and not args.dry_run:
        parser.error("M3 regen requires --allow-llm unless --dry-run")

    task_ids = [t.strip() for t in args.tasks.split(",")] if args.tasks else None
    manifest = run_m3(
        output_dir=args.output_dir.resolve(),
        m2_dir=args.m2_dir.resolve(),
        m1_dir=args.m1_dir.resolve(),
        task_ids=task_ids,
        runs=args.runs,
        dry_run=args.dry_run,
        max_cost_usd=args.max_cost_usd,
    )
    if args.as_json:
        print(json.dumps(manifest, indent=2))
    else:
        print(f"M3 complete → {args.output_dir}")
        if manifest.get("summary"):
            print(f"  {manifest['summary'].get('headline', '')}")
        print(f"  Report: {args.output_dir / 'REPORT.md'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
