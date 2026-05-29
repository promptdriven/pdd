#!/usr/bin/env python3
"""Batch Milestone 1 experiment: score A0, formalize to A1, score A1, write summary."""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
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

import formalize_a1  # noqa: E402
import prompt_metrics  # noqa: E402

EXPERIMENT_VERSION = "m1_v1"
DEFAULT_OUTPUT = _BENCHMARK_ROOT / "experiments" / "latest"


def _git_sha(project_root: Path) -> str:
    try:
        proc = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=project_root,
            capture_output=True,
            text=True,
            check=False,
        )
        if proc.returncode == 0:
            return proc.stdout.strip()
    except OSError:
        pass
    return "unknown"


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_corpus_manifest(manifest_path: Path) -> list[dict[str, Any]]:
    """Load task entries from corpus/manifest.yaml."""
    raw = yaml.safe_load(manifest_path.read_text(encoding="utf-8")) or {}
    tasks = raw.get("tasks") or []
    if not tasks:
        raise ValueError(f"No tasks in {manifest_path}")
    return list(tasks)


def run_experiment(
    *,
    output_dir: Path,
    task_ids: Optional[list[str]],
    allow_llm: bool,
    dry_run: bool,
    max_cost_usd: Optional[float],
    project_root: Path,
    verbose: bool,
) -> dict[str, Any]:
    """Run M1 experiment over corpus tasks."""
    if allow_llm and dry_run:
        raise ValueError("--allow-llm cannot be combined with --dry-run")
    if allow_llm and max_cost_usd is None:
        max_cost_usd = 25.0

    corpus_root = _BENCHMARK_ROOT / "corpus"
    manifest_path = corpus_root / "manifest.yaml"
    tasks = load_corpus_manifest(manifest_path)
    if task_ids:
        tasks = [t for t in tasks if t["id"] in task_ids]
        if not tasks:
            raise ValueError(f"No matching tasks in {task_ids}")

    output_dir.mkdir(parents=True, exist_ok=True)
    template_path = formalize_a1.DEFAULT_TEMPLATE.resolve()
    run_manifest: dict[str, Any] = {
        "experiment_version": EXPERIMENT_VERSION,
        "benchmark_name": "A0→A1 Prompt Formalization Benchmark",
        "milestone": 1,
        "started_at": datetime.now(timezone.utc).isoformat(),
        "git_sha": _git_sha(project_root),
        "formalize_script_version": formalize_a1.SCRIPT_VERSION,
        "template_sha256": _sha256(template_path),
        "allow_llm": allow_llm,
        "dry_run": dry_run,
        "max_cost_usd": max_cost_usd if allow_llm else None,
        "formalize_note": (
            "A1 produced by benchmark-local formalize_a1.py (formalize_script_v1), "
            "not native pdd checkup formalize --apply."
        ),
        "tasks": [],
    }

    total_cost = 0.0
    for entry in tasks:
        task_id = entry["id"]
        a0_path = (corpus_root / entry["a0"]).resolve()
        task_dir = output_dir / task_id
        task_dir.mkdir(parents=True, exist_ok=True)
        a1_path = task_dir / "A1.prompt"
        commands_log = task_dir / "commands.jsonl"

        a0_metrics = prompt_metrics.collect_prompt_metrics(a0_path)
        a0_metrics["prompt_sha256"] = _sha256(a0_path)
        a0_metrics["arm"] = "A0"

        formalize_manifest = formalize_a1.formalize(
            input_path=a0_path,
            output_path=a1_path,
            commands_log=commands_log,
            template_path=template_path,
            max_iters=formalize_a1.DEFAULT_MAX_ITERS,
            allow_llm=allow_llm,
            dry_run=dry_run,
            verbose=verbose,
            project_root=project_root,
        )

        for step in formalize_manifest.get("iterations", []):
            cost = step.get("cost_usd")
            if isinstance(cost, (int, float)):
                total_cost += float(cost)
                if allow_llm and max_cost_usd is not None and total_cost > max_cost_usd:
                    raise RuntimeError(
                        f"Exceeded --max-cost-usd {max_cost_usd} at task {task_id}"
                    )

        a1_metrics = prompt_metrics.collect_prompt_metrics(a1_path)
        a1_metrics["prompt_sha256"] = _sha256(a1_path)
        a1_metrics["arm"] = "A1"
        a1_metrics["formalize_script_version"] = formalize_a1.SCRIPT_VERSION
        a1_metrics["template_sha256"] = run_manifest["template_sha256"]
        a1_metrics["commands_log_present"] = commands_log.is_file()
        a1_metrics["formalize_iterations"] = len(
            [
                s
                for s in formalize_manifest.get("iterations", [])
                if s.get("stage", "").startswith("deterministic")
            ]
        )

        deltas = prompt_metrics.delta_metrics(a0_metrics, a1_metrics)
        task_result = {
            "task_id": task_id,
            "tier": entry.get("tier"),
            "description": entry.get("description"),
            "a0_path": str(a0_path),
            "a1_path": str(a1_path),
            "a0": a0_metrics,
            "a1": a1_metrics,
            "delta": deltas,
            "formalize_manifest": formalize_manifest,
        }
        (task_dir / "result.json").write_text(
            json.dumps(task_result, indent=2) + "\n",
            encoding="utf-8",
        )
        run_manifest["tasks"].append(task_result)

    run_manifest["finished_at"] = datetime.now(timezone.utc).isoformat()
    run_manifest["total_cost_usd"] = round(total_cost, 4) if allow_llm else None

    summary = _build_summary(run_manifest["tasks"])
    run_manifest["summary"] = summary

    (output_dir / "run_manifest.json").write_text(
        json.dumps(run_manifest, indent=2) + "\n",
        encoding="utf-8",
    )
    (output_dir / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n",
        encoding="utf-8",
    )
    _write_report_md(output_dir / "REPORT.md", summary, run_manifest)
    return run_manifest


def _build_summary(task_results: list[dict[str, Any]]) -> dict[str, Any]:
    """Aggregate per-task results into summary statistics."""
    n = len(task_results)
    gained_vocab = sum(1 for t in task_results if t["delta"].get("gained_vocabulary"))
    gained_rules = sum(1 for t in task_results if t["delta"].get("gained_contract_rules"))
    lint_improved = sum(
        1
        for t in task_results
        if (t["delta"].get("delta_lint_warnings") or 0) < 0
    )
    headlines: list[str] = []
    for task in task_results:
        tid = task["task_id"]
        dw = task["delta"].get("delta_lint_warnings")
        dr = task["delta"].get("delta_contract_rule_count")
        parts = [tid]
        if dw is not None:
            parts.append(f"Δlint={dw:+d}")
        if dr is not None:
            parts.append(f"Δrules={dr:+d}")
        headlines.append(": ".join(parts))

    return {
        "milestone": 1,
        "claim": (
            "M1 measures prompt checkability (vocabulary, contract rules, lint). "
            "It does not measure generated code correctness (M2) or regen stability (M3)."
        ),
        "task_count": n,
        "tasks_gained_vocabulary": gained_vocab,
        "tasks_gained_contract_rules": gained_rules,
        "tasks_lint_warnings_improved": lint_improved,
        "headline": "; ".join(headlines),
        "tasks": [
            {
                "task_id": t["task_id"],
                "a0_lint_warnings": t["a0"]["lint_warnings"],
                "a1_lint_warnings": t["a1"]["lint_warnings"],
                "a0_contract_rule_count": t["a0"]["contract_rule_count"],
                "a1_contract_rule_count": t["a1"]["contract_rule_count"],
                "a0_has_vocabulary": t["a0"]["has_vocabulary"],
                "a1_has_vocabulary": t["a1"]["has_vocabulary"],
                "a1_has_contract_rules": t["a1"]["has_contract_rules"],
                "regen_runs": None,
                "behavior_stability": None,
            }
            for t in task_results
        ],
    }


def _write_report_md(path: Path, summary: dict[str, Any], manifest: dict[str, Any]) -> None:
    """Write human-readable M1 report."""
    lines = [
        "# A0→A1 Prompt Formalization Benchmark — Milestone 1 Report",
        "",
        f"**Claim scope:** {summary['claim']}",
        "",
        f"**Tasks:** {summary['task_count']} · "
        f"gained vocabulary: {summary['tasks_gained_vocabulary']} · "
        f"gained contract rules: {summary['tasks_gained_contract_rules']} · "
        f"lint improved: {summary['tasks_lint_warnings_improved']}",
        "",
        "| Task | A0 lint | A1 lint | A0 rules | A1 rules | A1 vocab | A1 rules |",
        "|------|---------|---------|----------|----------|----------|----------|",
    ]
    for row in summary["tasks"]:
        lines.append(
            f"| {row['task_id']} | {row['a0_lint_warnings']} | {row['a1_lint_warnings']} | "
            f"{row['a0_contract_rule_count']} | {row['a1_contract_rule_count']} | "
            f"{'yes' if row['a1_has_vocabulary'] else 'no'} | "
            f"{'yes' if row['a1_has_contract_rules'] else 'no'} |"
        )
    lines.extend(
        [
            "",
            f"**Headline:** {summary['headline']}",
            "",
            f"Formalize script: `{manifest.get('formalize_script_version')}` · "
            f"allow_llm={manifest.get('allow_llm')} · dry_run={manifest.get('dry_run')}",
            "",
            "*M2: Formalized Prompt Generation Benchmark · "
            "M3: Formalized Prompt Regeneration Stability Benchmark*",
        ]
    )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main(argv: Optional[list[str]] = None) -> int:
    """CLI entrypoint."""
    parser = argparse.ArgumentParser(
        description="Milestone 1 A0→A1 formalization checkability experiment",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Experiment output directory (default: experiments/latest)",
    )
    parser.add_argument(
        "--tasks",
        type=str,
        default=None,
        help="Comma-separated task ids (default: all corpus tasks)",
    )
    parser.add_argument(
        "--allow-llm",
        action="store_true",
        help="Enable LLM formalization stages (requires API credentials)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Copy A0 to A1 without writeback (metrics only)",
    )
    parser.add_argument(
        "--max-cost-usd",
        type=float,
        default=None,
        help="Budget cap when --allow-llm (default 25)",
    )
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--project-root", type=Path, default=_REPO_ROOT)
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    task_ids = [t.strip() for t in args.tasks.split(",")] if args.tasks else None
    manifest = run_experiment(
        output_dir=args.output_dir.resolve(),
        task_ids=task_ids,
        allow_llm=args.allow_llm,
        dry_run=args.dry_run,
        max_cost_usd=args.max_cost_usd,
        project_root=args.project_root.resolve(),
        verbose=args.verbose,
    )

    if args.as_json:
        print(json.dumps(manifest["summary"], indent=2))
    else:
        print(f"Wrote experiment to {args.output_dir}")
        print(f"  {manifest['summary']['headline']}")
        print(f"  Report: {args.output_dir / 'REPORT.md'}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
