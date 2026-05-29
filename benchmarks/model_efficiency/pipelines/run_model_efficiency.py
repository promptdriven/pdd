#!/usr/bin/env python3
"""Model Efficiency Benchmark (M4): smart vs budget model × A0 vs A1.

A0 prompts are handcrafted in the formalization corpus. A1 prompts, generated
code, and generated tests all come from PDD CLI commands (``pdd generate``,
``pdd test``, optional ``pdd fix``) — never from hand-curated baselines.

Core comparison: **budget model + A1** vs **smart model + A0**.
"""
from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional

import yaml

_PIPELINE_DIR = Path(__file__).resolve().parent
_BENCHMARK_ROOT = _PIPELINE_DIR.parent
_REPO_ROOT = _BENCHMARK_ROOT.parents[1]
_FORMALIZATION_ROOT = _BENCHMARK_ROOT.parent / "formalization"
_FORMALIZATION_PIPELINES = _FORMALIZATION_ROOT / "pipelines"

for path in (_REPO_ROOT, _FORMALIZATION_PIPELINES, _PIPELINE_DIR):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

import cloud_formalize  # noqa: E402
from economics import m4_business_value_block  # noqa: E402
from generation_loop import run_generation_loop  # noqa: E402
from metrics import aggregate_cells, cell_key, core_comparison, m4_headline  # noqa: E402

DEFAULT_OUTPUT = _BENCHMARK_ROOT / "experiments" / "latest"


def _tier_runtime(
    tier_cfg: dict[str, Any],
    *,
    cloud_only_default: bool = False,
) -> dict[str, Any]:
    """Normalize manifest tier config for generation_loop / cloud_formalize."""
    routing = str(tier_cfg.get("routing", "cloud")).lower()
    use_cloud = routing != "local"
    cloud_only = bool(tier_cfg.get("cloud_only", use_cloud and cloud_only_default))
    return {
        "label": tier_cfg.get("label", ""),
        "routing": routing,
        "strength": float(tier_cfg.get("strength", 0.5)),
        "expected_model": tier_cfg.get("expected_model") or tier_cfg.get("model"),
        "force_local": routing == "local",
        "cloud_only": cloud_only,
    }


def _smart_tier(tiers: dict[str, Any], *, cloud_only_default: bool = False) -> dict[str, Any]:
    return _tier_runtime(tiers["smart"], cloud_only_default=cloud_only_default)


def _load_manifest() -> dict[str, Any]:
    return yaml.safe_load((_BENCHMARK_ROOT / "manifest.yaml").read_text(encoding="utf-8"))


def _load_formalization_tasks(task_ids: list[str]) -> list[dict[str, Any]]:
    corpus_path = (_BENCHMARK_ROOT / _load_manifest()["formalization_corpus"]).resolve()
    raw = yaml.safe_load(corpus_path.read_text(encoding="utf-8"))
    by_id = {t["id"]: t for t in (raw.get("tasks") or [])}
    missing = [tid for tid in task_ids if tid not in by_id]
    if missing:
        raise KeyError(f"Unknown formalization tasks: {missing}")
    return [by_id[tid] for tid in task_ids]


def _ensure_a1(
    *,
    entry: dict[str, Any],
    task_out: Path,
    corpus: Path,
    allow_llm: bool,
    replay_a1: bool,
    project_root: Path,
    formalize_tier: dict[str, Any],
) -> Path:
    """Produce or replay A1 via PDD (never hand-written)."""
    a1_path = task_out / "A1.prompt"
    if a1_path.is_file():
        return a1_path

    a0_path = (corpus / entry["a0"]).resolve()
    stories_dir = (corpus / entry["stories_dir"]).resolve() if entry.get("stories_dir") else None
    log = task_out / "formalize_commands.jsonl"

    if replay_a1 or not allow_llm:
        fixtures = entry.get("pdd_fixtures")
        if not fixtures:
            raise FileNotFoundError(
                f"No pdd_fixtures for {entry['id']}; use --allow-llm or add fixtures"
            )
        recorded = (_FORMALIZATION_ROOT / fixtures / "A1.prompt").resolve()
        cloud_formalize.replay_a1(recorded_a1=recorded, output_path=a1_path)
        append_note = task_out / "a1_provenance.json"
        append_note.write_text(
            json.dumps({"source": "replay", "recorded_a1": str(recorded)}, indent=2) + "\n",
            encoding="utf-8",
        )
        return a1_path

    manifest = cloud_formalize.formalize(
        input_path=a0_path,
        output_path=a1_path,
        commands_log=log,
        dry_run=False,
        verbose=False,
        project_root=project_root,
        stories_dir=stories_dir,
        pdd_strength=formalize_tier["strength"],
        pdd_model=formalize_tier["expected_model"] if formalize_tier["force_local"] else None,
        pdd_force_local=formalize_tier["force_local"],
        pdd_cloud_only=formalize_tier["cloud_only"],
    )
    (task_out / "a1_provenance.json").write_text(json.dumps(manifest, indent=2) + "\n")
    if not manifest.get("summary", {}).get("cloud_generate"):
        raise RuntimeError(f"A1 formalization failed for {entry['id']}")
    return a1_path


def run_m4(
    *,
    output_dir: Path,
    task_ids: list[str],
    runs_per_cell: int,
    max_rounds: int,
    allow_llm: bool,
    harness_only: bool,
    replay_a1: bool,
    max_cost_usd: Optional[float],
) -> dict[str, Any]:
    manifest_yaml = _load_manifest()
    tiers: dict[str, Any] = manifest_yaml["model_tiers"]
    exp_cfg = manifest_yaml.get("experiment") or {}
    cloud_only_default = bool(exp_cfg.get("cloud_only", True))
    smart_tier = _smart_tier(tiers, cloud_only_default=cloud_only_default)
    tasks = _load_formalization_tasks(task_ids)
    corpus = _FORMALIZATION_ROOT / "corpus"
    output_dir.mkdir(parents=True, exist_ok=True)

    run_manifest: dict[str, Any] = {
        "milestone": 4,
        "benchmark_name": manifest_yaml["benchmark_name"],
        "started_at": datetime.now(timezone.utc).isoformat(),
        "business_value": m4_business_value_block(),
        "model_tiers": tiers,
        "cloud_only": cloud_only_default,
        "formalize_tier": smart_tier,
        "allow_llm": allow_llm,
        "harness_only": harness_only,
        "replay_a1": replay_a1,
        "runs_per_cell": runs_per_cell,
        "tasks": [],
        "cells": [],
    }
    total_cost = 0.0
    all_cells: list[dict[str, Any]] = []

    for entry in tasks:
        task_id = entry["id"]
        module = entry.get("module", task_id)
        task_out = output_dir / task_id
        task_out.mkdir(parents=True, exist_ok=True)

        a0_path = (corpus / entry["a0"]).resolve()
        a1_path = _ensure_a1(
            entry=entry,
            task_out=task_out,
            corpus=corpus,
            allow_llm=allow_llm and not harness_only,
            replay_a1=replay_a1 or harness_only,
            project_root=_REPO_ROOT,
            formalize_tier=smart_tier,
        )

        oracle_dir = (
            (_FORMALIZATION_ROOT / entry["oracle_tests"]).resolve()
            if entry.get("oracle_tests")
            else None
        )
        pdd_fixtures_root = (
            (_FORMALIZATION_ROOT / entry["pdd_fixtures"]).resolve()
            if entry.get("pdd_fixtures")
            else None
        )

        task_cells: list[dict[str, Any]] = []
        for run_index in range(runs_per_cell):
            for tier_name, tier_cfg in tiers.items():
                runtime = _tier_runtime(tier_cfg, cloud_only_default=cloud_only_default)
                for arm, prompt in (("A0", a0_path), ("A1", a1_path)):
                    cell_dir = task_out / f"run_{run_index}" / f"{tier_name}_{arm}"
                    log = cell_dir / "commands.jsonl"
                    result = run_generation_loop(
                        arm=arm,
                        prompt_path=prompt,
                        module=module,
                        work_dir=cell_dir,
                        oracle_test_dir=oracle_dir,
                        commands_log=log,
                        project_root=_REPO_ROOT,
                        allow_llm=allow_llm,
                        max_rounds=max_rounds,
                        harness_only=harness_only,
                        baseline_src=None,
                        pdd_fixtures_root=pdd_fixtures_root,
                        pdd_strength=runtime["strength"] if not harness_only else None,
                        pdd_model=runtime["expected_model"]
                        if runtime["force_local"] and not harness_only
                        else None,
                        pdd_force_local=runtime["force_local"] if not harness_only else False,
                        pdd_cloud_only=runtime["cloud_only"] if not harness_only else False,
                    )
                    cell_record = {
                        "task_id": task_id,
                        "tier": tier_name,
                        "tier_label": runtime["label"],
                        "tier_routing": runtime["routing"],
                        "expected_model": runtime["expected_model"],
                        "arm": arm,
                        "run_index": run_index,
                        "cell_key": cell_key(tier=tier_name, arm=arm, run_index=run_index),
                        "pdd_strength": runtime["strength"],
                        "pdd_routing": runtime["routing"],
                        "pdd_cloud_only": runtime["cloud_only"],
                        "prompt": str(prompt),
                        "economics": result.economics,
                        "code_path": str(result.code_path),
                        "test_path": str(result.generated_test_path),
                        "notes": result.notes,
                    }
                    task_cells.append(cell_record)
                    all_cells.append(cell_record)
                    total_cost += float(result.economics.get("cost_usd") or 0)
                    if max_cost_usd and total_cost > max_cost_usd:
                        raise RuntimeError(f"Exceeded --max-cost-usd {max_cost_usd}")

        task_summary = {
            "task_id": task_id,
            "cells": task_cells,
            "by_tier_arm": {
                f"{tier}_{arm}": aggregate_cells(
                    [c for c in task_cells if c["tier"] == tier and c["arm"] == arm]
                )
                for tier in tiers
                for arm in ("A0", "A1")
            },
        }
        (task_out / "result.json").write_text(json.dumps(task_summary, indent=2) + "\n")
        run_manifest["tasks"].append(task_summary)

    run_manifest["cells"] = all_cells
    run_manifest["aggregate"] = aggregate_cells(all_cells)
    run_manifest["core_comparison"] = core_comparison(all_cells)
    run_manifest["finished_at"] = datetime.now(timezone.utc).isoformat()
    run_manifest["total_cost_usd"] = round(total_cost, 6)
    summary = {
        "headline": m4_headline(all_cells),
        "core_comparison": run_manifest["core_comparison"],
        "aggregate": run_manifest["aggregate"],
        "cell_count": len(all_cells),
        "total_cost_usd": run_manifest["total_cost_usd"],
    }
    run_manifest["summary"] = summary
    (output_dir / "run_manifest.json").write_text(json.dumps(run_manifest, indent=2) + "\n")
    (output_dir / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return run_manifest


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="M4 model-efficiency benchmark")
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--tasks", type=str, default=None, help="Comma-separated task ids")
    parser.add_argument("--runs", type=int, default=None, help="Override runs_per_cell")
    parser.add_argument("--max-rounds", type=int, default=None)
    parser.add_argument("--allow-llm", action="store_true", help="Live PDD cloud generate/test")
    parser.add_argument(
        "--harness-only",
        action="store_true",
        help="CI: replay pdd_fixtures (no LLM); A1 via --replay-a1",
    )
    parser.add_argument(
        "--replay-a1",
        action="store_true",
        help="Replay recorded A1.prompt from tier_gold pdd_generated (no formalize LLM)",
    )
    parser.add_argument("--max-cost-usd", type=float, default=None)
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    m4_manifest = _load_manifest()
    exp = m4_manifest["experiment"]
    task_ids = [t.strip() for t in args.tasks.split(",")] if args.tasks else list(exp["tasks"])
    runs = args.runs if args.runs is not None else int(exp["runs_per_cell"])
    max_rounds = args.max_rounds if args.max_rounds is not None else int(exp["max_rounds"])

    if args.harness_only:
        args.replay_a1 = True
    elif not args.allow_llm:
        parser.error("Live experiment requires --allow-llm; CI uses --harness-only --replay-a1")

    manifest = run_m4(
        output_dir=args.output_dir.resolve(),
        task_ids=task_ids,
        runs_per_cell=runs,
        max_rounds=max_rounds,
        allow_llm=args.allow_llm,
        harness_only=args.harness_only,
        replay_a1=args.replay_a1,
        max_cost_usd=args.max_cost_usd,
    )
    if args.as_json:
        print(json.dumps(manifest, indent=2))
    else:
        print(f"M4 complete → {args.output_dir}")
        print(f"  {manifest['summary']['headline']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
