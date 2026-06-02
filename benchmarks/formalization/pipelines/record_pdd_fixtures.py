#!/usr/bin/env python3
"""Record ``pdd generate`` + ``pdd test`` outputs into corpus fixture dirs (M2 live path)."""
from __future__ import annotations

import argparse
import sys
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

import cloud_formalize  # noqa: E402
import pdd_fixture_store  # noqa: E402
from generation_loop import run_generation_loop  # noqa: E402


def _load_tasks(task_ids: Optional[list[str]]) -> list[dict[str, Any]]:
    raw = yaml.safe_load(
        (_BENCHMARK_ROOT / "corpus" / "manifest.yaml").read_text(encoding="utf-8")
    )
    tasks = [t for t in (raw.get("tasks") or []) if t.get("m2")]
    if task_ids:
        tasks = [t for t in tasks if t["id"] in task_ids]
    return tasks


def record(
    *,
    task_ids: Optional[list[str]],
    m1_dir: Path,
    max_rounds: int,
    max_cost_usd: Optional[float],
    dry_run: bool,
) -> dict[str, Any]:
    """Run live M2 generate/test for A0 and A1; save under tier_gold pdd_generated/."""
    corpus = _BENCHMARK_ROOT / "corpus"
    summary: dict[str, Any] = {"tasks": [], "dry_run": dry_run}

    for entry in _load_tasks(task_ids):
        task_id = entry["id"]
        module = entry.get("module", task_id)
        a0_path = (corpus / entry["a0"]).resolve()
        fixtures_root = _BENCHMARK_ROOT / entry.get(
            "pdd_fixtures",
            f"corpus/tier_gold/{task_id}/pdd_generated",
        )
        if not fixtures_root.is_absolute():
            fixtures_root = (_BENCHMARK_ROOT / fixtures_root).resolve()

        a1_path = m1_dir / task_id / "A1.prompt"
        if not a1_path.is_file():
            tmp = _BENCHMARK_ROOT / "experiments" / "_record_tmp" / task_id / "A1.prompt"
            tmp.parent.mkdir(parents=True, exist_ok=True)
            stories_dir = None
            if entry.get("stories_dir"):
                stories_dir = (corpus / entry["stories_dir"]).resolve()
            cloud_formalize.formalize(
                input_path=a0_path,
                output_path=tmp,
                commands_log=None,
                dry_run=False,
                verbose=False,
                project_root=_REPO_ROOT,
                stories_dir=stories_dir,
            )
            pdd_fixture_store.save_recorded_a1(
                fixtures_root=fixtures_root,
                arm="A1",
                prompt_path=tmp,
            )
            a1_path = tmp
        else:
            pdd_fixture_store.save_recorded_a1(
                fixtures_root=fixtures_root,
                arm="A1",
                prompt_path=a1_path,
            )

        task_summary: dict[str, Any] = {"task_id": task_id, "fixtures_root": str(fixtures_root)}
        total_cost = 0.0

        for arm, prompt in (("A0", a0_path), ("A1", a1_path)):
            arm_dir = fixtures_root.parent / "_record_work" / task_id / arm
            if dry_run:
                task_summary[arm] = {"prompt": str(prompt), "skipped": True}
                continue

            result = run_generation_loop(
                arm=arm,
                prompt_path=prompt,
                module=module,
                work_dir=arm_dir,
                oracle_test_dir=None,
                commands_log=arm_dir / "commands.jsonl",
                project_root=_REPO_ROOT,
                allow_llm=True,
                max_rounds=max_rounds,
                harness_only=False,
                baseline_src=None,
                pdd_fixtures_root=None,
            )
            total_cost += float(result.economics.get("cost_usd") or 0)
            if max_cost_usd and total_cost > max_cost_usd:
                raise RuntimeError(f"Exceeded --max-cost-usd {max_cost_usd} at {task_id}")

            pdd_fixture_store.save_arm_fixtures(
                fixtures_root=fixtures_root,
                arm=arm,
                module=module,
                work_dir=arm_dir,
                prompt_path=prompt,
                provenance="pdd_cli_record",
                extra={
                    "generation_rounds": result.economics.get("generation_rounds"),
                    "fix_rounds": result.economics.get("fix_rounds"),
                    "generated_test_pass_rate": result.economics.get("generated_test_pass_rate"),
                },
            )
            task_summary[arm] = {
                "prompt": str(prompt),
                "economics": result.economics,
                "code_path": str(result.code_path),
                "test_path": str(result.generated_test_path),
            }

        summary["tasks"].append(task_summary)

    return summary


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Record pdd generate/test fixtures for CI replay (requires API keys)",
    )
    parser.add_argument("--tasks", type=str, default=None, help="Comma-separated task ids")
    parser.add_argument(
        "--m1-dir",
        type=Path,
        default=_BENCHMARK_ROOT / "experiments" / "latest",
        help="M1 output with A1.prompt files",
    )
    parser.add_argument("--max-rounds", type=int, default=2)
    parser.add_argument("--max-cost-usd", type=float, default=50.0)
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="List tasks/prompts only; do not call pdd generate/test",
    )
    args = parser.parse_args(argv)
    task_ids = [t.strip() for t in args.tasks.split(",")] if args.tasks else None
    summary = record(
        task_ids=task_ids,
        m1_dir=args.m1_dir.resolve(),
        max_rounds=args.max_rounds,
        max_cost_usd=args.max_cost_usd,
        dry_run=args.dry_run,
    )
    if args.dry_run:
        print(f"Would record {len(summary['tasks'])} task(s)")
    else:
        print(f"Recorded fixtures for {len(summary['tasks'])} task(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
