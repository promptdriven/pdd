#!/usr/bin/env python3
"""Milestone 2: compare A0 vs A1 generation economics."""
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
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
if str(_PIPELINE_DIR) not in sys.path:
    sys.path.insert(0, str(_PIPELINE_DIR))

import formalize_a1  # noqa: E402
from economics import business_value_block, economics_delta_from_arms, evaluation_modes_summary  # noqa: E402
from generation_loop import run_generation_loop  # noqa: E402

DEFAULT_OUTPUT = _BENCHMARK_ROOT / "experiments" / "m2_latest"


def _load_tasks(m2_only: bool = True) -> list[dict[str, Any]]:
    raw = yaml.safe_load((_BENCHMARK_ROOT / "corpus" / "manifest.yaml").read_text(encoding="utf-8"))
    tasks = raw.get("tasks") or []
    if m2_only:
        return [t for t in tasks if t.get("m2")]
    return tasks


def run_m2(
    *,
    output_dir: Path,
    task_ids: Optional[list[str]],
    m1_dir: Path,
    allow_llm: bool,
    harness_only: bool,
    max_rounds: int,
    max_cost_usd: Optional[float],
    skip_formalize: bool,
) -> dict[str, Any]:
    tasks = _load_tasks()
    if task_ids:
        tasks = [t for t in tasks if t["id"] in task_ids]
    output_dir.mkdir(parents=True, exist_ok=True)
    corpus = _BENCHMARK_ROOT / "corpus"

    manifest: dict[str, Any] = {
        "milestone": 2,
        "started_at": datetime.now(timezone.utc).isoformat(),
        "business_value": business_value_block(),
        "allow_llm": allow_llm,
        "harness_only": harness_only,
        "m1_dir": str(m1_dir),
        "tasks": [],
    }
    total_cost = 0.0

    for entry in tasks:
        task_id = entry["id"]
        module = entry.get("module", task_id)
        a0_path = (corpus / entry["a0"]).resolve()
        task_out = output_dir / task_id
        task_out.mkdir(parents=True, exist_ok=True)

        a1_path = m1_dir / task_id / "A1.prompt"
        if not a1_path.is_file() and not skip_formalize:
            a1_path = task_out / "A1.prompt"
            formalize_a1.formalize(
                input_path=a0_path,
                output_path=a1_path,
                commands_log=task_out / "formalize_commands.jsonl",
                template_path=formalize_a1.DEFAULT_TEMPLATE,
                max_iters=formalize_a1.DEFAULT_MAX_ITERS,
                allow_llm=allow_llm and not harness_only,
                dry_run=False,
                verbose=False,
                project_root=_REPO_ROOT,
            )
        elif not a1_path.is_file():
            raise FileNotFoundError(
                f"Missing A1 for {task_id}; run M1 first or omit --skip-formalize"
            )

        oracle_dir = None
        if entry.get("oracle_tests"):
            oracle_dir = (_BENCHMARK_ROOT / entry["oracle_tests"]).resolve()

        baseline_src = None
        if entry.get("baseline_src"):
            baseline_src = (_BENCHMARK_ROOT / entry["baseline_src"]).resolve()

        arms_result: dict[str, Any] = {}
        for arm, prompt in (("A0", a0_path), ("A1", a1_path)):
            arm_dir = task_out / arm
            log = arm_dir / "commands.jsonl"
            result = run_generation_loop(
                arm=arm,
                prompt_path=prompt,
                module=module,
                work_dir=arm_dir,
                oracle_test_dir=oracle_dir,
                commands_log=log,
                project_root=_REPO_ROOT,
                allow_llm=allow_llm,
                max_rounds=max_rounds,
                harness_only=harness_only,
                baseline_src=baseline_src if arm == "A1" else None,
            )
            arms_result[arm] = {
                "prompt": str(prompt),
                "economics": result.economics,
                "evaluation_modes": result.economics.get("evaluation_modes")
                or evaluation_modes_summary(result.economics),
                "code_path": str(result.code_path),
                "notes": result.notes,
            }
            total_cost += float(result.economics.get("cost_usd") or 0)
            if max_cost_usd and total_cost > max_cost_usd:
                raise RuntimeError(f"Exceeded --max-cost-usd {max_cost_usd}")

        delta = economics_delta_from_arms(
            arms_result["A0"]["economics"],
            arms_result["A1"]["economics"],
        )
        eval_a0 = arms_result["A0"]["evaluation_modes"]
        eval_a1 = arms_result["A1"]["evaluation_modes"]
        task_record = {
            "task_id": task_id,
            "module": module,
            "arms": arms_result,
            "delta": delta,
            "evaluation_summary": {
                "oracle_a0": eval_a0["oracle"]["pass_rate"],
                "oracle_a1": eval_a1["oracle"]["pass_rate"],
                "non_oracle_a0": eval_a0["non_oracle"]["pass_rate"],
                "non_oracle_a1": eval_a1["non_oracle"]["pass_rate"],
                "oracle_gap_a1_minus_a0": (
                    (eval_a1["oracle"]["pass_rate"] or 0)
                    - (eval_a0["oracle"]["pass_rate"] or 0)
                    if eval_a1["oracle"]["pass_rate"] is not None
                    and eval_a0["oracle"]["pass_rate"] is not None
                    else None
                ),
            },
        }
        (task_out / "result.json").write_text(json.dumps(task_record, indent=2) + "\n")
        manifest["tasks"].append(task_record)

    manifest["finished_at"] = datetime.now(timezone.utc).isoformat()
    manifest["total_cost_usd"] = round(total_cost, 4)
    (output_dir / "run_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="M2 generation economics benchmark")
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--m1-dir", type=Path, default=_BENCHMARK_ROOT / "experiments" / "latest")
    parser.add_argument("--tasks", type=str, default=None)
    parser.add_argument("--allow-llm", action="store_true")
    parser.add_argument("--harness-only", action="store_true", help="CI: use baseline/stub, no LLM")
    parser.add_argument("--max-rounds", type=int, default=2)
    parser.add_argument("--max-cost-usd", type=float, default=None)
    parser.add_argument("--skip-formalize", action="store_true")
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    task_ids = [t.strip() for t in args.tasks.split(",")] if args.tasks else None
    manifest = run_m2(
        output_dir=args.output_dir.resolve(),
        task_ids=task_ids,
        m1_dir=args.m1_dir.resolve(),
        allow_llm=args.allow_llm,
        harness_only=args.harness_only,
        max_rounds=args.max_rounds,
        max_cost_usd=args.max_cost_usd,
        skip_formalize=args.skip_formalize,
    )
    if args.as_json:
        print(json.dumps(manifest, indent=2))
    else:
        print(f"M2 complete → {args.output_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
