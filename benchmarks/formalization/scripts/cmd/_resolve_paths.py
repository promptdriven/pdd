#!/usr/bin/env python3
"""Print shell exports for benchmark paths (one pdd command scripts)."""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import yaml

_BENCHMARK_ROOT = Path(__file__).resolve().parents[2]
_CORPUS = _BENCHMARK_ROOT / "corpus"
_REPO_ROOT = _BENCHMARK_ROOT.parents[1]


def _load_task(task_id: str) -> dict:
    raw = yaml.safe_load((_CORPUS / "manifest.yaml").read_text(encoding="utf-8"))
    for entry in raw.get("tasks") or []:
        if entry["id"] == task_id:
            return entry
    raise SystemExit(f"Unknown task: {task_id}")


def m2_paths(*, task_id: str, arm: str, m1_dir: Path, m2_dir: Path) -> dict[str, str]:
    entry = _load_task(task_id)
    module = entry.get("module", task_id)
    a0 = (_CORPUS / entry["a0"]).resolve()
    if arm == "A0":
        prompt = a0
    elif arm == "A1":
        prompt = (m1_dir / task_id / "A1.prompt").resolve()
        if not prompt.is_file():
            raise SystemExit(f"Missing A1: {prompt}")
    else:
        raise SystemExit(f"ARM must be A0 or A1 (got {arm})")

    work = m2_dir / task_id / arm
    code = work / "generated" / "src" / f"{module}.py"
    test = work / "generated" / "tests" / f"test_{module}.py"
    oracle = ""
    if entry.get("oracle_tests"):
        oracle = str((_BENCHMARK_ROOT / entry["oracle_tests"]).resolve())
    stories = ""
    if entry.get("stories_dir"):
        stories = str((_CORPUS / entry["stories_dir"]).resolve())

    language = entry.get("language", "python")
    return {
        "TASK": task_id,
        "ARM": arm,
        "MODULE": module,
        "LANGUAGE": language,
        "PROMPT": str(prompt),
        "CODE": str(code),
        "TEST": str(test),
        "WORK_DIR": str(work),
        "SRC_DIR": str(code.parent),
        "TEST_DIR": str(test.parent),
        "COMMANDS_LOG": str(work / "commands.jsonl"),
        "ORACLE_DIR": oracle,
        "STORIES_DIR": stories,
        "REPO_ROOT": str(_REPO_ROOT),
    }


def m1_paths(*, task_id: str, m1_dir: Path) -> dict[str, str]:
    entry = _load_task(task_id)
    a0 = (_CORPUS / entry["a0"]).resolve()
    a1 = (m1_dir / task_id / "A1.prompt").resolve()
    stories = ""
    if entry.get("stories_dir"):
        stories = str((_CORPUS / entry["stories_dir"]).resolve())
    return {
        "TASK": task_id,
        "A0_PROMPT": str(a0),
        "A1_PROMPT": str(a1),
        "STORIES_DIR": stories,
        "COMMANDS_LOG": str(m1_dir / task_id / "commands.jsonl"),
        "REPO_ROOT": str(_REPO_ROOT),
    }


def m3_paths(*, task_id: str, arm: str, m1_dir: Path, m2_dir: Path, m3_dir: Path) -> dict[str, str]:
    m2 = m2_paths(task_id=task_id, arm=arm, m1_dir=m1_dir, m2_dir=m2_dir)
    evidence = m3_dir / task_id / f"evidence_{arm}.json"
    return {
        **m2,
        "M3_DIR": str(m3_dir),
        "EVIDENCE": str(evidence),
        "DEVUNIT": m2["MODULE"],
    }


def _shell_export(data: dict[str, str]) -> None:
    for key, value in data.items():
        escaped = value.replace("'", "'\\''")
        print(f"export {key}='{escaped}'")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=["m1", "m2", "m3"])
    parser.add_argument("--task", required=True)
    parser.add_argument("--arm", default="A0")
    parser.add_argument("--m1-dir", type=Path, default=_BENCHMARK_ROOT / "experiments" / "latest")
    parser.add_argument("--m2-dir", type=Path, default=_BENCHMARK_ROOT / "experiments" / "m2_latest")
    parser.add_argument("--m3-dir", type=Path, default=_BENCHMARK_ROOT / "experiments" / "m3_latest")
    args = parser.parse_args()

    if args.mode == "m1":
        data = m1_paths(task_id=args.task, m1_dir=args.m1_dir.resolve())
    elif args.mode == "m2":
        data = m2_paths(
            task_id=args.task,
            arm=args.arm,
            m1_dir=args.m1_dir.resolve(),
            m2_dir=args.m2_dir.resolve(),
        )
    else:
        data = m3_paths(
            task_id=args.task,
            arm=args.arm,
            m1_dir=args.m1_dir.resolve(),
            m2_dir=args.m2_dir.resolve(),
            m3_dir=args.m3_dir.resolve(),
        )
    _shell_export(data)


if __name__ == "__main__":
    main()
