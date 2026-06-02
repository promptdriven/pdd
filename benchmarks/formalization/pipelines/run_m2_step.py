#!/usr/bin/env python3
"""Run one M2 step for a single task + arm (generate, test, fix, score, replay, all)."""
from __future__ import annotations

import argparse
import json
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

from command_log import append_jsonl, run_logged_command  # noqa: E402
from generation_loop import run_generation_loop  # noqa: E402
from pytest_metrics import run_pytest  # noqa: E402
from run_generation_benchmark import _fixtures_root  # noqa: E402


def _load_task(task_id: str) -> dict[str, Any]:
    raw = yaml.safe_load((_BENCHMARK_ROOT / "corpus" / "manifest.yaml").read_text(encoding="utf-8"))
    for entry in raw.get("tasks") or []:
        if entry["id"] == task_id:
            return entry
    raise SystemExit(f"Unknown task: {task_id}")


def _arm_paths(
    *,
    entry: dict[str, Any],
    task_id: str,
    arm: str,
    m1_dir: Path,
    m2_dir: Path,
) -> tuple[Path, Path, str, Path]:
    corpus = _BENCHMARK_ROOT / "corpus"
    module = entry.get("module", task_id)
    a0_path = (corpus / entry["a0"]).resolve()
    if arm == "A0":
        prompt = a0_path
    elif arm == "A1":
        prompt = (m1_dir / task_id / "A1.prompt").resolve()
        if not prompt.is_file():
            raise SystemExit(f"Missing A1 prompt: {prompt} (run M1 first)")
    else:
        raise SystemExit(f"arm must be A0 or A1 (got {arm})")

    work_dir = m2_dir / task_id / arm
    code_path = work_dir / "generated" / "src" / f"{module}.py"
    return prompt, work_dir, module, code_path


def _find_pdd() -> str:
    import shutil

    found = shutil.which("pdd")
    if not found:
        raise SystemExit("pdd CLI not found on PATH")
    return found


def _oracle_dir(entry: dict[str, Any]) -> Optional[Path]:
    if not entry.get("oracle_tests"):
        return None
    path = (_BENCHMARK_ROOT / entry["oracle_tests"]).resolve()
    return path if path.is_dir() else None


def step_generate(
    *,
    prompt: Path,
    code_path: Path,
    commands_log: Optional[Path],
) -> dict[str, Any]:
    code_path.parent.mkdir(parents=True, exist_ok=True)
    pdd = _find_pdd()
    cmd = [
        pdd,
        "--force",
        "generate",
        str(prompt),
        "--output",
        str(code_path),
        "--language",
        "python",
        "--evidence",
    ]
    entry = run_logged_command(cmd, cwd=_REPO_ROOT, log_path=commands_log)
    entry["stage"] = "generate"
    return entry


def step_test(
    *,
    prompt: Path,
    code_path: Path,
    module: str,
    work_dir: Path,
    commands_log: Optional[Path],
) -> dict[str, Any]:
    test_path = work_dir / "generated" / "tests" / f"test_{module}.py"
    test_path.parent.mkdir(parents=True, exist_ok=True)
    if not code_path.is_file():
        raise SystemExit(f"Missing code (run generate first): {code_path}")
    pdd = _find_pdd()
    cmd = [
        pdd,
        "--force",
        "test",
        str(prompt),
        str(code_path),
        "--output",
        str(test_path),
        "--language",
        "python",
        "--evidence",
    ]
    entry = run_logged_command(cmd, cwd=_REPO_ROOT, log_path=commands_log)
    entry["stage"] = "test"
    entry["test_path"] = str(test_path)
    return entry


def step_fix(
    *,
    prompt: Path,
    code_path: Path,
    module: str,
    work_dir: Path,
    commands_log: Optional[Path],
) -> dict[str, Any]:
    test_path = work_dir / "generated" / "tests" / f"test_{module}.py"
    if not test_path.is_file():
        raise SystemExit(f"Missing tests (run test first): {test_path}")
    pdd = _find_pdd()
    cmd = [pdd, "fix", str(prompt), str(code_path), str(test_path)]
    entry = run_logged_command(cmd, cwd=_REPO_ROOT, log_path=commands_log)
    entry["stage"] = "fix"
    return entry


def step_score(
    *,
    module: str,
    work_dir: Path,
    oracle_test_dir: Optional[Path],
    commands_log: Optional[Path],
) -> dict[str, Any]:
    src_dir = work_dir / "generated" / "src"
    test_path = work_dir / "generated" / "tests" / f"test_{module}.py"
    result: dict[str, Any] = {"stage": "score"}

    if test_path.is_file():
        non_oracle = run_pytest([test_path], pythonpath=[src_dir], cwd=_REPO_ROOT)
        result["non_oracle"] = non_oracle
    else:
        result["non_oracle"] = {"test_pass_rate": None, "note": "no generated test file"}

    if oracle_test_dir and (src_dir / f"{module}.py").is_file():
        oracle = run_pytest(
            list(oracle_test_dir.glob("test_*.py")),
            pythonpath=[src_dir],
            cwd=_REPO_ROOT,
        )
        result["oracle"] = oracle
    else:
        result["oracle"] = {"test_pass_rate": None, "note": "no oracle dir or code"}

    append_jsonl(commands_log, result)
    return result


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Single M2 step for one task + arm")
    parser.add_argument("--task", required=True, help="Task id, e.g. email_validator")
    parser.add_argument("--arm", required=True, choices=["A0", "A1"])
    parser.add_argument(
        "--step",
        required=True,
        choices=["generate", "test", "fix", "score", "replay", "all"],
        help="One micro-step, or 'all' for full arm loop",
    )
    parser.add_argument("--m1-dir", type=Path, default=_BENCHMARK_ROOT / "experiments" / "latest")
    parser.add_argument("--m2-dir", type=Path, default=_BENCHMARK_ROOT / "experiments" / "m2_latest")
    parser.add_argument("--allow-llm", action="store_true")
    parser.add_argument("--replay-fixtures", action="store_true")
    parser.add_argument("--max-rounds", type=int, default=3)
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    entry = _load_task(args.task)
    prompt, work_dir, module, code_path = _arm_paths(
        entry=entry,
        task_id=args.task,
        arm=args.arm,
        m1_dir=args.m1_dir.resolve(),
        m2_dir=args.m2_dir.resolve(),
    )
    commands_log = work_dir / "commands.jsonl"
    oracle_dir = _oracle_dir(entry)

    if args.step == "all":
        if args.replay_fixtures:
            harness_only = True
            allow_llm = False
        elif args.allow_llm:
            harness_only = False
            allow_llm = True
        else:
            parser.error("--step all requires --allow-llm or --replay-fixtures")
        baseline = None
        if entry.get("baseline_src"):
            baseline = (_BENCHMARK_ROOT / entry["baseline_src"]).resolve()
        fixtures = _fixtures_root(entry) if args.replay_fixtures else None
        result = run_generation_loop(
            arm=args.arm,
            prompt_path=prompt,
            module=module,
            work_dir=work_dir,
            oracle_test_dir=oracle_dir,
            commands_log=commands_log,
            project_root=_REPO_ROOT,
            allow_llm=allow_llm,
            max_rounds=args.max_rounds,
            harness_only=harness_only,
            baseline_src=baseline if args.arm == "A1" else None,
            pdd_fixtures_root=fixtures,
        )
        payload = {
            "task": args.task,
            "arm": args.arm,
            "step": "all",
            "economics": result.economics,
            "notes": result.notes,
        }
    elif args.step == "replay":
        if not args.replay_fixtures:
            parser.error("--step replay requires --replay-fixtures")
        baseline = None
        if entry.get("baseline_src"):
            baseline = (_BENCHMARK_ROOT / entry["baseline_src"]).resolve()
        fixtures = _fixtures_root(entry)
        result = run_generation_loop(
            arm=args.arm,
            prompt_path=prompt,
            module=module,
            work_dir=work_dir,
            oracle_test_dir=oracle_dir,
            commands_log=commands_log,
            project_root=_REPO_ROOT,
            allow_llm=False,
            max_rounds=0,
            harness_only=True,
            baseline_src=baseline if args.arm == "A1" else None,
            pdd_fixtures_root=fixtures,
        )
        payload = {"task": args.task, "arm": args.arm, "step": "replay", "economics": result.economics}
    else:
        if args.step in ("generate", "test", "fix") and not args.allow_llm:
            parser.error(f"--step {args.step} requires --allow-llm")
        if args.step == "generate":
            payload = step_generate(prompt=prompt, code_path=code_path, commands_log=commands_log)
        elif args.step == "test":
            payload = step_test(
                prompt=prompt,
                code_path=code_path,
                module=module,
                work_dir=work_dir,
                commands_log=commands_log,
            )
        elif args.step == "fix":
            payload = step_fix(
                prompt=prompt,
                code_path=code_path,
                module=module,
                work_dir=work_dir,
                commands_log=commands_log,
            )
        else:
            payload = step_score(
                module=module,
                work_dir=work_dir,
                oracle_test_dir=oracle_dir,
                commands_log=commands_log,
            )
        payload = {"task": args.task, "arm": args.arm, **payload}

    if args.as_json:
        print(json.dumps(payload, indent=2))
    else:
        stage = payload.get("step", args.step)
        print(f"OK {args.task}/{args.arm} step={stage}")
        if "economics" in payload:
            eco = payload["economics"]
            print(f"  oracle: {eco.get('oracle_test_pass_rate')}  cost: ${eco.get('cost_usd')}")
        if payload.get("exit_code") is not None:
            print(f"  exit_code: {payload['exit_code']}")
        if "non_oracle" in payload:
            print(f"  non_oracle pass: {payload['non_oracle'].get('test_pass_rate')}")
        if "oracle" in payload and isinstance(payload["oracle"], dict):
            print(f"  oracle pass: {payload['oracle'].get('test_pass_rate')}")
        print(f"  log: {commands_log}")

    exit_code = payload.get("exit_code")
    if exit_code is not None and exit_code != 0:
        return int(exit_code)
    if payload.get("economics", {}).get("oracle_test_pass_rate") == 0.0:
        return 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
