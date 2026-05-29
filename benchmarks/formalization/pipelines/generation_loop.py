"""M2 generation loop: generate → test → pytest (optional fix rounds)."""
from __future__ import annotations

import shutil
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional

from command_log import append_jsonl, run_logged_command
from economics import economics_placeholders, evaluation_modes_summary
from pdd_fixture_store import arm_has_fixtures, copy_arm_fixtures
from pytest_metrics import run_pytest


@dataclass
class GenerationLoopResult:
    """Outcome of one arm generation run."""

    arm: str
    prompt_path: Path
    work_dir: Path
    code_path: Path
    generated_test_path: Path
    economics: dict[str, Any] = field(default_factory=dict)
    rounds: list[dict[str, Any]] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)


def _find_pdd() -> str:
    import shutil as sh

    found = sh.which("pdd")
    if found:
        return found
    raise RuntimeError("pdd CLI not found on PATH; run pip install -e .")


def run_generation_loop(
    *,
    arm: str,
    prompt_path: Path,
    module: str,
    work_dir: Path,
    oracle_test_dir: Optional[Path],
    commands_log: Optional[Path],
    project_root: Path,
    allow_llm: bool,
    max_rounds: int,
    harness_only: bool,
    baseline_src: Optional[Path],
    pdd_fixtures_root: Optional[Path] = None,
) -> GenerationLoopResult:
    """Run generate/test/pytest for one prompt arm."""
    work_dir.mkdir(parents=True, exist_ok=True)
    src_dir = work_dir / "generated" / "src"
    tests_dir = work_dir / "generated" / "tests"
    src_dir.mkdir(parents=True, exist_ok=True)
    tests_dir.mkdir(parents=True, exist_ok=True)

    code_path = src_dir / f"{module}.py"
    test_path = tests_dir / f"test_{module}.py"
    pdd = _find_pdd()

    economics = economics_placeholders(
        milestone=2,
        reason="Populated by generation_loop",
    )
    economics["generation_rounds"] = 0
    economics["fix_rounds"] = 0
    total_cost = 0.0
    total_wall = 0.0
    rounds: list[dict[str, Any]] = []

    loop_notes: list[str] = []
    if harness_only:
        if (
            pdd_fixtures_root
            and arm_has_fixtures(pdd_fixtures_root, arm, module)
        ):
            replay = copy_arm_fixtures(
                fixtures_root=pdd_fixtures_root,
                arm=arm,
                module=module,
                work_dir=work_dir,
            )
            rounds.append(replay)
            economics["generation_rounds"] = 0
            loop_notes.append(
                f"harness_only: replayed pdd_generated fixtures from {pdd_fixtures_root}"
            )
        elif baseline_src and (baseline_src / f"{module}.py").is_file():
            shutil.copy2(baseline_src / f"{module}.py", code_path)
            economics["generation_rounds"] = 0
            loop_notes.append("harness_only: used baseline reference implementation")
            rounds.append({"stage": "harness_only", "code_path": str(code_path)})
        else:
            code_path.write_text(
                f"def {module}():\n    \"\"\"Harness stub for {arm}.\"\"\"\n    return None\n",
                encoding="utf-8",
            )
            loop_notes.append("harness_only: wrote minimal stub (no baseline)")
            rounds.append({"stage": "harness_only", "code_path": str(code_path)})
    else:
        if not allow_llm:
            raise RuntimeError("M2 generation requires --allow-llm (or use --harness-only for CI)")
        gen_cmd = [
            pdd,
            "generate",
            str(prompt_path),
            "--output",
            str(code_path),
            "--force",
            "--evidence",
        ]
        gen_entry = run_logged_command(gen_cmd, cwd=project_root, log_path=commands_log)
        rounds.append({"stage": "generate", **gen_entry})
        economics["generation_rounds"] = 1
        total_cost += float(gen_entry.get("cost_usd") or 0)
        total_wall += float(gen_entry.get("wall_clock_s") or 0)

        if gen_entry.get("exit_code") != 0:
            economics["wall_clock_s"] = round(total_wall, 3)
            economics["cost_usd"] = round(total_cost, 6)
            return GenerationLoopResult(
                arm=arm,
                prompt_path=prompt_path,
                work_dir=work_dir,
                code_path=code_path,
                generated_test_path=test_path,
                economics=economics,
                rounds=rounds,
                notes=["generate failed"] + loop_notes,
            )

        test_cmd = [
            pdd,
            "test",
            str(prompt_path),
            str(code_path),
            "--output",
            str(test_path),
            "--force",
            "--evidence",
        ]
        test_entry = run_logged_command(test_cmd, cwd=project_root, log_path=commands_log)
        rounds.append({"stage": "test", **test_entry})
        total_cost += float(test_entry.get("cost_usd") or 0)
        total_wall += float(test_entry.get("wall_clock_s") or 0)

        fix_rounds = 0
        for fix_idx in range(max_rounds):
            gen_metrics = run_pytest([test_path], pythonpath=[src_dir], cwd=project_root)
            rounds.append({"stage": f"pytest_generated_{fix_idx}", **gen_metrics})
            if gen_metrics.get("test_pass_rate") == 1.0:
                break
            if fix_idx + 1 >= max_rounds:
                break
            fix_cmd = [pdd, "fix", str(prompt_path), str(code_path), str(test_path)]
            fix_entry = run_logged_command(fix_cmd, cwd=project_root, log_path=commands_log)
            rounds.append({"stage": "fix", "round": fix_idx + 1, **fix_entry})
            fix_rounds += 1
            total_cost += float(fix_entry.get("cost_usd") or 0)
            total_wall += float(fix_entry.get("wall_clock_s") or 0)
            if fix_entry.get("exit_code") != 0:
                break
        economics["fix_rounds"] = fix_rounds

    gen_metrics = run_pytest([test_path], pythonpath=[src_dir], cwd=project_root)
    non_oracle_rate = gen_metrics.get("test_pass_rate")
    economics["generated_test_pass_rate"] = non_oracle_rate
    economics["non_oracle_test_pass_rate"] = non_oracle_rate
    rounds.append({"stage": "pytest_non_oracle", **gen_metrics})

    oracle_rate = None
    if oracle_test_dir and oracle_test_dir.is_dir():
        oracle_metrics = run_pytest(
            list(oracle_test_dir.glob("test_*.py")),
            pythonpath=[src_dir],
            cwd=project_root,
        )
        economics["oracle_test_pass_rate"] = oracle_metrics.get("test_pass_rate")
        oracle_rate = oracle_metrics.get("test_pass_rate")
        rounds.append({"stage": "pytest_oracle", **oracle_metrics})
    else:
        economics["oracle_test_pass_rate"] = None

    economics["evaluation_modes"] = evaluation_modes_summary(economics)

    economics["rounds_to_acceptable"] = (
        1
        if oracle_rate == 1.0 or gen_metrics.get("test_pass_rate") == 1.0
        else max_rounds + 1
    )
    economics["wall_clock_s"] = round(total_wall, 3)
    economics["cost_usd"] = round(total_cost, 6)
    economics["milestone_measured"] = 2

    append_jsonl(commands_log, {"stage": "economics", "economics": economics})

    return GenerationLoopResult(
        arm=arm,
        prompt_path=prompt_path,
        work_dir=work_dir,
        code_path=code_path,
        generated_test_path=test_path,
        economics=economics,
        rounds=rounds,
        notes=loop_notes,
    )
