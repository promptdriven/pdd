"""Core logic for the PDD formalization benchmark."""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional

import yaml

from pdd.contract_check import check_prompt, check_stories
from pdd.coverage_contracts import build_coverage
from pdd.prompt_lint import scan_prompt

BENCHMARK_VERSION = "0.3.0"
ARMS = ("A0", "A1", "A2")


@dataclass
class TaskConfig:
    """Parsed ``task.yaml`` for one benchmark task."""

    task_id: str
    description: str
    root: Path
    a0_prompt: Optional[Path] = None
    a1_prompt: Optional[Path] = None
    a1_stories_dir: Optional[Path] = None
    a1_tests_dir: Optional[Path] = None
    a2_test_paths: list[Path] = field(default_factory=list)
    a2_pythonpath: list[Path] = field(default_factory=list)
    evidence_paths: list[Path] = field(default_factory=list)


def benchmark_root() -> Path:
    """Return the ``benchmarks/formalization`` directory."""
    return Path(__file__).resolve().parent


def load_task_config(task_dir: Path) -> TaskConfig:
    """Load ``task.yaml`` from a task directory."""
    config_path = task_dir / "task.yaml"
    if not config_path.is_file():
        raise FileNotFoundError(f"Missing task config: {config_path}")

    raw = yaml.safe_load(config_path.read_text(encoding="utf-8")) or {}
    task_id = str(raw.get("id", task_dir.name))
    description = str(raw.get("description", ""))

    def _resolve(rel: Optional[str]) -> Optional[Path]:
        if not rel:
            return None
        path = (task_dir / rel).resolve()
        return path

    arms = raw.get("arms") or {}
    a0 = arms.get("a0") or {}
    a1 = arms.get("a1") or {}
    a2 = arms.get("a2") or {}

    a2_tests = [
        (task_dir / rel).resolve()
        for rel in (a2.get("test_paths") or [])
    ]
    a2_pythonpath = [
        (task_dir / rel).resolve()
        for rel in (a2.get("pythonpath") or [])
    ]
    evidence_paths = [
        (task_dir / rel).resolve()
        for rel in (raw.get("evidence_paths") or [])
    ]

    return TaskConfig(
        task_id=task_id,
        description=description,
        root=task_dir.resolve(),
        a0_prompt=_resolve(a0.get("prompt")),
        a1_prompt=_resolve(a1.get("prompt")),
        a1_stories_dir=_resolve(a1.get("stories_dir")),
        a1_tests_dir=_resolve(a1.get("tests_dir")),
        a2_test_paths=a2_tests,
        a2_pythonpath=a2_pythonpath,
        evidence_paths=evidence_paths,
    )


def discover_tasks(tasks_dir: Path, *, task_ids: Optional[list[str]] = None) -> list[TaskConfig]:
    """Discover tasks under ``tasks/``."""
    configs: list[TaskConfig] = []
    for child in sorted(tasks_dir.iterdir()):
        if not child.is_dir():
            continue
        if not (child / "task.yaml").is_file():
            continue
        cfg = load_task_config(child)
        if task_ids and cfg.task_id not in task_ids:
            continue
        configs.append(cfg)
    if not configs:
        raise FileNotFoundError(f"No tasks found under {tasks_dir}")
    return configs


def _empty_metrics() -> dict[str, Any]:
    return {
        "prompt_lint_warnings": None,
        "prompt_lint_errors": None,
        "contract_check_errors": None,
        "contract_check_warnings": None,
        "formalization_records": None,
        "formal_candidate_rules": None,
        "z3_test_count": None,
        "total_rules": None,
        "checked_rules": None,
        "story_only_rules": None,
        "test_only_rules": None,
        "unchecked_rules": None,
        "waived_rules": None,
        "test_pass_rate": None,
        "test_passed": None,
        "test_failed": None,
        "test_total": None,
        "evidence_manifest_present": None,
        "generated_file_count": None,
        "wall_clock_s": 0.0,
    }


def _count_z3_tests(test_paths: list[Path]) -> int:
    """Count test functions whose names or bodies indicate Z3 formal tests."""
    count = 0
    for path in test_paths:
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        if "importorskip(\"z3\")" in text or "from z3 import" in text:
            count += text.count("def test_z3_")
    return count


def _formalization_stats(prompt_path: Path) -> tuple[Optional[int], Optional[int]]:
    """Return (formalization_record_count, formal_candidate_rule_count)."""
    from pdd.contract_ir import parse_prompt_contracts  # pylint: disable=import-outside-toplevel

    ir = parse_prompt_contracts(prompt_path)
    if not ir.formalizations:
        return 0, 0
    formal_candidates = sum(
        1
        for record in ir.formalizations
        if "FORMAL_CANDIDATE" in (record.level or "").upper()
    )
    return len(ir.formalizations), formal_candidates


def _collect_prompt_metrics(
    prompt_path: Path,
    *,
    stories_dir: Optional[Path],
    tests_dir: Optional[Path],
    notes: list[str],
) -> dict[str, Any]:
    """Run lint, contract check, and coverage for one prompt."""
    metrics = _empty_metrics()

    lint = scan_prompt(prompt_path, strict=False)
    metrics["prompt_lint_warnings"] = lint.warn_count
    metrics["prompt_lint_errors"] = lint.error_count

    record_count, formal_candidate_count = _formalization_stats(prompt_path)
    metrics["formalization_records"] = record_count
    metrics["formal_candidate_rules"] = formal_candidate_count
    if formal_candidate_count == 0:
        notes.append(
            "No FORMAL_CANDIDATE entries in <formalization>; "
            "pdd test is unlikely to emit Z3 proofs."
        )

    contract = check_prompt(prompt_path, strict=False)
    if stories_dir and stories_dir.is_dir():
        for story_result in check_stories(stories_dir, prompt_path.parent, strict=False):
            contract.issues.extend(story_result.issues)
    metrics["contract_check_errors"] = contract.error_count
    metrics["contract_check_warnings"] = contract.warn_count

    stories = stories_dir if stories_dir and stories_dir.is_dir() else None
    tests = tests_dir if tests_dir and tests_dir.is_dir() else None
    coverage = build_coverage(prompt_path, stories, tests)
    if not coverage.has_contract_rules:
        notes.append("Prompt has no <contract_rules>; coverage counts are zero.")
    summary = coverage.summary
    metrics["total_rules"] = summary.get("total", 0)
    metrics["checked_rules"] = summary.get("checked", 0)
    metrics["story_only_rules"] = summary.get("story_only", 0)
    metrics["test_only_rules"] = summary.get("test_only", 0)
    metrics["unchecked_rules"] = summary.get("unchecked", 0)
    metrics["waived_rules"] = summary.get("waived", 0)

    return metrics


def _run_pytest(
    test_paths: list[Path],
    *,
    pythonpath: list[Path],
    notes: list[str],
) -> dict[str, Any]:
    """Run pytest on the given paths and return test metrics."""
    metrics = _empty_metrics()
    existing = [p for p in test_paths if p.exists()]
    if not existing:
        notes.append("No test files found for pytest arm; test_pass_rate is null.")
        return metrics

    env = dict(os.environ)
    if pythonpath:
        prefix = os.pathsep.join(str(p) for p in pythonpath)
        env["PYTHONPATH"] = (
            f"{prefix}{os.pathsep}{env['PYTHONPATH']}"
            if env.get("PYTHONPATH")
            else prefix
        )

    cmd = [sys.executable, "-m", "pytest", "-q", "--tb=no", *[str(p) for p in existing]]
    completed = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        check=False,
        env=env,
    )
    stdout = completed.stdout + "\n" + completed.stderr
    passed = failed = errors = 0
    for match in re.finditer(r"(\d+)\s+passed", stdout):
        passed = max(passed, int(match.group(1)))
    for match in re.finditer(r"(\d+)\s+failed", stdout):
        failed = max(failed, int(match.group(1)))
    for match in re.finditer(r"(\d+)\s+error", stdout):
        errors = max(errors, int(match.group(1)))

    total = passed + failed + errors
    if total == 0:
        if completed.returncode == 0:
            collected = subprocess.run(
                [
                    sys.executable,
                    "-m",
                    "pytest",
                    "--collect-only",
                    "-q",
                    *[str(p) for p in existing],
                ],
                capture_output=True,
                text=True,
                check=False,
                env=env,
            )
            collect_out = collected.stdout + collected.stderr
            collected_count = sum(
                1
                for line in collect_out.splitlines()
                if "test_" in line and ("::" in line or line.strip().endswith(".py"))
            )
            if collected_count > 0:
                passed = collected_count
                total = collected_count
                notes.append(
                    "pytest -q summary had no counts; used --collect-only fallback."
                )
            else:
                notes.append(
                    f"pytest exit {completed.returncode} with no parseable test counts."
                )
                metrics["test_pass_rate"] = 1.0 if completed.returncode == 0 else 0.0
                return metrics
        else:
            notes.append(f"pytest failed (exit {completed.returncode}) with no test counts.")
            metrics["test_pass_rate"] = 0.0
            return metrics

    metrics["test_passed"] = passed
    metrics["test_failed"] = failed + errors
    metrics["test_total"] = total
    metrics["test_pass_rate"] = passed / total if total else None
    if completed.returncode != 0:
        notes.append(f"pytest exited with code {completed.returncode}")
    return metrics


def _count_generated_files(task_root: Path) -> tuple[Optional[int], list[str]]:
    """Count files under ``generated/`` if present."""
    generated = task_root / "generated"
    if not generated.is_dir():
        return None, ["No generated/ directory; generated_file_count is null."]
    count = sum(1 for path in generated.rglob("*") if path.is_file())
    return count, []


def _evidence_present(paths: list[Path], notes: list[str]) -> Optional[bool]:
    """Return whether any configured evidence manifest path exists."""
    if not paths:
        notes.append("No evidence_paths in task.yaml; evidence_manifest_present is null.")
        return None
    return any(path.is_file() for path in paths)


def run_arm(task: TaskConfig, arm: str) -> dict[str, Any]:
    """Execute one benchmark arm and return a schema-shaped result dict."""
    notes: list[str] = []
    metrics = _empty_metrics()
    command_success = True
    start = time.perf_counter()

    try:
        if arm == "A0":
            if task.a0_prompt is None or not task.a0_prompt.is_file():
                raise FileNotFoundError(f"A0 prompt missing for task {task.task_id}")
            metrics.update(
                _collect_prompt_metrics(
                    task.a0_prompt,
                    stories_dir=None,
                    tests_dir=None,
                    notes=notes,
                )
            )
            notes.append(
                "A0 arm: contract/coverage reflect ad-hoc prompt only; "
                "no story/test dirs wired for this arm."
            )
        elif arm == "A1":
            if task.a1_prompt is None or not task.a1_prompt.is_file():
                raise FileNotFoundError(f"A1 prompt missing for task {task.task_id}")
            metrics.update(
                _collect_prompt_metrics(
                    task.a1_prompt,
                    stories_dir=task.a1_stories_dir,
                    tests_dir=task.a1_tests_dir,
                    notes=notes,
                )
            )
            if task.a1_tests_dir and task.a1_tests_dir.is_dir():
                test_files = list(task.a1_tests_dir.rglob("test_*.py"))
                metrics["z3_test_count"] = _count_z3_tests(test_files)
                test_metrics = _run_pytest(
                    test_files,
                    pythonpath=task.a2_pythonpath,
                    notes=notes,
                )
                for key in (
                    "test_pass_rate",
                    "test_passed",
                    "test_failed",
                    "test_total",
                ):
                    if test_metrics[key] is not None:
                        metrics[key] = test_metrics[key]
            else:
                notes.append("A1 has no tests_dir; test_pass_rate is null.")
        elif arm == "A2":
            notes.append(
                "A2 code-as-SOT arm: prompt lint/contract/coverage metrics are null by design."
            )
            if not task.a2_test_paths:
                notes.append("A2 has no test_paths configured; test_pass_rate is null.")
            else:
                test_metrics = _run_pytest(
                    task.a2_test_paths,
                    pythonpath=task.a2_pythonpath,
                    notes=notes,
                )
                metrics.update(
                    {k: test_metrics[k] for k in test_metrics if k.startswith("test_")}
                )
        else:
            raise ValueError(f"Unknown arm: {arm}")

        gen_count, gen_notes = _count_generated_files(task.root)
        metrics["generated_file_count"] = gen_count
        notes.extend(gen_notes)
        metrics["evidence_manifest_present"] = _evidence_present(
            task.evidence_paths,
            notes,
        )
    except Exception as exc:  # pylint: disable=broad-except
        command_success = False
        notes.append(f"arm run failed: {exc!s}")

    metrics["wall_clock_s"] = round(time.perf_counter() - start, 4)

    prompt_for_epic: Optional[Path] = None
    stories_for_epic: Optional[Path] = None
    tests_for_epic: Optional[Path] = None
    if arm == "A0":
        prompt_for_epic = task.a0_prompt
    elif arm == "A1":
        prompt_for_epic = task.a1_prompt
        stories_for_epic = task.a1_stories_dir
        tests_for_epic = task.a1_tests_dir

    from _epic833 import evaluate_epic833  # pylint: disable=import-outside-toplevel

    epic833 = evaluate_epic833(
        arm=arm,
        prompt_path=prompt_for_epic,
        stories_dir=stories_for_epic,
        tests_dir=tests_for_epic,
        metrics=metrics,
        evidence_paths=task.evidence_paths,
    )

    return {
        "benchmark_version": BENCHMARK_VERSION,
        "task_id": task.task_id,
        "arm": arm,
        "collected_at": datetime.now(timezone.utc).isoformat(),
        "command_success": command_success,
        "metrics": metrics,
        "epic833": epic833,
        "notes": notes,
    }


def run_benchmark(
    *,
    tasks_dir: Path,
    results_dir: Path,
    task_ids: Optional[list[str]] = None,
    arms: Optional[list[str]] = None,
) -> dict[str, Any]:
    """Run all task/arm combinations and write JSON artifacts."""
    selected_arms = tuple(arms or ARMS)
    for arm in selected_arms:
        if arm not in ARMS:
            raise ValueError(f"Invalid arm {arm!r}; expected one of {ARMS}")

    tasks = discover_tasks(tasks_dir, task_ids=task_ids)
    results_dir.mkdir(parents=True, exist_ok=True)

    runs: list[dict[str, Any]] = []
    for task in tasks:
        task_results_dir = results_dir / task.task_id
        task_results_dir.mkdir(parents=True, exist_ok=True)
        for arm in selected_arms:
            payload = run_arm(task, arm)
            runs.append(payload)
            out_path = task_results_dir / f"{arm}.json"
            out_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    aggregate = {
        "benchmark_version": BENCHMARK_VERSION,
        "collected_at": datetime.now(timezone.utc).isoformat(),
        "task_ids": [task.task_id for task in tasks],
        "runs": runs,
    }
    aggregate_path = results_dir / "aggregate.json"
    aggregate_path.write_text(json.dumps(aggregate, indent=2) + "\n", encoding="utf-8")
    return aggregate


def finalize_benchmark(
    aggregate: dict[str, Any],
    results_dir: Path,
    *,
    emit_report: bool = True,
) -> dict[str, Any]:
    """Write v1 summary artifacts (summary.json, REPORT.md)."""
    from _report import write_summary_artifacts  # pylint: disable=import-outside-toplevel

    return write_summary_artifacts(
        aggregate,
        results_dir,
        print_report=emit_report,
    )


def validate_run_payload(payload: dict[str, Any], schema_path: Path) -> None:
    """Validate a run payload against ``results.schema.json``."""
    import jsonschema

    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    jsonschema.validate(instance=payload, schema=schema)
