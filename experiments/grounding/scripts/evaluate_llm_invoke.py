#!/usr/bin/env python3
"""Evaluate llm_invoke regeneration results: test suite execution and similarity metrics.

Runs after run_llm_invoke_stability.py. For each generated file:
  1. Reference similarity (difflib.SequenceMatcher) vs canonical llm_invoke.py
  2. Pairwise similarity between runs within each arm
  3. Test suite execution with PYTHONPATH isolation

Usage:
    python3 scripts/evaluate_llm_invoke.py
"""

from __future__ import annotations

import csv
import difflib
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Tuple

RESULTS_DIR = Path(__file__).resolve().parent.parent / "results"
GENERATIONS_DIR = RESULTS_DIR / "llm_invoke_generations"
EVAL_CSV_PATH = RESULTS_DIR / "llm_invoke_evaluation.csv"
STABILITY_CSV_PATH = RESULTS_DIR / "llm_invoke_stability.csv"

PDD_REPO_ROOT = Path("/Users/gregtanaka/Documents/pdd_cloud/pdd")
CANONICAL_FILE = PDD_REPO_ROOT / "pdd" / "llm_invoke.py"
TEST_FILE = PDD_REPO_ROOT / "tests" / "test_llm_invoke.py"

EVAL_FIELDS = [
    "arm",
    "run_number",
    "syntax_valid",
    "line_count",
    "function_count",
    "class_count",
    "reference_similarity",
    "tests_total",
    "tests_passed",
    "tests_failed",
    "tests_error",
    "test_runtime_seconds",
]

TEST_TIMEOUT = 300  # seconds


# ---------------------------------------------------------------------------
# Stability CSV reader
# ---------------------------------------------------------------------------

def _load_stability_csv() -> List[Dict[str, str]]:
    """Load the generation stability CSV."""
    if not STABILITY_CSV_PATH.exists():
        return []
    with STABILITY_CSV_PATH.open("r", encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f))


# ---------------------------------------------------------------------------
# Similarity
# ---------------------------------------------------------------------------

def _sequence_matcher_ratio(a: str, b: str) -> float:
    """Compute difflib.SequenceMatcher ratio between two strings."""
    if a == b:
        return 1.0
    if not a or not b:
        return 0.0
    return difflib.SequenceMatcher(None, a, b).ratio()


# ---------------------------------------------------------------------------
# Test execution with PYTHONPATH isolation
# ---------------------------------------------------------------------------

def _run_tests_isolated(generated_file: Path) -> Dict[str, Any]:
    """Run test_llm_invoke.py with the generated file replacing llm_invoke.py.

    Creates a temp directory with symlinked pdd package, swapping only
    llm_invoke.py, then runs pytest with PYTHONPATH override.
    """
    pdd_src = PDD_REPO_ROOT / "pdd"

    with tempfile.TemporaryDirectory(prefix="llm_invoke_eval_") as tmp:
        tmp_path = Path(tmp)
        pdd_pkg = tmp_path / "pdd"
        pdd_pkg.mkdir()

        # Symlink all pdd source files/dirs except llm_invoke.py and __pycache__
        for item in pdd_src.iterdir():
            if item.name in ("llm_invoke.py", "__pycache__"):
                continue
            target = pdd_pkg / item.name
            target.symlink_to(item)

        # Copy generated llm_invoke.py into the temp package
        shutil.copy2(generated_file, pdd_pkg / "llm_invoke.py")

        # Run pytest with PYTHONPATH override so `from pdd.llm_invoke import ...`
        # picks up the generated version
        env = os.environ.copy()
        env["PYTHONPATH"] = str(tmp_path) + ":" + env.get("PYTHONPATH", "")

        start = __import__("time").monotonic()
        try:
            result = subprocess.run(
                [
                    "pytest", "--tb=line", "-q",
                    str(TEST_FILE),
                ],
                capture_output=True,
                text=True,
                timeout=TEST_TIMEOUT,
                env=env,
                cwd=str(PDD_REPO_ROOT),
            )
            elapsed = __import__("time").monotonic() - start
        except subprocess.TimeoutExpired:
            elapsed = TEST_TIMEOUT
            return {
                "tests_total": 0,
                "tests_passed": 0,
                "tests_failed": 0,
                "tests_error": 0,
                "test_runtime_seconds": round(elapsed, 1),
                "raw_output": f"TIMEOUT after {TEST_TIMEOUT}s",
            }

        return {
            **_parse_pytest_output(result),
            "test_runtime_seconds": round(elapsed, 1),
        }


def _parse_pytest_output(result: subprocess.CompletedProcess) -> Dict[str, Any]:
    """Parse pytest -q output for pass/fail/error counts."""
    output = result.stdout + "\n" + result.stderr
    raw = output.strip()

    # Match patterns like "85 passed", "3 failed", "2 error"
    passed = 0
    failed = 0
    errors = 0

    # pytest summary line: "X passed, Y failed, Z error in Ns"
    summary_match = re.search(
        r"(\d+) passed", raw
    )
    if summary_match:
        passed = int(summary_match.group(1))

    fail_match = re.search(r"(\d+) failed", raw)
    if fail_match:
        failed = int(fail_match.group(1))

    error_match = re.search(r"(\d+) error", raw)
    if error_match:
        errors = int(error_match.group(1))

    total = passed + failed + errors

    # If no summary line found and returncode != 0, likely import/collection error
    if total == 0 and result.returncode != 0:
        # Try to count expected tests from "X error" in the output
        # or fall back to marking everything as error
        errors = max(1, errors)
        total = errors

    return {
        "tests_total": total,
        "tests_passed": passed,
        "tests_failed": failed,
        "tests_error": errors,
        "raw_output": raw[-500:],  # last 500 chars for debugging
    }


# ---------------------------------------------------------------------------
# Main evaluator
# ---------------------------------------------------------------------------

def main() -> int:
    """Evaluate all generated llm_invoke files."""
    stability_rows = _load_stability_csv()
    if not stability_rows:
        print(f"No stability results found at {STABILITY_CSV_PATH}")
        print("Run the generation first: make llm-invoke-prod")
        return 1

    if not CANONICAL_FILE.exists():
        print(f"Canonical file not found: {CANONICAL_FILE}")
        return 1

    canonical_code = CANONICAL_FILE.read_text(encoding="utf-8")

    # Collect generated files grouped by arm
    arms = ["grounded", "ungrounded"]
    files_by_arm: Dict[str, List[Tuple[int, Path]]] = {arm: [] for arm in arms}

    for row in stability_rows:
        arm = row["arm"]
        run_num = int(row["run_number"])
        gen_file = GENERATIONS_DIR / f"llm_invoke_{arm}_run{run_num}.py"
        if gen_file.exists():
            files_by_arm[arm].append((run_num, gen_file))

    total_files = sum(len(v) for v in files_by_arm.values())
    if total_files == 0:
        print(f"No generated files found in {GENERATIONS_DIR}")
        return 1

    print(f"\nllm_invoke Evaluation")
    print(f"{'=' * 70}")
    print(f"Canonical:    {CANONICAL_FILE} ({len(canonical_code.splitlines())} lines)")
    print(f"Test file:    {TEST_FILE}")
    print(f"Generations:  {total_files} files")
    print(f"{'=' * 70}\n")

    # Init eval CSV
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    with EVAL_CSV_PATH.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=EVAL_FIELDS)
        writer.writeheader()

    eval_rows: List[Dict[str, Any]] = []

    for arm in arms:
        arm_files = sorted(files_by_arm[arm], key=lambda x: x[0])
        print(f"Arm: {arm} ({len(arm_files)} files)")

        for run_num, gen_file in arm_files:
            print(f"  Run {run_num}: {gen_file.name}...", end="", flush=True)

            code = gen_file.read_text(encoding="utf-8")

            # Get syntax_valid, function_count, class_count from stability CSV
            matching_rows = [
                r for r in stability_rows
                if r["arm"] == arm and int(r["run_number"]) == run_num
            ]
            if matching_rows:
                syntax_valid = matching_rows[0].get("syntax_valid", "").lower() == "true"
                func_count = int(matching_rows[0].get("function_count", 0))
                cls_count = int(matching_rows[0].get("class_count", 0))
            else:
                syntax_valid = False
                func_count = 0
                cls_count = 0

            line_count = len(code.splitlines())

            # Reference similarity (difflib — O(n) average, safe for 100KB files)
            ref_sim = _sequence_matcher_ratio(code, canonical_code)

            # Test execution
            if syntax_valid:
                test_result = _run_tests_isolated(gen_file)
            else:
                test_result = {
                    "tests_total": 0,
                    "tests_passed": 0,
                    "tests_failed": 0,
                    "tests_error": 0,
                    "test_runtime_seconds": 0.0,
                    "raw_output": "SKIPPED: syntax invalid",
                }

            row = {
                "arm": arm,
                "run_number": run_num,
                "syntax_valid": syntax_valid,
                "line_count": line_count,
                "function_count": func_count,
                "class_count": cls_count,
                "reference_similarity": round(ref_sim, 4),
                "tests_total": test_result["tests_total"],
                "tests_passed": test_result["tests_passed"],
                "tests_failed": test_result["tests_failed"],
                "tests_error": test_result["tests_error"],
                "test_runtime_seconds": test_result["test_runtime_seconds"],
            }
            eval_rows.append(row)

            # Append to CSV
            with EVAL_CSV_PATH.open("a", newline="", encoding="utf-8") as f:
                writer = csv.DictWriter(f, fieldnames=EVAL_FIELDS)
                writer.writerow(row)

            # Status
            t_pass = test_result["tests_passed"]
            t_total = test_result["tests_total"]
            print(
                f" ref_sim={ref_sim:.3f} "
                f"tests={t_pass}/{t_total} "
                f"time={test_result['test_runtime_seconds']}s"
            )

        print()

    # Pairwise similarity within each arm
    print("Pairwise Similarity (within arm)")
    print("-" * 40)
    for arm in arms:
        arm_files = sorted(files_by_arm[arm], key=lambda x: x[0])
        codes = [f.read_text(encoding="utf-8") for _, f in arm_files]
        if len(codes) < 2:
            print(f"  {arm}: N/A (< 2 files)")
            continue

        sims = []
        for i in range(len(codes)):
            for j in range(i + 1, len(codes)):
                sims.append(_sequence_matcher_ratio(codes[i], codes[j]))

        avg_sim = sum(sims) / len(sims) if sims else 0.0
        min_sim = min(sims) if sims else 0.0
        max_sim = max(sims) if sims else 0.0
        print(f"  {arm}: avg={avg_sim:.3f} min={min_sim:.3f} max={max_sim:.3f}")

    print(f"\nEvaluation CSV: {EVAL_CSV_PATH}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
