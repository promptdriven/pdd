"""
Example: compression_benchmark module
======================================

Demonstrates how to use the compression_benchmark module to:
  1. Run a benchmark across fixture directories (frozen-fixture mode, no live LLM).
  2. Check the gate (R1–R3: contract-symbol loss, pass-rate regression, churn).
  3. Print a rich Markdown table and optionally write a JSON report.

Functions shown:
  - run_benchmark(fixtures_dir, *, strategies=None, live_llm=False) -> list[CompressionBenchmarkResult]
  - check_compression_benchmark(results, baselines) -> GateResult
  - print_benchmark_report(results, *, output_path=None) -> None

Return types:
  - CompressionBenchmarkResult: dataclass with strategy, fixture_id, passed (bool),
    input_tokens (int), elapsed_sec (float), churn_score (float [0,1]),
    missing_contracts (list[str])
  - GateResult: passed (bool), failures (list[GateFailure]), exit_code (int)
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from pathlib import Path
from unittest.mock import patch, MagicMock

from pdd.compression_benchmark import (
    run_benchmark,
    check_compression_benchmark,
    print_benchmark_report,
    CompressionBenchmarkResult,
    ALL_STRATEGIES,
)


# ---------------------------------------------------------------------------
# Helpers: build fake fixtures in a temp dir so the example is self-contained
# ---------------------------------------------------------------------------

def _make_fixture(base: Path, name: str) -> Path:
    """Create a minimal fixture directory with all required files."""
    d = base / name
    d.mkdir(parents=True, exist_ok=True)

    # Minimal valid Python source
    (d / "source.py").write_text(
        "from __future__ import annotations\n\n"
        "def _helper(x: int) -> int:\n    return x * 2\n\n"
        "def compute(x: int) -> int:\n    return _helper(x)\n",
        encoding="utf-8",
    )

    # Minimal test file
    (d / "test_file.py").write_text(
        "from __future__ import annotations\n\n"
        "def test_compute():\n    from source import compute\n    assert compute(3) == 6\n",
        encoding="utf-8",
    )

    # Seeds that both functions exist in source
    (d / "contract_seeds.json").write_text('["compute", "_helper"]', encoding="utf-8")

    # Simulated LLM output that includes both seeds — passes R1/R2
    full_output = (
        "from __future__ import annotations\n\n"
        "def _helper(x: int) -> int:\n    return x * 2\n\n"
        "def compute(x: int) -> int:\n    return _helper(x)\n"
    )
    # Per-strategy outputs: all pass for demo
    for strategy in ALL_STRATEGIES:
        (d / f"expected_output_{strategy}.py").write_text(full_output, encoding="utf-8")
    (d / "expected_output.py").write_text(full_output, encoding="utf-8")

    # Baselines: all strategies should pass with high churn
    import json
    baselines = {}
    for strategy in ALL_STRATEGIES:
        baselines[strategy] = {
            "passed": True,
            "max_input_tokens": 1000,
            "min_churn_score": 0.85,
        }
    (d / "expected_results.json").write_text(json.dumps(baselines, indent=2), encoding="utf-8")

    return d


def main() -> None:
    import tempfile
    import json

    print("=" * 60)
    print("compression_benchmark module example")
    print("=" * 60)
    print()

    # -----------------------------------------------------------------------
    # Section 1: Run benchmark on the real fixture included in the repo
    # -----------------------------------------------------------------------
    real_fixtures = Path(__file__).resolve().parent.parent / "tests" / "fixtures" / "compression_benchmark"

    if real_fixtures.is_dir():
        print("Section 1: Running benchmark on real repo fixture")
        print("-" * 50)

        # Mock external dependencies so no real LLM/tiktoken calls are needed
        with patch("pdd.compression_benchmark.count_tokens", return_value=120), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer_cls:

            # ContentSelector.select returns a stub string
            mock_cs.select.return_value = "def stub(): pass\n"

            # ApiContractSlicer instance: slice() returns (str, manifest)
            mock_slicer_inst = MagicMock()
            mock_slicer_inst.slice.return_value = (
                "def _get_job_secrets(): pass\ndef run_worker(): pass\n",
                MagicMock(),
            )
            mock_slicer_cls.return_value = mock_slicer_inst

            # ApiContractSlicer.verify_contract (static) — does not raise for passing outputs
            mock_slicer_cls.verify_contract = MagicMock()

            results = run_benchmark(real_fixtures, strategies=["ast_contracts", "full_tests"])

        print(f"Results collected: {len(results)} entries")
        for r in results:
            status = "PASS" if r.passed else "FAIL"
            print(
                f"  [{status}] fixture={r.fixture_id} strategy={r.strategy} "
                f"tokens={r.input_tokens} churn={r.churn_score:.3f} "
                f"missing={r.missing_contracts}"
            )
        print()
    else:
        print("(Real fixture directory not found — skipping Section 1)")
        print()
        results = []

    # -----------------------------------------------------------------------
    # Section 2: Run benchmark on a synthetic temp fixture
    # -----------------------------------------------------------------------
    print("Section 2: Running benchmark on synthetic temp fixture")
    print("-" * 50)

    with tempfile.TemporaryDirectory() as tmp:
        fixtures_dir = Path(tmp)
        _make_fixture(fixtures_dir, "demo_fixture")

        with patch("pdd.compression_benchmark.count_tokens", return_value=42), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs2, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer2:

            mock_cs2.select.return_value = "def compute(x): ...\n"

            mock_inst2 = MagicMock()
            mock_inst2.slice.return_value = (
                "def _helper(x): ...\ndef compute(x): ...\n",
                MagicMock(),
            )
            mock_slicer2.return_value = mock_inst2
            mock_slicer2.verify_contract = MagicMock()  # no-raise = pass

            synthetic_results = run_benchmark(fixtures_dir, strategies=["full_tests", "ast_contracts"])

        print(f"Synthetic results: {len(synthetic_results)} entries")
        for r in synthetic_results:
            print(
                f"  strategy={r.strategy} passed={r.passed} "
                f"input_tokens={r.input_tokens} elapsed_sec={r.elapsed_sec:.4f} "
                f"churn={r.churn_score:.3f}"
            )
        print()

        # -----------------------------------------------------------------------
        # Section 3: Gate check
        # -----------------------------------------------------------------------
        print("Section 3: check_compression_benchmark (gate R1-R3)")
        print("-" * 50)

        baselines = {
            "demo_fixture": {
                strategy: {"passed": True, "max_input_tokens": 1000, "min_churn_score": 0.85}
                for strategy in ["full_tests", "ast_contracts"]
            }
        }

        gate = check_compression_benchmark(synthetic_results, baselines)
        print(f"Gate passed : {gate.passed}")
        print(f"Exit code   : {gate.exit_code}")
        print(f"Manifests   : {gate.manifests_checked}")
        if gate.failures:
            for f in gate.failures:
                print(f"  FAILURE [{f.code}]: {f.message}")
        else:
            print("  No failures — all gates passed.")
        print()

        # -----------------------------------------------------------------------
        # Section 4: print_benchmark_report with JSON output
        # -----------------------------------------------------------------------
        print("Section 4: print_benchmark_report")
        print("-" * 50)

        report_path = fixtures_dir / "benchmark_report.json"
        print_benchmark_report(synthetic_results, output_path=report_path)

        if report_path.exists():
            report_data = json.loads(report_path.read_text(encoding="utf-8"))
            print(f"JSON report written: {len(report_data)} entries")
            print(f"First entry keys: {list(report_data[0].keys())}")
        print()

    print("=" * 60)
    print("Example complete — all steps ran without error.")
    print("=" * 60)


if __name__ == "__main__":
    main()
