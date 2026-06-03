from __future__ import annotations

import difflib
import json
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Sequence, Any

from .api_contract_slicer import ApiContractSlicer, ContractSlicerError
from .content_selector import ContentSelector
from .server.token_counter import count_tokens
from .gate_main import GateFailure, GateResult

try:
    from . import PDD_COMPRESSION_CHURN_THRESHOLD
except ImportError:
    PDD_COMPRESSION_CHURN_THRESHOLD = 0.90

ALL_STRATEGIES = (
    "full_tests",
    "ast_tests",
    "ast_contracts",
    "full_fewshot",
    "compressed_fewshot",
)


@dataclass
class CompressionBenchmarkResult:
    strategy: str
    fixture_id: str
    passed: bool
    input_tokens: int
    elapsed_sec: float
    churn_score: float
    missing_contracts: list[str]


def _build_full_tests(fixture: dict[str, Any]) -> str:
    return fixture["test_file"]


def _build_ast_tests(fixture: dict[str, Any]) -> str:
    seeds_str = ",".join(fixture["seeds"])
    return ContentSelector.select(fixture["test_file"], f"contract:{seeds_str}")


def _build_ast_contracts(fixture: dict[str, Any]) -> str:
    slicer = ApiContractSlicer(fixture["source"])
    sliced_source, _ = slicer.slice(fixture["seeds"])
    return sliced_source


def _build_full_fewshot(fixture: dict[str, Any]) -> str:
    return fixture["test_file"]


def _build_compressed_fewshot(fixture: dict[str, Any]) -> str:
    contract = _build_ast_contracts(fixture)
    tests = _build_ast_tests(fixture)
    return f"{contract}\n{tests}"


_STRATEGY_BUILDERS = {
    "full_tests": _build_full_tests,
    "ast_tests": _build_ast_tests,
    "ast_contracts": _build_ast_contracts,
    "full_fewshot": _build_full_fewshot,
    "compressed_fewshot": _build_compressed_fewshot,
}


def _load_fixture(fixture_dir: Path) -> dict[str, Any]:
    source = (fixture_dir / "source.py").read_text(encoding="utf-8")
    test_file = (fixture_dir / "test_file.py").read_text(encoding="utf-8")
    seeds = json.loads((fixture_dir / "contract_seeds.json").read_text(encoding="utf-8"))
    expected_results = json.loads((fixture_dir / "expected_results.json").read_text(encoding="utf-8"))
    
    fallback_output_file = fixture_dir / "expected_output.py"
    fallback_output = fallback_output_file.read_text(encoding="utf-8") if fallback_output_file.exists() else ""

    expected_outputs = {}
    for strategy in ALL_STRATEGIES:
        strat_file = fixture_dir / f"expected_output_{strategy}.py"
        if strat_file.exists():
            expected_outputs[strategy] = strat_file.read_text(encoding="utf-8")
        else:
            expected_outputs[strategy] = fallback_output

    return {
        "fixture_id": fixture_dir.name,
        "source": source,
        "test_file": test_file,
        "seeds": seeds,
        "expected_results": expected_results,
        "expected_outputs": expected_outputs,
        "fallback_output": fallback_output,
    }


def run_benchmark(
    fixtures_dir: Path,
    *,
    strategies: Sequence[str] | None = None,
    live_llm: bool = False,
) -> list[CompressionBenchmarkResult]:
    if strategies is None:
        strategies = ALL_STRATEGIES

    results: list[CompressionBenchmarkResult] = []

    for fixture_dir in sorted(fixtures_dir.iterdir()):
        if not fixture_dir.is_dir():
            continue

        fixture = _load_fixture(fixture_dir)

        for strategy in strategies:
            builder = _STRATEGY_BUILDERS[strategy]
            
            t0 = time.perf_counter()
            context = builder(fixture)
            input_tokens = count_tokens(context)
            
            if live_llm:
                raise NotImplementedError("Live LLM benchmarking is not yet implemented.")
            else:
                actual_output = fixture["expected_outputs"][strategy]

            elapsed = time.perf_counter() - t0

            churn_score = difflib.SequenceMatcher(
                None, fixture["fallback_output"], actual_output
            ).ratio()

            missing_contracts: list[str] = []
            try:
                ApiContractSlicer.verify_contract(actual_output, fixture["seeds"])
            except ContractSlicerError as exc:
                msg = str(exc)
                if "missing symbols:" in msg:
                    symbols_part = msg.split("missing symbols:")[1].strip()
                    missing_contracts = [s.strip() for s in symbols_part.split(",")]
                else:
                    missing_contracts = ["<unknown parse error>"]

            passed = len(missing_contracts) == 0

            results.append(
                CompressionBenchmarkResult(
                    strategy=strategy,
                    fixture_id=fixture["fixture_id"],
                    passed=passed,
                    input_tokens=input_tokens,
                    elapsed_sec=elapsed,
                    churn_score=churn_score,
                    missing_contracts=missing_contracts,
                )
            )

    return results


def check_compression_benchmark(
    results: list[CompressionBenchmarkResult],
    baselines: dict[str, dict]
) -> GateResult:
    failures: list[GateFailure] = []
    manifests_checked = len(results)

    for res in results:
        fixture_baselines = baselines.get(res.fixture_id, {})
        baseline = fixture_baselines.get(res.strategy, {})
        if not baseline:
            continue

        baseline_passed = baseline.get("passed", False)
        min_churn = baseline.get("min_churn_score", 0.0)

        # R1: Contract-symbol gate
        if baseline_passed and res.missing_contracts:
            failures.append(
                GateFailure(
                    code="CONTRACT_SYMBOL_LOSS",
                    message=f"[{res.fixture_id} | {res.strategy}] Baseline passed but missing contracts: {res.missing_contracts}",
                )
            )

        # R2: Pass-rate gate
        if baseline_passed and not res.passed:
            failures.append(
                GateFailure(
                    code="PASS_RATE_REGRESSION",
                    message=f"[{res.fixture_id} | {res.strategy}] Pass rate regressed below baseline (expected True, got False).",
                )
            )

        # R3: Churn gate
        if res.churn_score < PDD_COMPRESSION_CHURN_THRESHOLD and res.churn_score < min_churn:
            failures.append(
                GateFailure(
                    code="CHURN_REGRESSION",
                    message=f"[{res.fixture_id} | {res.strategy}] Churn score {res.churn_score:.3f} below threshold {PDD_COMPRESSION_CHURN_THRESHOLD} and baseline {min_churn}.",
                )
            )

    return GateResult(
        passed=len(failures) == 0,
        failures=failures,
        manifests_checked=manifests_checked,
    )


def print_benchmark_report(
    results: list[CompressionBenchmarkResult],
    *,
    output_path: Path | None = None
) -> None:
    try:
        from rich.console import Console
        from rich.table import Table
    except ImportError:
        return

    console = Console()
    table = Table(title="Compression Benchmark Results")
    table.add_column("Fixture", style="cyan")
    table.add_column("Strategy", style="magenta")
    table.add_column("Passed", justify="center")
    table.add_column("Tokens", justify="right")
    table.add_column("Time (s)", justify="right")
    table.add_column("Churn", justify="right")
    table.add_column("Missing", style="red")

    for res in results:
        pass_emoji = "✅" if res.passed else "❌"
        table.add_row(
            res.fixture_id,
            res.strategy,
            pass_emoji,
            str(res.input_tokens),
            f"{res.elapsed_sec:.2f}",
            f"{res.churn_score:.3f}",
            ", ".join(res.missing_contracts) if res.missing_contracts else "-",
        )

    console.print(table)

    if output_path:
        out_data = [
            {
                "strategy": r.strategy,
                "fixture_id": r.fixture_id,
                "passed": r.passed,
                "input_tokens": r.input_tokens,
                "elapsed_sec": r.elapsed_sec,
                "churn_score": r.churn_score,
                "missing_contracts": r.missing_contracts,
            }
            for r in results
        ]
        output_path.write_text(json.dumps(out_data, indent=2), encoding="utf-8")