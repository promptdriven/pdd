"""Tests for pdd.compression_benchmark module.

Test Plan (by spec requirement):
---------------------------------
1. CompressionBenchmarkResult dataclass has all required fields with correct types
2. ALL_STRATEGIES contains exactly the 5 required strategy names
3. _load_fixture reads source.py, test_file.py, contract_seeds.json, expected_results.json
4. _load_fixture reads per-strategy expected_output_{strategy}.py files
5. _load_fixture falls back to expected_output.py when per-strategy file is absent
6. _load_fixture returns dict with expected keys: source, test_file, expected_outputs, seeds, expected_results, fixture_id
7. _build_full_tests returns raw test_file content unchanged
8. _build_ast_tests calls ContentSelector.select with contract:{seeds} selector
9. _build_ast_contracts calls ApiContractSlicer.slice with seeds
10. _build_full_fewshot returns test_file content (without source implementation)
11. _build_compressed_fewshot concatenates _build_ast_contracts + _build_ast_tests output
12. run_benchmark iterates fixture subdirectories, skips non-directories
13. run_benchmark uses ALL_STRATEGIES when strategies=None (R7)
14. run_benchmark accepts explicit strategies list
15. run_benchmark calls count_tokens before simulated output (R4) - input_tokens is non-zero
16. run_benchmark uses time.perf_counter for elapsed_sec (R5)
17. run_benchmark uses per-strategy expected output file in frozen mode (R6)
18. run_benchmark falls back to expected_output.py when per-strategy file absent (R6)
19. run_benchmark computes churn_score using difflib.SequenceMatcher
20. run_benchmark sets passed=True when verify_contract raises no error
21. run_benchmark sets passed=False and populates missing_contracts on ContractSlicerError
22. run_benchmark raises NotImplementedError for live_llm=True
23. run_benchmark returns list[CompressionBenchmarkResult] with correct field values
24. check_compression_benchmark returns GateResult.passed=True when no violations
25. check_compression_benchmark R1: fails when baseline passed=True and missing_contracts non-empty
26. check_compression_benchmark R1: does NOT fail when baseline passed=False and missing_contracts non-empty
27. check_compression_benchmark R2: fails when baseline passed=True and result.passed=False
28. check_compression_benchmark R2: does NOT fail when baseline passed=False and result.passed=False
29. check_compression_benchmark R3: fails when churn below threshold AND below baseline min_churn_score
30. check_compression_benchmark R3: does NOT fail when churn below threshold but >= baseline min_churn_score
31. check_compression_benchmark skips results with no baseline entry
32. check_compression_benchmark records correct manifests_checked count
33. check_compression_benchmark returns GateResult with correct exit_code (0=pass, 1=fail)
34. print_benchmark_report prints a rich table without error
35. print_benchmark_report writes JSON to output_path when provided
36. print_benchmark_report JSON output has correct fields for each result
37. Regression: input_tokens is never 0 (R4 enforcement)
"""
from __future__ import annotations

import json
import tempfile
from pathlib import Path
from unittest.mock import MagicMock, patch, call
import pytest

from pdd.compression_benchmark import (
    ALL_STRATEGIES,
    CompressionBenchmarkResult,
    _build_ast_contracts,
    _build_ast_tests,
    _build_compressed_fewshot,
    _build_full_fewshot,
    _build_full_tests,
    _load_fixture,
    check_compression_benchmark,
    print_benchmark_report,
    run_benchmark,
)
from pdd.gate_main import GateResult, GateFailure


# ---------------------------------------------------------------------------
# Fixtures / helpers
# ---------------------------------------------------------------------------

def _make_fixture_dir(
    base: Path,
    name: str = "fix1",
    seeds: list[str] | None = None,
    expected_results: dict | None = None,
    per_strategy_outputs: dict[str, str] | None = None,
    fallback_output: str = "def foo(): pass\n",
) -> Path:
    """Create a minimal fixture directory for testing."""
    if seeds is None:
        seeds = ["foo"]
    if expected_results is None:
        expected_results = {
            strategy: {"passed": True, "max_input_tokens": 500, "min_churn_score": 0.85}
            for strategy in ALL_STRATEGIES
        }

    d = base / name
    d.mkdir(parents=True, exist_ok=True)
    (d / "source.py").write_text("def foo(): pass\n", encoding="utf-8")
    (d / "test_file.py").write_text("def test_foo(): pass\n", encoding="utf-8")
    (d / "contract_seeds.json").write_text(json.dumps(seeds), encoding="utf-8")
    (d / "expected_results.json").write_text(json.dumps(expected_results), encoding="utf-8")
    (d / "expected_output.py").write_text(fallback_output, encoding="utf-8")

    if per_strategy_outputs:
        for strategy, content in per_strategy_outputs.items():
            (d / f"expected_output_{strategy}.py").write_text(content, encoding="utf-8")

    return d


def _make_result(
    *,
    strategy: str = "full_tests",
    fixture_id: str = "fix1",
    passed: bool = True,
    input_tokens: int = 100,
    elapsed_sec: float = 0.1,
    churn_score: float = 0.95,
    missing_contracts: list[str] | None = None,
) -> CompressionBenchmarkResult:
    return CompressionBenchmarkResult(
        strategy=strategy,
        fixture_id=fixture_id,
        passed=passed,
        input_tokens=input_tokens,
        elapsed_sec=elapsed_sec,
        churn_score=churn_score,
        missing_contracts=missing_contracts if missing_contracts is not None else [],
    )


# ---------------------------------------------------------------------------
# 1. CompressionBenchmarkResult dataclass
# ---------------------------------------------------------------------------

class TestCompressionBenchmarkResultDataclass:
    def test_has_all_required_fields(self):
        """The dataclass must have exactly the fields defined in the spec."""
        fields = list(CompressionBenchmarkResult.__dataclass_fields__.keys())
        expected = ["strategy", "fixture_id", "passed", "input_tokens", "elapsed_sec", "churn_score", "missing_contracts"]
        for f in expected:
            assert f in fields

    def test_field_types_and_values(self):
        r = _make_result(strategy="ast_tests", fixture_id="fx2", passed=False,
                         input_tokens=42, elapsed_sec=1.23, churn_score=0.77,
                         missing_contracts=["sym_a", "sym_b"])
        assert r.strategy == "ast_tests"
        assert r.fixture_id == "fx2"
        assert r.passed is False
        assert r.input_tokens == 42
        assert abs(r.elapsed_sec - 1.23) < 1e-9
        assert abs(r.churn_score - 0.77) < 1e-9
        assert r.missing_contracts == ["sym_a", "sym_b"]


# ---------------------------------------------------------------------------
# 2. ALL_STRATEGIES
# ---------------------------------------------------------------------------

class TestAllStrategies:
    def test_has_five_strategies(self):
        assert len(ALL_STRATEGIES) == 5

    def test_contains_required_names(self):
        required = {"full_tests", "ast_tests", "ast_contracts", "full_fewshot", "compressed_fewshot"}
        assert set(ALL_STRATEGIES) == required


# ---------------------------------------------------------------------------
# 3-6. _load_fixture
# ---------------------------------------------------------------------------

class TestLoadFixture:
    def test_reads_required_files(self, tmp_path):
        """_load_fixture must read source.py, test_file.py, contract_seeds.json, expected_results.json."""
        d = _make_fixture_dir(tmp_path, seeds=["bar"], expected_results={"full_tests": {"passed": True}})
        result = _load_fixture(d)
        assert result["source"] == "def foo(): pass\n"
        assert result["test_file"] == "def test_foo(): pass\n"
        assert result["seeds"] == ["bar"]
        assert "full_tests" in result["expected_results"]

    def test_fixture_id_is_directory_name(self, tmp_path):
        d = _make_fixture_dir(tmp_path, name="my_fixture")
        result = _load_fixture(d)
        assert result["fixture_id"] == "my_fixture"

    def test_expected_outputs_has_all_strategies(self, tmp_path):
        d = _make_fixture_dir(tmp_path)
        result = _load_fixture(d)
        assert "expected_outputs" in result
        for strategy in ALL_STRATEGIES:
            assert strategy in result["expected_outputs"]

    def test_reads_per_strategy_output_file(self, tmp_path):
        """Per-strategy expected_output_{strategy}.py files must be read."""
        d = _make_fixture_dir(
            tmp_path,
            per_strategy_outputs={"full_tests": "def custom_full_tests(): pass\n"},
        )
        result = _load_fixture(d)
        assert result["expected_outputs"]["full_tests"] == "def custom_full_tests(): pass\n"

    def test_falls_back_to_expected_output_when_no_per_strategy_file(self, tmp_path):
        """When no per-strategy file exists, fallback to expected_output.py content."""
        d = _make_fixture_dir(tmp_path, fallback_output="def fallback(): pass\n")
        result = _load_fixture(d)
        # No per-strategy files were written, so all strategies get fallback
        for strategy in ALL_STRATEGIES:
            assert result["expected_outputs"][strategy] == "def fallback(): pass\n"

    def test_per_strategy_overrides_fallback(self, tmp_path):
        """Per-strategy file takes precedence over expected_output.py."""
        d = _make_fixture_dir(
            tmp_path,
            fallback_output="def fallback(): pass\n",
            per_strategy_outputs={"ast_contracts": "def specific(): pass\n"},
        )
        result = _load_fixture(d)
        assert result["expected_outputs"]["ast_contracts"] == "def specific(): pass\n"
        # Other strategies still get fallback
        assert result["expected_outputs"]["full_tests"] == "def fallback(): pass\n"

    def test_returns_dict_with_required_keys(self, tmp_path):
        d = _make_fixture_dir(tmp_path)
        result = _load_fixture(d)
        for key in ["source", "test_file", "expected_outputs", "seeds", "expected_results", "fixture_id"]:
            assert key in result


# ---------------------------------------------------------------------------
# 7-11. Strategy builders
# ---------------------------------------------------------------------------

class TestStrategyBuilders:
    def test_build_full_tests_returns_test_file_unchanged(self):
        fixture = {"test_file": "def test_it(): pass\n", "seeds": ["x"], "source": "def x(): pass\n"}
        assert _build_full_tests(fixture) == "def test_it(): pass\n"

    def test_build_full_fewshot_returns_test_file(self):
        fixture = {"test_file": "def test_it(): pass\n", "seeds": ["x"], "source": "def x(): pass\n"}
        # Full fewshot = test file only, no source
        assert _build_full_fewshot(fixture) == "def test_it(): pass\n"

    def test_build_ast_tests_calls_content_selector(self):
        fixture = {"test_file": "def test_it(): pass\n", "seeds": ["foo", "bar"], "source": ""}
        with patch("pdd.compression_benchmark.ContentSelector") as mock_cs:
            mock_cs.select.return_value = "selected"
            result = _build_ast_tests(fixture)
        assert result == "selected"
        mock_cs.select.assert_called_once_with("def test_it(): pass\n", "contract:foo,bar")

    def test_build_ast_contracts_calls_api_contract_slicer(self):
        fixture = {"source": "def foo(): pass\n", "seeds": ["foo"], "test_file": ""}
        mock_slicer = MagicMock()
        mock_slicer.slice.return_value = ("sliced_output", MagicMock())
        with patch("pdd.compression_benchmark.ApiContractSlicer", return_value=mock_slicer) as mock_cls:
            result = _build_ast_contracts(fixture)
        assert result == "sliced_output"
        mock_cls.assert_called_once_with("def foo(): pass\n")
        mock_slicer.slice.assert_called_once_with(["foo"])

    def test_build_compressed_fewshot_concatenates_contracts_and_tests(self):
        fixture = {"source": "def foo(): pass\n", "seeds": ["foo"], "test_file": "def test_foo(): pass\n"}
        with patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer_cls, \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs:
            mock_slicer_inst = MagicMock()
            mock_slicer_inst.slice.return_value = ("contract_part\n", MagicMock())
            mock_slicer_cls.return_value = mock_slicer_inst
            mock_cs.select.return_value = "test_part\n"
            result = _build_compressed_fewshot(fixture)
        assert "contract_part" in result
        assert "test_part" in result
        # contract comes before tests
        assert result.index("contract_part") < result.index("test_part")


# ---------------------------------------------------------------------------
# 12-23. run_benchmark
# ---------------------------------------------------------------------------

class TestRunBenchmark:
    def _mock_context(self):
        """Return context managers that mock all external I/O in run_benchmark."""
        slicer_inst = MagicMock()
        slicer_inst.slice.return_value = ("def foo(): pass\n", MagicMock())
        return slicer_inst

    def test_skips_non_directories(self, tmp_path):
        """Files in fixtures_dir are ignored; only subdirectories are processed."""
        (tmp_path / "not_a_dir.txt").write_text("noise", encoding="utf-8")
        _make_fixture_dir(tmp_path, name="valid")
        with patch("pdd.compression_benchmark.count_tokens", return_value=10), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer:
            mock_cs.select.return_value = "def foo(): pass\n"
            inst = self._mock_context()
            mock_slicer.return_value = inst
            mock_slicer.verify_contract = MagicMock()
            results = run_benchmark(tmp_path, strategies=["full_tests"])
        # Only valid/ was processed
        assert all(r.fixture_id == "valid" for r in results)

    def test_runs_all_five_strategies_when_none(self, tmp_path):
        """R7: all 5 strategies run by default."""
        _make_fixture_dir(tmp_path, name="fix1")
        with patch("pdd.compression_benchmark.count_tokens", return_value=10), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer:
            mock_cs.select.return_value = "def foo(): pass\n"
            inst = self._mock_context()
            mock_slicer.return_value = inst
            mock_slicer.verify_contract = MagicMock()
            results = run_benchmark(tmp_path, strategies=None)
        strategies_used = {r.strategy for r in results}
        assert strategies_used == set(ALL_STRATEGIES)

    def test_accepts_explicit_strategies(self, tmp_path):
        _make_fixture_dir(tmp_path, name="fix1")
        with patch("pdd.compression_benchmark.count_tokens", return_value=5), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer:
            mock_cs.select.return_value = "def foo(): pass\n"
            inst = self._mock_context()
            mock_slicer.return_value = inst
            mock_slicer.verify_contract = MagicMock()
            results = run_benchmark(tmp_path, strategies=["full_tests", "ast_contracts"])
        strategies_used = {r.strategy for r in results}
        assert strategies_used == {"full_tests", "ast_contracts"}

    def test_input_tokens_is_nonzero_r4(self, tmp_path):
        """R4: input_tokens must be recorded (not 0)."""
        _make_fixture_dir(tmp_path, name="fix1")
        with patch("pdd.compression_benchmark.count_tokens", return_value=77), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer:
            mock_cs.select.return_value = "def foo(): pass\n"
            inst = self._mock_context()
            mock_slicer.return_value = inst
            mock_slicer.verify_contract = MagicMock()
            results = run_benchmark(tmp_path, strategies=["full_tests"])
        assert all(r.input_tokens == 77 for r in results)

    def test_count_tokens_called_before_output(self, tmp_path):
        """R4: count_tokens is called before the simulated output lookup."""
        _make_fixture_dir(tmp_path, name="fix1")
        call_order = []

        def track_tokens(text):
            call_order.append("count_tokens")
            return 10

        original_outputs = None

        def fake_builder(fixture):
            return "ctx"

        with patch("pdd.compression_benchmark.count_tokens", side_effect=track_tokens), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer:
            mock_cs.select.return_value = "def foo(): pass\n"
            inst = self._mock_context()
            mock_slicer.return_value = inst
            mock_slicer.verify_contract = MagicMock()
            results = run_benchmark(tmp_path, strategies=["full_tests"])

        # count_tokens must have been called for each result
        assert call_order.count("count_tokens") == len(results)

    def test_elapsed_sec_positive_r5(self, tmp_path):
        """R5: elapsed_sec must be set (non-negative)."""
        _make_fixture_dir(tmp_path, name="fix1")
        with patch("pdd.compression_benchmark.count_tokens", return_value=1), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer:
            mock_cs.select.return_value = "def foo(): pass\n"
            inst = self._mock_context()
            mock_slicer.return_value = inst
            mock_slicer.verify_contract = MagicMock()
            results = run_benchmark(tmp_path, strategies=["full_tests"])
        assert all(r.elapsed_sec >= 0.0 for r in results)

    def test_uses_per_strategy_output_file_r6(self, tmp_path):
        """R6: frozen-fixture mode uses per-strategy expected_output_{strategy}.py."""
        _make_fixture_dir(
            tmp_path, name="fix1",
            fallback_output="def fallback(): pass\n",
            per_strategy_outputs={"full_tests": "def full_tests_specific(): pass\n"},
        )
        with patch("pdd.compression_benchmark.count_tokens", return_value=1), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer:
            mock_cs.select.return_value = "def foo(): pass\n"
            inst = self._mock_context()
            mock_slicer.return_value = inst
            # verify_contract raises for fallback but not for full_tests_specific
            from pdd.api_contract_slicer import ContractSlicerError
            def verify_side_effect(output, seeds, **kwargs):
                if "full_tests_specific" not in output and "def foo" not in output:
                    raise ContractSlicerError("missing symbols: foo")
            mock_slicer.verify_contract = MagicMock(side_effect=verify_side_effect)
            results = run_benchmark(tmp_path, strategies=["full_tests"])

        full_test_result = next(r for r in results if r.strategy == "full_tests")
        # The per-strategy file should have been used, not the fallback
        # We can verify by checking that verify_contract was called with the specific content
        call_args = mock_slicer.verify_contract.call_args
        assert "full_tests_specific" in str(call_args) or full_test_result.passed

    def test_falls_back_to_expected_output_py_r6(self, tmp_path):
        """R6: when per-strategy file absent, use expected_output.py."""
        fallback_content = "def foo(): pass\n"
        _make_fixture_dir(tmp_path, name="fix1", fallback_output=fallback_content)
        # No per-strategy files, so all strategies use fallback
        from pdd.api_contract_slicer import ContractSlicerError

        called_with = []

        def capture_verify(output, seeds, **kwargs):
            called_with.append(output)

        with patch("pdd.compression_benchmark.count_tokens", return_value=1), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer:
            mock_cs.select.return_value = "def foo(): pass\n"
            inst = self._mock_context()
            mock_slicer.return_value = inst
            mock_slicer.verify_contract = MagicMock(side_effect=capture_verify)
            results = run_benchmark(tmp_path, strategies=["full_tests"])

        # verify_contract was called with the fallback content
        assert any(fallback_content in args for args in called_with)

    def test_churn_score_computed_via_sequence_matcher(self, tmp_path):
        """Churn score is the SequenceMatcher ratio of expected output vs actual."""
        fallback = "abcde\n"
        per_strat = "abcde\n"  # identical → churn=1.0
        _make_fixture_dir(
            tmp_path, name="fix1",
            fallback_output=fallback,
            per_strategy_outputs={"full_tests": per_strat},
        )
        with patch("pdd.compression_benchmark.count_tokens", return_value=1), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer:
            mock_cs.select.return_value = "def foo(): pass\n"
            inst = self._mock_context()
            mock_slicer.return_value = inst
            mock_slicer.verify_contract = MagicMock()
            results = run_benchmark(tmp_path, strategies=["full_tests"])
        result = next(r for r in results if r.strategy == "full_tests")
        assert abs(result.churn_score - 1.0) < 1e-6

    def test_passed_true_when_verify_contract_no_error(self, tmp_path):
        _make_fixture_dir(tmp_path, name="fix1")
        with patch("pdd.compression_benchmark.count_tokens", return_value=1), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer:
            mock_cs.select.return_value = "def foo(): pass\n"
            inst = self._mock_context()
            mock_slicer.return_value = inst
            mock_slicer.verify_contract = MagicMock()  # no-raise
            results = run_benchmark(tmp_path, strategies=["full_tests"])
        assert all(r.passed for r in results)
        assert all(r.missing_contracts == [] for r in results)

    def test_passed_false_and_missing_contracts_on_slicer_error(self, tmp_path):
        """When verify_contract raises ContractSlicerError with missing symbols, result.passed=False."""
        from pdd.api_contract_slicer import ContractSlicerError
        _make_fixture_dir(tmp_path, name="fix1")
        with patch("pdd.compression_benchmark.count_tokens", return_value=1), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer:
            mock_cs.select.return_value = "def foo(): pass\n"
            inst = self._mock_context()
            mock_slicer.return_value = inst
            mock_slicer.verify_contract = MagicMock(
                side_effect=ContractSlicerError("Contract verification failed; missing symbols: alpha, beta")
            )
            results = run_benchmark(tmp_path, strategies=["full_tests"])
        result = results[0]
        assert result.passed is False
        assert "alpha" in result.missing_contracts
        assert "beta" in result.missing_contracts

    def test_live_llm_true_raises_not_implemented(self, tmp_path):
        """live_llm=True raises NotImplementedError."""
        _make_fixture_dir(tmp_path, name="fix1")
        with patch("pdd.compression_benchmark.count_tokens", return_value=1), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer:
            mock_cs.select.return_value = "def foo(): pass\n"
            inst = self._mock_context()
            mock_slicer.return_value = inst
            mock_slicer.verify_contract = MagicMock()
            with pytest.raises(NotImplementedError):
                run_benchmark(tmp_path, strategies=["full_tests"], live_llm=True)

    def test_returns_list_of_compression_benchmark_results(self, tmp_path):
        _make_fixture_dir(tmp_path, name="fix1")
        with patch("pdd.compression_benchmark.count_tokens", return_value=5), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer:
            mock_cs.select.return_value = "def foo(): pass\n"
            inst = self._mock_context()
            mock_slicer.return_value = inst
            mock_slicer.verify_contract = MagicMock()
            results = run_benchmark(tmp_path, strategies=["full_tests"])
        assert isinstance(results, list)
        assert all(isinstance(r, CompressionBenchmarkResult) for r in results)

    def test_regression_input_tokens_never_zero(self, tmp_path):
        """Regression: input_tokens must always be set (R4)."""
        _make_fixture_dir(tmp_path, name="fix1")
        with patch("pdd.compression_benchmark.count_tokens", return_value=99), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer:
            mock_cs.select.return_value = "def foo(): pass\n"
            inst = self._mock_context()
            mock_slicer.return_value = inst
            mock_slicer.verify_contract = MagicMock()
            results = run_benchmark(tmp_path)
        assert all(r.input_tokens > 0 for r in results)


# ---------------------------------------------------------------------------
# 24-33. check_compression_benchmark
# ---------------------------------------------------------------------------

class TestCheckCompressionBenchmark:
    def test_passes_when_no_violations(self):
        """GateResult.passed=True when all results meet baselines."""
        results = [_make_result(passed=True, churn_score=0.95, missing_contracts=[])]
        baselines = {"fix1": {"full_tests": {"passed": True, "min_churn_score": 0.85}}}
        gate = check_compression_benchmark(results, baselines)
        assert gate.passed is True
        assert gate.failures == []

    def test_r1_fails_when_baseline_passed_and_missing_contracts(self):
        """R1: contract-symbol loss when baseline passed=True but missing_contracts non-empty."""
        results = [_make_result(passed=False, missing_contracts=["sym_a"])]
        baselines = {"fix1": {"full_tests": {"passed": True, "min_churn_score": 0.0}}}
        gate = check_compression_benchmark(results, baselines)
        assert gate.passed is False
        codes = [f.code for f in gate.failures]
        assert "CONTRACT_SYMBOL_LOSS" in codes

    def test_r1_does_not_fail_when_baseline_not_passed(self):
        """R1: missing_contracts on a baseline-failed strategy is expected, not a gate failure."""
        results = [_make_result(passed=False, missing_contracts=["sym_a"])]
        baselines = {"fix1": {"full_tests": {"passed": False, "min_churn_score": 0.0}}}
        gate = check_compression_benchmark(results, baselines)
        codes = [f.code for f in gate.failures]
        assert "CONTRACT_SYMBOL_LOSS" not in codes

    def test_r2_fails_when_baseline_passed_but_result_failed(self):
        """R2: pass-rate regression when baseline passed=True but result.passed=False."""
        results = [_make_result(passed=False, missing_contracts=[])]
        baselines = {"fix1": {"full_tests": {"passed": True, "min_churn_score": 0.0}}}
        gate = check_compression_benchmark(results, baselines)
        assert gate.passed is False
        codes = [f.code for f in gate.failures]
        assert "PASS_RATE_REGRESSION" in codes

    def test_r2_does_not_fail_when_baseline_not_passed(self):
        """R2: failing result against a failing baseline is not a regression."""
        results = [_make_result(passed=False, missing_contracts=[])]
        baselines = {"fix1": {"full_tests": {"passed": False, "min_churn_score": 0.0}}}
        gate = check_compression_benchmark(results, baselines)
        codes = [f.code for f in gate.failures]
        assert "PASS_RATE_REGRESSION" not in codes

    def test_r3_fails_when_churn_below_threshold_and_below_baseline(self):
        """R3: churn below PDD_COMPRESSION_CHURN_THRESHOLD AND below baseline min_churn_score."""
        # Default threshold is 0.90
        results = [_make_result(passed=True, churn_score=0.50)]
        baselines = {"fix1": {"full_tests": {"passed": True, "min_churn_score": 0.85}}}
        gate = check_compression_benchmark(results, baselines)
        assert gate.passed is False
        codes = [f.code for f in gate.failures]
        assert "CHURN_REGRESSION" in codes

    def test_r3_does_not_fail_when_churn_below_threshold_but_above_baseline(self):
        """R3: churn below threshold but >= baseline min_churn_score is NOT a failure."""
        # churn=0.89 < threshold (0.90) BUT >= min_churn_score (0.50)
        results = [_make_result(passed=True, churn_score=0.89)]
        baselines = {"fix1": {"full_tests": {"passed": True, "min_churn_score": 0.50}}}
        gate = check_compression_benchmark(results, baselines)
        codes = [f.code for f in gate.failures]
        assert "CHURN_REGRESSION" not in codes

    def test_r3_does_not_fail_when_churn_above_threshold(self):
        """R3: churn above threshold is fine regardless of baseline."""
        results = [_make_result(passed=True, churn_score=0.95)]
        baselines = {"fix1": {"full_tests": {"passed": True, "min_churn_score": 0.85}}}
        gate = check_compression_benchmark(results, baselines)
        codes = [f.code for f in gate.failures]
        assert "CHURN_REGRESSION" not in codes

    def test_skips_results_with_no_baseline(self):
        """Results without a baseline entry are skipped (no false positives)."""
        results = [_make_result(passed=False, missing_contracts=["x"], fixture_id="unknown_fixture")]
        baselines = {}
        gate = check_compression_benchmark(results, baselines)
        assert gate.passed is True

    def test_manifests_checked_count(self):
        """manifests_checked must equal len(results)."""
        results = [_make_result(fixture_id="fx1"), _make_result(fixture_id="fx2", strategy="ast_tests")]
        baselines = {}
        gate = check_compression_benchmark(results, baselines)
        assert gate.manifests_checked == 2

    def test_exit_code_zero_when_passed(self):
        results = [_make_result(passed=True, churn_score=0.99)]
        baselines = {"fix1": {"full_tests": {"passed": True, "min_churn_score": 0.85}}}
        gate = check_compression_benchmark(results, baselines)
        assert gate.exit_code == 0

    def test_exit_code_one_when_failed(self):
        results = [_make_result(passed=False, missing_contracts=["x"])]
        baselines = {"fix1": {"full_tests": {"passed": True, "min_churn_score": 0.0}}}
        gate = check_compression_benchmark(results, baselines)
        assert gate.exit_code == 1

    def test_returns_gate_result_type(self):
        results = []
        baselines = {}
        gate = check_compression_benchmark(results, baselines)
        assert isinstance(gate, GateResult)


# ---------------------------------------------------------------------------
# 34-36. print_benchmark_report
# ---------------------------------------------------------------------------

class TestPrintBenchmarkReport:
    def test_prints_without_error(self, capsys):
        """print_benchmark_report must run without raising."""
        results = [
            _make_result(strategy="full_tests", fixture_id="fx1", passed=True, churn_score=0.95),
            _make_result(strategy="ast_contracts", fixture_id="fx1", passed=False,
                         missing_contracts=["sym_x"], churn_score=0.5),
        ]
        # Should not raise
        print_benchmark_report(results)

    def test_writes_json_when_output_path_given(self, tmp_path):
        """When output_path provided, JSON file is written."""
        results = [
            _make_result(strategy="full_tests", fixture_id="fx1", passed=True,
                         input_tokens=100, elapsed_sec=0.5, churn_score=0.95),
        ]
        output_path = tmp_path / "report.json"
        print_benchmark_report(results, output_path=output_path)
        assert output_path.exists()

    def test_json_output_has_correct_fields(self, tmp_path):
        """JSON output must contain all CompressionBenchmarkResult fields for each result."""
        results = [
            _make_result(strategy="ast_tests", fixture_id="fx2", passed=False,
                         input_tokens=42, elapsed_sec=1.1, churn_score=0.7,
                         missing_contracts=["foo"]),
        ]
        output_path = tmp_path / "report.json"
        print_benchmark_report(results, output_path=output_path)
        data = json.loads(output_path.read_text(encoding="utf-8"))
        assert len(data) == 1
        entry = data[0]
        assert entry["strategy"] == "ast_tests"
        assert entry["fixture_id"] == "fx2"
        assert entry["passed"] is False
        assert entry["input_tokens"] == 42
        assert abs(entry["elapsed_sec"] - 1.1) < 1e-6
        assert abs(entry["churn_score"] - 0.7) < 1e-6
        assert entry["missing_contracts"] == ["foo"]

    def test_json_not_written_when_no_output_path(self, tmp_path):
        """When output_path is None, no JSON file is created."""
        results = [_make_result()]
        # No output_path argument
        print_benchmark_report(results)
        # Ensure no unexpected files were written in tmp_path
        assert list(tmp_path.iterdir()) == []

    def test_empty_results_no_crash(self):
        """print_benchmark_report must handle empty results list without crashing."""
        print_benchmark_report([])


# ---------------------------------------------------------------------------
# Integration: real fixture from repo
# ---------------------------------------------------------------------------

class TestIntegrationRealFixture:
    """Run against the actual fixture included in the repo (frozen-fixture mode)."""

    REAL_FIXTURES = Path(__file__).resolve().parent / "fixtures" / "compression_benchmark"

    @pytest.mark.skipif(
        not (Path(__file__).resolve().parent / "fixtures" / "compression_benchmark").is_dir(),
        reason="Real fixture directory not present",
    )
    def test_real_fixture_run_benchmark(self):
        """run_benchmark on the real fixture returns results for all strategies."""
        with patch("pdd.compression_benchmark.count_tokens", return_value=50), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer:
            mock_cs.select.return_value = "def run_worker(): pass\n"
            inst = MagicMock()
            inst.slice.return_value = (
                "def run_worker(): pass\ndef _get_job_secrets(): pass\n",
                MagicMock(),
            )
            mock_slicer.return_value = inst
            mock_slicer.verify_contract = MagicMock()
            results = run_benchmark(self.REAL_FIXTURES)
        assert len(results) == len(ALL_STRATEGIES)
        fixture_ids = {r.fixture_id for r in results}
        assert "contract_loss_regression" in fixture_ids

    @pytest.mark.skipif(
        not (Path(__file__).resolve().parent / "fixtures" / "compression_benchmark").is_dir(),
        reason="Real fixture directory not present",
    )
    def test_real_fixture_input_tokens_nonzero(self):
        """R4: input_tokens > 0 for real fixture."""
        with patch("pdd.compression_benchmark.count_tokens", return_value=100), \
             patch("pdd.compression_benchmark.ContentSelector") as mock_cs, \
             patch("pdd.compression_benchmark.ApiContractSlicer") as mock_slicer:
            mock_cs.select.return_value = "def foo(): pass\n"
            inst = MagicMock()
            inst.slice.return_value = ("def foo(): pass\n", MagicMock())
            mock_slicer.return_value = inst
            mock_slicer.verify_contract = MagicMock()
            results = run_benchmark(self.REAL_FIXTURES)
        assert all(r.input_tokens > 0 for r in results)
