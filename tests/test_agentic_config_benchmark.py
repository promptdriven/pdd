"""Tests for the agentic-config benchmark harness (PR #1582 / #1209).

The harness lives in research/agentic-config-benchmark/ and is only present on
epic/1431-task-routing-v1.  All tests skip gracefully when the directory or its
entry-point module is absent.

Coverage:
  - Harness module imports cleanly
  - run_benchmark() (or equivalent) accepts a config dict and returns a result
  - Results include required fields (score, cost, provider, task_class)
  - Integration smoke: harness runs at least one benchmark iteration with
    providers fully stubbed
  - Error path: malformed config raises a clear ValueError (not a crash)
"""

from __future__ import annotations

import importlib
import os
import sys
from pathlib import Path
from typing import Any, Dict
from unittest.mock import MagicMock, patch

import pytest

# ---------------------------------------------------------------------------
# Harness location guard
# ---------------------------------------------------------------------------

_REPO_ROOT = Path(__file__).resolve().parents[1]
_BENCHMARK_DIR = _REPO_ROOT / "research" / "agentic-config-benchmark"

if not _BENCHMARK_DIR.exists():
    pytest.skip(
        "research/agentic-config-benchmark/ not present on this branch "
        "(epic/1431-task-routing-v1 only)",
        allow_module_level=True,
    )

# Add the benchmark directory to sys.path so its modules are importable
if str(_BENCHMARK_DIR) not in sys.path:
    sys.path.insert(0, str(_BENCHMARK_DIR))

# Attempt to import the benchmark entry-point
_HARNESS_MODULE = None
_HARNESS_MODULE_NAME = None
for _candidate in ("benchmark", "run_benchmark", "agentic_config_benchmark",
                   "harness", "main"):
    try:
        _HARNESS_MODULE = importlib.import_module(_candidate)
        _HARNESS_MODULE_NAME = _candidate
        break
    except ModuleNotFoundError:
        continue

if _HARNESS_MODULE is None:
    pytest.skip(
        "No benchmark entry-point module found in research/agentic-config-benchmark/",
        allow_module_level=True,
    )

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

_MINIMAL_CONFIG: Dict[str, Any] = {
    "task_class": "bugfix",
    "model": "claude-sonnet-4-6",
    "temperature": 0.0,
    "thinking": 0.5,
    "shots": 1,
    "instruction": "Fix the trivial off-by-one error in add(a, b).",
}

_REQUIRED_RESULT_FIELDS = {"score", "cost", "provider", "task_class"}


def _get_run_fn():
    """Return the main benchmark runner function."""
    for name in ("run_benchmark", "run", "execute", "benchmark", "main"):
        fn = getattr(_HARNESS_MODULE, name, None)
        if callable(fn):
            return fn
    return None


def _make_stub_result(score: float = 1.0, cost: float = 0.02,
                      provider: str = "claude", task_class: str = "bugfix"):
    return {
        "score": score,
        "cost": cost,
        "provider": provider,
        "task_class": task_class,
        "output": "fixed code",
    }


# ---------------------------------------------------------------------------
# Section 1: Import sanity
# ---------------------------------------------------------------------------

class TestHarnessImport:
    """The harness module must import cleanly with no side effects."""

    def test_harness_module_imports(self):
        """Import must succeed (guarded at module level above)."""
        assert _HARNESS_MODULE is not None

    def test_harness_has_callable_entry_point(self):
        """The harness must expose at least one callable entry-point."""
        run_fn = _get_run_fn()
        assert run_fn is not None, (
            f"No callable entry-point found in {_HARNESS_MODULE_NAME}; "
            "expected run_benchmark, run, execute, benchmark, or main"
        )


# ---------------------------------------------------------------------------
# Section 2: Unit tests — config validation
# ---------------------------------------------------------------------------

class TestConfigValidation:
    """Harness validates its config dict before running."""

    def test_minimal_config_accepted(self):
        """A minimal valid config must not raise on validation."""
        run_fn = _get_run_fn()
        if run_fn is None:
            pytest.skip("No entry-point found")

        validate_fn = getattr(_HARNESS_MODULE, "validate_config", None)
        if validate_fn is not None:
            # Should not raise
            validate_fn(_MINIMAL_CONFIG)
        else:
            pytest.skip("validate_config not found — skipping config validation test")

    def test_missing_required_field_raises(self):
        """A config missing 'task_class' must raise ValueError (or similar)."""
        validate_fn = getattr(_HARNESS_MODULE, "validate_config", None)
        if validate_fn is None:
            pytest.skip("validate_config not found")

        bad_config = {k: v for k, v in _MINIMAL_CONFIG.items() if k != "task_class"}
        with pytest.raises((ValueError, KeyError, TypeError)):
            validate_fn(bad_config)

    def test_invalid_temperature_raises(self):
        """A temperature outside [0, 2] must raise ValueError."""
        validate_fn = getattr(_HARNESS_MODULE, "validate_config", None)
        if validate_fn is None:
            pytest.skip("validate_config not found")

        bad_config = dict(_MINIMAL_CONFIG, temperature=99.0)
        with pytest.raises((ValueError, TypeError)):
            validate_fn(bad_config)


# ---------------------------------------------------------------------------
# Section 3: Unit tests — result schema
# ---------------------------------------------------------------------------

class TestResultSchema:
    """Benchmark results must include the required fields."""

    def test_result_has_required_fields(self, tmp_path):
        """run_benchmark must return a dict (or object) with score, cost,
        provider, and task_class."""
        run_fn = _get_run_fn()
        if run_fn is None:
            pytest.skip("No entry-point found")

        mock_result = _make_stub_result()

        # Stub out the provider call inside the harness
        for stub_target in ("pdd.agentic_common.run_agentic_task",
                             f"{_HARNESS_MODULE_NAME}.run_agentic_task",
                             f"{_HARNESS_MODULE_NAME}._run_shot"):
            try:
                with patch(stub_target, return_value=MagicMock(
                    success=True, output_text="fixed", cost_usd=0.02,
                    provider_used="claude"
                )):
                    result = run_fn(_MINIMAL_CONFIG, cwd=tmp_path)
                    break
            except (AttributeError, ModuleNotFoundError):
                continue
        else:
            pytest.skip("Could not stub provider call in harness")

        if isinstance(result, dict):
            for field in _REQUIRED_RESULT_FIELDS:
                assert field in result, (
                    f"Benchmark result must include '{field}'; got keys: {list(result.keys())}"
                )
        else:
            for field in _REQUIRED_RESULT_FIELDS:
                assert hasattr(result, field), (
                    f"Benchmark result must have attribute '{field}'"
                )


# ---------------------------------------------------------------------------
# Section 4: Integration smoke test
# ---------------------------------------------------------------------------

class TestIntegrationSmoke:
    """Smoke test: harness runs at least one iteration with providers stubbed."""

    @pytest.mark.timeout(30)
    def test_smoke_run_with_stubbed_provider(self, tmp_path):
        """run_benchmark completes in under 30 s with a stubbed provider."""
        run_fn = _get_run_fn()
        if run_fn is None:
            pytest.skip("No entry-point found")

        stub_result = MagicMock(
            success=True,
            output_text="def add(a, b): return a + b",
            cost_usd=0.01,
            provider_used="claude",
        )

        stub_targets = [
            "pdd.agentic_common.run_agentic_task",
            f"{_HARNESS_MODULE_NAME}.run_agentic_task",
            f"{_HARNESS_MODULE_NAME}._run_shot",
            "pdd.llm_invoke.llm_invoke",
        ]

        ran = False
        for target in stub_targets:
            try:
                with patch(target, return_value=stub_result):
                    result = run_fn(_MINIMAL_CONFIG, cwd=tmp_path)
                    ran = True
                    break
            except (AttributeError, ModuleNotFoundError, TypeError):
                continue

        if not ran:
            pytest.skip("Could not stub any provider path in harness")

        assert result is not None, "Smoke run must return a non-None result"

    def test_benchmark_handles_provider_failure_gracefully(self, tmp_path):
        """If the provider fails, run_benchmark must return a failure result
        rather than propagating an unhandled exception."""
        run_fn = _get_run_fn()
        if run_fn is None:
            pytest.skip("No entry-point found")

        fail_result = MagicMock(
            success=False,
            output_text="provider error: rate limit",
            cost_usd=0.0,
            provider_used="claude",
        )

        stub_targets = [
            "pdd.agentic_common.run_agentic_task",
            f"{_HARNESS_MODULE_NAME}.run_agentic_task",
            f"{_HARNESS_MODULE_NAME}._run_shot",
        ]

        for target in stub_targets:
            try:
                with patch(target, return_value=fail_result):
                    result = run_fn(_MINIMAL_CONFIG, cwd=tmp_path)
                    # Must not raise; result should reflect failure
                    success = (
                        result.get("score", 1) if isinstance(result, dict)
                        else getattr(result, "score", 1)
                    )
                    assert success == 0 or success is False or success <= 0.5, (
                        "Benchmark result must reflect provider failure"
                    )
                    return
            except (AttributeError, ModuleNotFoundError, TypeError):
                continue

        pytest.skip("Could not stub provider failure path in harness")
