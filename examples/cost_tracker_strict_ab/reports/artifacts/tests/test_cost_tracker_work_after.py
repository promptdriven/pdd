

# pdd:sys.path-preamble
import sys
from pathlib import Path

# Add project root and src/ so ``import foo_work`` works when code lives under src/
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))
_src_dir = project_root / "src"
if _src_dir.is_dir() and str(_src_dir) not in sys.path:
    sys.path.insert(0, str(_src_dir))

import sys
from pathlib import Path

# This allows testing local changes without installing the package

import sys
import math
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent
SRC = ROOT / "src"

from edit_file_tool.cost_tracker_utility import (  # noqa: E402
    calculate_cost,
    calculate_cost_breakdown,
    MODEL_PRICING,
)


# ---------------------------------------------------------------------------
# R3: Cost formula correctness
# ---------------------------------------------------------------------------
def _expected_cost(model_family, ti, to, tcw, tcr):
    rates = MODEL_PRICING[model_family]
    ir = rates["input_per_mtok"] / 1_000_000.0
    or_ = rates["output_per_mtok"] / 1_000_000.0
    return ti * ir + to * or_ + tcw * ir * 1.25 + tcr * ir * 0.10


def test_zero_tokens_returns_zero():
    assert calculate_cost("claude-3-opus", 0, 0, 0, 0) == 0.0


def test_simple_input_only_haiku_one_million():
    # 1M input tokens at $0.80 per 1M -> $0.80
    cost = calculate_cost("claude-3-5-haiku-20241022", input_tokens=1_000_000, output_tokens=0)
    expected = MODEL_PRICING["claude-3-5-haiku"]["input_per_mtok"]
    assert math.isclose(cost, expected, rel_tol=1e-12, abs_tol=1e-15)


def test_simple_output_only_opus_one_million():
    cost = calculate_cost("claude-3-opus", input_tokens=0, output_tokens=1_000_000)
    expected = MODEL_PRICING["claude-3-opus"]["output_per_mtok"]
    assert math.isclose(cost, expected, rel_tol=1e-12, abs_tol=1e-15)


def test_cache_write_uses_125_percent_of_input_rate():
    # Pure cache write: cost = tokens * input_rate * 1.25
    cost = calculate_cost("claude-3-haiku", 0, 0, cache_write_tokens=1_000_000)
    expected = MODEL_PRICING["claude-3-haiku"]["input_per_mtok"] * 1.25
    assert math.isclose(cost, expected, rel_tol=1e-12, abs_tol=1e-15)


def test_cache_read_uses_10_percent_of_input_rate():
    cost = calculate_cost("claude-3-haiku", 0, 0, cache_read_tokens=1_000_000)
    expected = MODEL_PRICING["claude-3-haiku"]["input_per_mtok"] * 0.10
    assert math.isclose(cost, expected, rel_tol=1e-12, abs_tol=1e-15)


def test_combined_components_match_formula():
    cost = calculate_cost(
        "claude-3-5-sonnet",
        input_tokens=12345,
        output_tokens=6789,
        cache_write_tokens=345,
        cache_read_tokens=678,
    )
    expected = _expected_cost("claude-3-5-sonnet", 12345, 6789, 345, 678)
    assert math.isclose(cost, expected, rel_tol=1e-12, abs_tol=1e-15)


def test_return_type_is_float():
    result = calculate_cost("claude-3-opus", 10, 5)
    assert isinstance(result, float)


# ---------------------------------------------------------------------------
# Model family resolution (versioned strings, vendor prefixes, dot notation)
# ---------------------------------------------------------------------------
def test_versioned_model_resolves_same_as_family():
    v1 = calculate_cost("claude-3-7-sonnet-20250219", 100, 50, 10, 5)
    v2 = calculate_cost("claude-3-7-sonnet", 100, 50, 10, 5)
    assert v1 == v2


def test_dot_notation_resolves_to_family():
    v_dot = calculate_cost("claude-3.5-sonnet", 100, 50)
    v_dash = calculate_cost("claude-3-5-sonnet", 100, 50)
    assert v_dot == v_dash


def test_vendor_prefix_slash_resolves():
    v = calculate_cost("anthropic/claude-3-5-haiku-20241022", 100, 50)
    expected = calculate_cost("claude-3-5-haiku", 100, 50)
    assert v == expected


def test_vendor_prefix_colon_resolves():
    v = calculate_cost("anthropic:claude-3-opus-20240229", 100, 50)
    expected = calculate_cost("claude-3-opus", 100, 50)
    assert v == expected


def test_longest_match_distinguishes_3_5_sonnet_from_3_sonnet():
    # claude-3-5-sonnet and claude-3-sonnet have different keys but share substring
    # Pricing might be the same; what matters is no ambiguity error and identical to family
    v = calculate_cost("claude-3-5-sonnet-20240620", 1000, 0)
    expected = MODEL_PRICING["claude-3-5-sonnet"]["input_per_mtok"] * 1000 / 1_000_000.0
    assert math.isclose(v, expected, rel_tol=1e-12, abs_tol=1e-15)


@pytest.mark.parametrize("family", list(MODEL_PRICING.keys()))
def test_all_supported_families_resolve(family):
    cost = calculate_cost(family, 100, 50)
    assert cost > 0
    assert isinstance(cost, float)


def test_case_insensitive_resolution():
    v_upper = calculate_cost("CLAUDE-3-OPUS", 100, 50)
    v_lower = calculate_cost("claude-3-opus", 100, 50)
    assert v_upper == v_lower


def test_whitespace_stripped():
    v = calculate_cost("  claude-3-haiku  ", 100, 50)
    expected = calculate_cost("claude-3-haiku", 100, 50)
    assert v == expected


# ---------------------------------------------------------------------------
# R2: Input validation
# ---------------------------------------------------------------------------
@pytest.mark.parametrize("bad_value", [-1, -100, -1_000_000])
def test_negative_input_tokens_raises(bad_value):
    with pytest.raises(ValueError, match="input_tokens"):
        calculate_cost("claude-3-opus", bad_value, 0)


@pytest.mark.parametrize("bad_value", [-1, -100])
def test_negative_output_tokens_raises(bad_value):
    with pytest.raises(ValueError, match="output_tokens"):
        calculate_cost("claude-3-opus", 0, bad_value)


def test_negative_cache_write_tokens_raises():
    with pytest.raises(ValueError, match="cache_write_tokens"):
        calculate_cost("claude-3-opus", 0, 0, cache_write_tokens=-1)


def test_negative_cache_read_tokens_raises():
    with pytest.raises(ValueError, match="cache_read_tokens"):
        calculate_cost("claude-3-opus", 0, 0, cache_read_tokens=-1)


@pytest.mark.parametrize("bad_value", [1.5, 2.0, "100", None, [1], {"a": 1}])
def test_non_int_tokens_raise(bad_value):
    with pytest.raises(ValueError):
        calculate_cost("claude-3-haiku", bad_value, 0)


def test_bool_input_tokens_raises():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-haiku", True, 0)


def test_bool_output_tokens_raises():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-haiku", 0, False)


def test_bool_cache_write_tokens_raises():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-haiku", 0, 0, cache_write_tokens=True)


# ---------------------------------------------------------------------------
# R2 / model validation: empty / non-string model
# ---------------------------------------------------------------------------
@pytest.mark.parametrize("bad_model", ["", "   ", "\t\n", None, 123, 1.5, [], {}])
def test_invalid_model_raises_value_error(bad_model):
    with pytest.raises(ValueError):
        calculate_cost(bad_model, 1, 1)


# ---------------------------------------------------------------------------
# R4: Unknown model handling
# ---------------------------------------------------------------------------
def test_unknown_model_raises_with_model_name_in_message():
    with pytest.raises(ValueError) as excinfo:
        calculate_cost("gpt-4o", 10, 5)
    assert "gpt-4o" in str(excinfo.value)


def test_unknown_model_message_lists_supported_families():
    with pytest.raises(ValueError) as excinfo:
        calculate_cost("gpt-4o", 10, 5)
    msg = str(excinfo.value)
    for family in MODEL_PRICING.keys():
        assert family in msg, f"Expected supported family {family!r} in error message"


@pytest.mark.parametrize("bad_model", ["gpt-4o", "llama-3", "mistral-large", "claude-2", "claude"])
def test_clearly_unknown_models_raise(bad_model):
    with pytest.raises(ValueError):
        calculate_cost(bad_model, 1, 1)


# ---------------------------------------------------------------------------
# R5: Purity / determinism
# ---------------------------------------------------------------------------
def test_determinism_identical_args_return_equal_results():
    a = calculate_cost("claude-3-opus", 1234, 567, 89, 12)
    b = calculate_cost("claude-3-opus", 1234, 567, 89, 12)
    assert a == b


def test_no_mutation_of_pricing_table():
    snapshot = {k: dict(v) for k, v in MODEL_PRICING.items()}
    _ = calculate_cost("claude-3-opus", 100, 200, 50, 25)
    _ = calculate_cost("claude-3-haiku", 1, 2, 3, 4)
    after = {k: dict(v) for k, v in MODEL_PRICING.items()}
    assert snapshot == after


# ---------------------------------------------------------------------------
# calculate_cost_breakdown
# ---------------------------------------------------------------------------
def test_breakdown_total_matches_calculate_cost():
    bd = calculate_cost_breakdown(
        "claude-3-5-sonnet",
        input_tokens=3000, output_tokens=1500, cache_write_tokens=200,
    )
    total = calculate_cost(
        "claude-3-5-sonnet",
        input_tokens=3000, output_tokens=1500, cache_write_tokens=200,
    )
    assert math.isclose(bd["total_cost"], total, rel_tol=1e-12, abs_tol=1e-15)


def test_breakdown_contains_all_expected_keys():
    bd = calculate_cost_breakdown("claude-3-opus", 10, 10, 10, 10)
    for key in ("input_cost", "output_cost", "cache_write_cost",
                "cache_read_cost", "total_cost"):
        assert key in bd
        assert isinstance(bd[key], float)


def test_breakdown_components_sum_to_total():
    bd = calculate_cost_breakdown("claude-3-7-sonnet", 1000, 500, 100, 50)
    component_sum = (bd["input_cost"] + bd["output_cost"]
                     + bd["cache_write_cost"] + bd["cache_read_cost"])
    assert math.isclose(bd["total_cost"], component_sum, rel_tol=1e-12, abs_tol=1e-15)


def test_breakdown_zero_when_tokens_zero():
    bd = calculate_cost_breakdown("claude-3-haiku", 0, 0, 0, 0)
    assert bd["total_cost"] == 0.0
    assert bd["input_cost"] == 0.0
    assert bd["output_cost"] == 0.0
    assert bd["cache_write_cost"] == 0.0
    assert bd["cache_read_cost"] == 0.0


def test_breakdown_validates_inputs():
    with pytest.raises(ValueError):
        calculate_cost_breakdown("claude-3-opus", -1, 0)
    with pytest.raises(ValueError):
        calculate_cost_breakdown("unknown-model", 0, 0)


# ---------------------------------------------------------------------------
# Edge cases: large counts, default cache args
# ---------------------------------------------------------------------------
def test_large_token_counts_do_not_overflow_and_match_formula():
    ti = 10**9
    to = 10**9
    cost = calculate_cost("claude-3-5-sonnet", ti, to)
    expected = _expected_cost("claude-3-5-sonnet", ti, to, 0, 0)
    assert math.isclose(cost, expected, rel_tol=1e-12, abs_tol=1e-9)
    assert math.isfinite(cost)


def test_cache_tokens_without_standard_tokens():
    cost = calculate_cost("claude-3-opus", 0, 0,
                          cache_write_tokens=500, cache_read_tokens=1000)
    expected = _expected_cost("claude-3-opus", 0, 0, 500, 1000)
    assert math.isclose(cost, expected, rel_tol=1e-12, abs_tol=1e-15)


def test_default_cache_args_equal_explicit_zero():
    a = calculate_cost("claude-3-opus", 100, 50)
    b = calculate_cost("claude-3-opus", 100, 50, 0, 0)
    assert a == b


# ---------------------------------------------------------------------------
# Optional: Z3-based formal property (cost non-negativity)
# ---------------------------------------------------------------------------
def test_cost_formula_non_negative_z3():
    z3 = pytest.importorskip("z3")
    ti = z3.Int("ti")
    to = z3.Int("to")
    cw = z3.Int("cw")
    cr = z3.Int("cr")
    Pi = z3.Real("Pi")
    Po = z3.Real("Po")

    solver = z3.Solver()
    solver.add(ti >= 0, to >= 0, cw >= 0, cr >= 0, Pi >= 0, Po >= 0)

    cost = (ti * Pi + to * Po
            + cw * Pi * z3.RealVal("1.25")
            + cr * Pi * z3.RealVal("0.10")) / z3.RealVal(1_000_000)

    solver.add(cost < 0)
    assert solver.check() == z3.unsat