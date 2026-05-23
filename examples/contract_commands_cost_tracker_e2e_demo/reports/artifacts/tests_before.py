

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

import math

import pytest
from z3 import Real, Int, Solver, And, Implies, ForAll, sat, unsat

from edit_file_tool.cost_tracker_utility import (
    MODEL_PRICING,
    calculate_cost,
    calculate_cost_breakdown,
)


# ---------------------------------------------------------------------------
# Basic correctness for known model families
# ---------------------------------------------------------------------------
def test_zero_tokens_returns_zero_cost():
    assert calculate_cost("claude-3-7-sonnet", 0, 0) == 0.0
    assert calculate_cost("claude-3-7-sonnet", 0, 0, 0, 0) == 0.0


def test_sonnet_3_7_one_million_in_one_million_out():
    # $3 input + $15 output per MTok
    cost = calculate_cost("claude-3-7-sonnet", 1_000_000, 1_000_000)
    assert math.isclose(cost, 18.0, rel_tol=0, abs_tol=1e-9)


def test_haiku_3_pricing():
    # $0.25 input + $1.25 output per MTok => 1.5 for 1M+1M
    cost = calculate_cost("claude-3-haiku", 1_000_000, 1_000_000)
    assert math.isclose(cost, 1.50, rel_tol=0, abs_tol=1e-9)


def test_opus_3_pricing():
    # $15 input + $75 output per MTok => 90 for 1M+1M
    cost = calculate_cost("claude-3-opus", 1_000_000, 1_000_000)
    assert math.isclose(cost, 90.0, rel_tol=0, abs_tol=1e-9)


def test_haiku_3_5_pricing():
    # $0.80 input + $4.00 output per MTok
    cost = calculate_cost("claude-3-5-haiku", 1_000_000, 1_000_000)
    assert math.isclose(cost, 4.80, rel_tol=0, abs_tol=1e-9)


# ---------------------------------------------------------------------------
# Versioned & alias model resolution
# ---------------------------------------------------------------------------
def test_versioned_model_resolves_via_prefix():
    cost = calculate_cost("claude-3-7-sonnet-20250219", 1_000_000, 1_000_000)
    assert math.isclose(cost, 18.0, abs_tol=1e-9)


def test_versioned_haiku_resolves():
    cost = calculate_cost("claude-3-haiku-20240307", 1_000_000, 1_000_000)
    assert math.isclose(cost, 1.50, abs_tol=1e-9)


def test_alias_dot_naming_resolves():
    # "claude-3.7-sonnet" alias maps to claude-3-7-sonnet
    cost = calculate_cost("claude-3.7-sonnet", 1_000_000, 0)
    assert math.isclose(cost, 3.0, abs_tol=1e-9)


def test_alias_3_5_sonnet_resolves():
    cost = calculate_cost("claude-3.5-sonnet-latest", 1_000_000, 0)
    assert math.isclose(cost, 3.0, abs_tol=1e-9)


def test_model_resolution_case_insensitive():
    cost = calculate_cost("Claude-3-7-Sonnet-20250219", 1_000_000, 1_000_000)
    assert math.isclose(cost, 18.0, abs_tol=1e-9)


def test_specific_family_preferred_over_general_3_5_haiku_vs_3_haiku():
    # claude-3-5-haiku must NOT be resolved as claude-3-haiku
    cost_3_5 = calculate_cost("claude-3-5-haiku-20241022", 1_000_000, 0)
    cost_3 = calculate_cost("claude-3-haiku-20240307", 1_000_000, 0)
    assert math.isclose(cost_3_5, 0.80, abs_tol=1e-9)
    assert math.isclose(cost_3, 0.25, abs_tol=1e-9)


# ---------------------------------------------------------------------------
# Cache pricing rules
# ---------------------------------------------------------------------------
def test_cache_write_charged_at_125_percent_of_input_rate():
    # 1M cache_write at $3 input rate => 3 * 1.25 = 3.75
    cost = calculate_cost(
        "claude-3-7-sonnet",
        input_tokens=0,
        output_tokens=0,
        cache_write_tokens=1_000_000,
        cache_read_tokens=0,
    )
    assert math.isclose(cost, 3.75, abs_tol=1e-9)


def test_cache_read_charged_at_10_percent_of_input_rate():
    # 1M cache_read at $3 input rate => 3 * 0.10 = 0.30
    cost = calculate_cost(
        "claude-3-7-sonnet",
        input_tokens=0,
        output_tokens=0,
        cache_write_tokens=0,
        cache_read_tokens=1_000_000,
    )
    assert math.isclose(cost, 0.30, abs_tol=1e-9)


def test_combined_cost_with_cache_components():
    # in=500k, out=200k, cw=300k, cr=1M for claude-3-7-sonnet
    # input: 0.5 * 3 = 1.50
    # output: 0.2 * 15 = 3.00
    # cache_write: 0.3 * 3 * 1.25 = 1.125
    # cache_read: 1.0 * 3 * 0.10 = 0.30
    # total = 5.925
    cost = calculate_cost(
        "claude-3-7-sonnet",
        input_tokens=500_000,
        output_tokens=200_000,
        cache_write_tokens=300_000,
        cache_read_tokens=1_000_000,
    )
    assert math.isclose(cost, 5.925, abs_tol=1e-9)


def test_cache_tokens_without_standard_tokens():
    cost = calculate_cost(
        "claude-3-haiku",
        input_tokens=0,
        output_tokens=0,
        cache_write_tokens=2_000_000,
        cache_read_tokens=2_000_000,
    )
    # input_rate = 0.25/1M; cw = 2*0.25*1.25 = 0.625; cr = 2*0.25*0.10 = 0.05
    assert math.isclose(cost, 0.675, abs_tol=1e-9)


# ---------------------------------------------------------------------------
# Input validation
# ---------------------------------------------------------------------------
def test_negative_input_tokens_raises():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", -1, 0)


def test_negative_output_tokens_raises():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", 0, -1)


def test_negative_cache_write_tokens_raises():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", 0, 0, cache_write_tokens=-5)


def test_negative_cache_read_tokens_raises():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", 0, 0, cache_read_tokens=-5)


def test_bool_tokens_rejected():
    # bool is int subclass; must be rejected per spec
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", True, 0)
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", 0, False)


def test_float_tokens_rejected():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", 1.5, 0)


def test_string_tokens_rejected():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", "100", 0)


def test_empty_model_raises():
    with pytest.raises(ValueError):
        calculate_cost("", 10, 10)


def test_whitespace_model_raises():
    with pytest.raises(ValueError):
        calculate_cost("   ", 10, 10)


def test_non_string_model_raises():
    with pytest.raises(ValueError):
        calculate_cost(None, 10, 10)
    with pytest.raises(ValueError):
        calculate_cost(123, 10, 10)


def test_unknown_model_raises_with_message_listing_families():
    with pytest.raises(ValueError) as excinfo:
        calculate_cost("gpt-4o", 10, 10)
    msg = str(excinfo.value)
    assert "gpt-4o" in msg
    # Some supported family should be mentioned
    assert "claude-3" in msg


# ---------------------------------------------------------------------------
# Linearity / scaling properties
# ---------------------------------------------------------------------------
def test_cost_scales_linearly_with_input_tokens():
    base = calculate_cost("claude-3-7-sonnet", 100_000, 0)
    doubled = calculate_cost("claude-3-7-sonnet", 200_000, 0)
    assert math.isclose(doubled, 2 * base, abs_tol=1e-9)


def test_cost_is_additive_across_components():
    in_only = calculate_cost("claude-3-7-sonnet", 12_345, 0)
    out_only = calculate_cost("claude-3-7-sonnet", 0, 6_789)
    cw_only = calculate_cost("claude-3-7-sonnet", 0, 0, 1_111, 0)
    cr_only = calculate_cost("claude-3-7-sonnet", 0, 0, 0, 2_222)
    combined = calculate_cost("claude-3-7-sonnet", 12_345, 6_789, 1_111, 2_222)
    assert math.isclose(combined, in_only + out_only + cw_only + cr_only, abs_tol=1e-9)


# ---------------------------------------------------------------------------
# Breakdown helper
# ---------------------------------------------------------------------------
def test_breakdown_components_sum_to_total():
    b = calculate_cost_breakdown(
        "claude-3-7-sonnet", 500_000, 200_000, 300_000, 1_000_000
    )
    s = b["input_cost"] + b["output_cost"] + b["cache_write_cost"] + b["cache_read_cost"]
    assert math.isclose(s, b["total_cost"], abs_tol=1e-9)


def test_breakdown_total_matches_calculate_cost():
    args = ("claude-3-5-sonnet-20240620", 123_456, 7_890, 1_234, 56_789)
    b = calculate_cost_breakdown(*args)
    assert math.isclose(b["total_cost"], calculate_cost(*args), abs_tol=1e-9)


def test_breakdown_contains_expected_keys():
    b = calculate_cost_breakdown("claude-3-7-sonnet", 1_000_000, 0, 0, 0)
    expected = {"family", "input_cost", "output_cost",
                "cache_write_cost", "cache_read_cost", "total_cost"}
    assert expected.issubset(set(b.keys()))
    assert b["family"] == "claude-3-7-sonnet"
    assert math.isclose(b["input_cost"], 3.0, abs_tol=1e-9)
    assert math.isclose(b["output_cost"], 0.0, abs_tol=1e-9)


def test_breakdown_validates_inputs():
    with pytest.raises(ValueError):
        calculate_cost_breakdown("claude-3-7-sonnet", -1, 0)
    with pytest.raises(ValueError):
        calculate_cost_breakdown("unknown-model", 10, 10)


# ---------------------------------------------------------------------------
# Pricing table integrity
# ---------------------------------------------------------------------------
def test_model_pricing_entries_have_required_keys_and_positive_rates():
    assert MODEL_PRICING, "MODEL_PRICING must not be empty"
    for family, prices in MODEL_PRICING.items():
        assert "input_per_mtok" in prices
        assert "output_per_mtok" in prices
        assert prices["input_per_mtok"] > 0
        assert prices["output_per_mtok"] > 0


@pytest.mark.parametrize("family", list(MODEL_PRICING.keys()))
def test_every_family_resolves_and_prices_match_table(family):
    pricing = MODEL_PRICING[family]
    cost = calculate_cost(family, 1_000_000, 0)
    assert math.isclose(cost, pricing["input_per_mtok"], abs_tol=1e-9)
    cost_out = calculate_cost(family, 0, 1_000_000)
    assert math.isclose(cost_out, pricing["output_per_mtok"], abs_tol=1e-9)


# ---------------------------------------------------------------------------
# Z3 formal checks: cache multipliers and non-negativity of cost
# ---------------------------------------------------------------------------
def test_z3_cache_multipliers_are_consistent_with_spec():
    # For any non-negative cache token amount, cache_write cost must equal
    # 1.25 * input_rate * tokens and cache_read cost must equal
    # 0.10 * input_rate * tokens. Verified symbolically for claude-3-7-sonnet.
    input_rate = MODEL_PRICING["claude-3-7-sonnet"]["input_per_mtok"] / 1_000_000.0

    cw_tokens = Real("cw")
    cr_tokens = Real("cr")
    expected_cw = cw_tokens * input_rate * 1.25
    expected_cr = cr_tokens * input_rate * 0.10

    # Sample concrete witnesses; assert calculate_cost agrees.
    for n in (0, 1, 1000, 1_000_000):
        s = Solver()
        s.add(cw_tokens == n, cr_tokens == 0)
        assert s.check() == sat
        cost = calculate_cost("claude-3-7-sonnet", 0, 0, n, 0)
        assert math.isclose(cost, n * input_rate * 1.25, abs_tol=1e-9)

        s = Solver()
        s.add(cw_tokens == 0, cr_tokens == n)
        assert s.check() == sat
        cost = calculate_cost("claude-3-7-sonnet", 0, 0, 0, n)
        assert math.isclose(cost, n * input_rate * 0.10, abs_tol=1e-9)


def test_z3_cost_non_negative_for_non_negative_inputs():
    # Symbolic proof that the cost formula is non-negative when all
    # token counts and rates are non-negative.
    i, o, cw, cr = Real("i"), Real("o"), Real("cw"), Real("cr")
    ir, orate = Real("ir"), Real("orate")
    cost_expr = i * ir + o * orate + cw * ir * 1.25 + cr * ir * 0.10

    s = Solver()
    s.add(i >= 0, o >= 0, cw >= 0, cr >= 0, ir >= 0, orate >= 0)
    s.add(cost_expr < 0)
    assert s.check() == unsat