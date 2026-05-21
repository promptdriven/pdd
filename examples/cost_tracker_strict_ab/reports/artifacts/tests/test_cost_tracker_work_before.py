

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

from edit_file_tool.cost_tracker_utility import (
    MODEL_PRICING,
    calculate_cost,
    calculate_cost_breakdown,
)


# ---------------------------------------------------------------------------
# Basic correctness
# ---------------------------------------------------------------------------
def test_zero_tokens_returns_zero():
    assert calculate_cost("claude-3-7-sonnet", 0, 0) == 0.0


def test_zero_tokens_with_explicit_cache_zero():
    assert calculate_cost("claude-3-7-sonnet", 0, 0, 0, 0) == 0.0


def test_returns_float_type():
    result = calculate_cost("claude-3-7-sonnet", 100, 50)
    assert isinstance(result, float)


def test_claude_3_7_sonnet_one_million_each():
    # 3 (input) + 15 (output) = 18 USD
    cost = calculate_cost("claude-3-7-sonnet", 1_000_000, 1_000_000)
    assert math.isclose(cost, 18.0, abs_tol=1e-9)


def test_claude_3_5_sonnet_pricing():
    cost = calculate_cost("claude-3-5-sonnet", 1_000_000, 1_000_000)
    assert math.isclose(cost, 18.0, abs_tol=1e-9)


def test_claude_3_5_haiku_pricing():
    # 0.80 + 4.00 = 4.80
    cost = calculate_cost("claude-3-5-haiku", 1_000_000, 1_000_000)
    assert math.isclose(cost, 4.80, abs_tol=1e-9)


def test_claude_3_opus_pricing():
    # 15 + 75 = 90
    cost = calculate_cost("claude-3-opus", 1_000_000, 1_000_000)
    assert math.isclose(cost, 90.0, abs_tol=1e-9)


def test_claude_3_haiku_pricing():
    # 0.25 + 1.25 = 1.50
    cost = calculate_cost("claude-3-haiku", 1_000_000, 1_000_000)
    assert math.isclose(cost, 1.50, abs_tol=1e-9)


def test_claude_3_sonnet_pricing():
    cost = calculate_cost("claude-3-sonnet", 1_000_000, 1_000_000)
    assert math.isclose(cost, 18.0, abs_tol=1e-9)


# ---------------------------------------------------------------------------
# Versioned model strings
# ---------------------------------------------------------------------------
def test_versioned_claude_3_7_sonnet():
    cost = calculate_cost("claude-3-7-sonnet-20250219", 1_000_000, 1_000_000)
    assert math.isclose(cost, 18.0, abs_tol=1e-9)


def test_versioned_claude_3_haiku():
    cost = calculate_cost("claude-3-haiku-20240307", 1_000_000, 1_000_000)
    assert math.isclose(cost, 1.50, abs_tol=1e-9)


def test_versioned_claude_3_5_haiku_does_not_match_claude_3_haiku():
    # Specific-first resolution must pick 3-5-haiku, not 3-haiku.
    cost = calculate_cost("claude-3-5-haiku-20241022", 1_000_000, 1_000_000)
    assert math.isclose(cost, 4.80, abs_tol=1e-9)


def test_versioned_claude_3_5_sonnet():
    cost = calculate_cost("claude-3-5-sonnet-20241022", 1_000_000, 1_000_000)
    assert math.isclose(cost, 18.0, abs_tol=1e-9)


def test_dotted_alias_3_7_sonnet():
    cost = calculate_cost("claude-3.7-sonnet", 1_000_000, 1_000_000)
    assert math.isclose(cost, 18.0, abs_tol=1e-9)


def test_dotted_alias_3_5_haiku():
    cost = calculate_cost("claude-3.5-haiku", 1_000_000, 1_000_000)
    assert math.isclose(cost, 4.80, abs_tol=1e-9)


def test_model_string_is_case_insensitive():
    cost = calculate_cost("CLAUDE-3-7-SONNET", 1_000_000, 1_000_000)
    assert math.isclose(cost, 18.0, abs_tol=1e-9)


def test_model_string_is_stripped():
    cost = calculate_cost("  claude-3-7-sonnet  ", 1_000_000, 1_000_000)
    assert math.isclose(cost, 18.0, abs_tol=1e-9)


# ---------------------------------------------------------------------------
# Cache pricing
# ---------------------------------------------------------------------------
def test_cache_write_premium():
    # 1M cache writes on claude-3-7-sonnet: 3 * 1.25 = 3.75
    cost = calculate_cost(
        "claude-3-7-sonnet",
        input_tokens=0,
        output_tokens=0,
        cache_write_tokens=1_000_000,
        cache_read_tokens=0,
    )
    assert math.isclose(cost, 3.75, abs_tol=1e-9)


def test_cache_read_discount():
    # 1M cache reads on claude-3-7-sonnet: 3 * 0.10 = 0.30
    cost = calculate_cost(
        "claude-3-7-sonnet",
        input_tokens=0,
        output_tokens=0,
        cache_write_tokens=0,
        cache_read_tokens=1_000_000,
    )
    assert math.isclose(cost, 0.30, abs_tol=1e-9)


def test_combined_input_output_cache():
    # 100k in, 50k out, 200k cache_write, 500k cache_read
    cost = calculate_cost(
        "claude-3-7-sonnet",
        input_tokens=100_000,
        output_tokens=50_000,
        cache_write_tokens=200_000,
        cache_read_tokens=500_000,
    )
    input_rate = 3.0 / 1_000_000
    output_rate = 15.0 / 1_000_000
    expected = (
        100_000 * input_rate
        + 50_000 * output_rate
        + 200_000 * input_rate * 1.25
        + 500_000 * input_rate * 0.10
    )
    assert math.isclose(cost, expected, abs_tol=1e-9)


def test_cache_only_no_standard_tokens():
    cost = calculate_cost(
        "claude-3-haiku",
        input_tokens=0,
        output_tokens=0,
        cache_write_tokens=1_000_000,
        cache_read_tokens=1_000_000,
    )
    # input rate = 0.25 / 1M -> cache_write: 0.25*1.25=0.3125, cache_read: 0.25*0.10=0.025
    assert math.isclose(cost, 0.3125 + 0.025, abs_tol=1e-9)


# ---------------------------------------------------------------------------
# Validation: model
# ---------------------------------------------------------------------------
def test_empty_model_raises():
    with pytest.raises(ValueError):
        calculate_cost("", 10, 10)


def test_whitespace_only_model_raises():
    with pytest.raises(ValueError):
        calculate_cost("   ", 10, 10)


def test_non_string_model_raises():
    with pytest.raises(ValueError):
        calculate_cost(None, 10, 10)  # type: ignore[arg-type]


def test_unknown_model_raises():
    with pytest.raises(ValueError) as exc_info:
        calculate_cost("gpt-4o", 10, 10)
    assert "gpt-4o" in str(exc_info.value)


def test_unknown_model_error_lists_supported_families():
    with pytest.raises(ValueError) as exc_info:
        calculate_cost("totally-unknown-model", 10, 10)
    msg = str(exc_info.value)
    # Should mention at least one well-known family
    assert "claude-3" in msg


# ---------------------------------------------------------------------------
# Validation: token counts
# ---------------------------------------------------------------------------
def test_negative_input_tokens_raises():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", -1, 0)


def test_negative_output_tokens_raises():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", 0, -1)


def test_negative_cache_write_raises():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", 0, 0, -1, 0)


def test_negative_cache_read_raises():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", 0, 0, 0, -1)


def test_bool_input_tokens_raises():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", True, 0)  # type: ignore[arg-type]


def test_bool_output_tokens_raises():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", 0, False)  # type: ignore[arg-type]


def test_float_tokens_raises():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", 10.5, 0)  # type: ignore[arg-type]


def test_string_tokens_raises():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", "100", 0)  # type: ignore[arg-type]


def test_none_tokens_raises():
    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet", None, 0)  # type: ignore[arg-type]


# ---------------------------------------------------------------------------
# Linearity / scaling properties
# ---------------------------------------------------------------------------
def test_cost_scales_linearly_with_input_tokens():
    base = calculate_cost("claude-3-7-sonnet", 1_000, 0)
    doubled = calculate_cost("claude-3-7-sonnet", 2_000, 0)
    assert math.isclose(doubled, 2 * base, abs_tol=1e-12)


def test_cost_scales_linearly_with_output_tokens():
    base = calculate_cost("claude-3-opus", 0, 1_000)
    tripled = calculate_cost("claude-3-opus", 0, 3_000)
    assert math.isclose(tripled, 3 * base, abs_tol=1e-12)


def test_cost_is_additive_across_components():
    in_only = calculate_cost("claude-3-7-sonnet", 1000, 0)
    out_only = calculate_cost("claude-3-7-sonnet", 0, 1000)
    cw_only = calculate_cost("claude-3-7-sonnet", 0, 0, 1000, 0)
    cr_only = calculate_cost("claude-3-7-sonnet", 0, 0, 0, 1000)
    combined = calculate_cost("claude-3-7-sonnet", 1000, 1000, 1000, 1000)
    assert math.isclose(combined, in_only + out_only + cw_only + cr_only, abs_tol=1e-12)


def test_cache_write_more_expensive_than_input():
    in_cost = calculate_cost("claude-3-7-sonnet", 1_000_000, 0)
    cw_cost = calculate_cost("claude-3-7-sonnet", 0, 0, 1_000_000, 0)
    assert cw_cost > in_cost
    assert math.isclose(cw_cost / in_cost, 1.25, abs_tol=1e-9)


def test_cache_read_cheaper_than_input():
    in_cost = calculate_cost("claude-3-7-sonnet", 1_000_000, 0)
    cr_cost = calculate_cost("claude-3-7-sonnet", 0, 0, 0, 1_000_000)
    assert cr_cost < in_cost
    assert math.isclose(cr_cost / in_cost, 0.10, abs_tol=1e-9)


# ---------------------------------------------------------------------------
# Breakdown helper
# ---------------------------------------------------------------------------
def test_breakdown_keys_present():
    breakdown = calculate_cost_breakdown("claude-3-7-sonnet", 100, 200, 300, 400)
    for key in (
        "family",
        "input_cost",
        "output_cost",
        "cache_write_cost",
        "cache_read_cost",
        "total_cost",
    ):
        assert key in breakdown


def test_breakdown_family_resolution():
    breakdown = calculate_cost_breakdown(
        "claude-3-7-sonnet-20250219", 0, 0, 0, 0
    )
    assert breakdown["family"] == "claude-3-7-sonnet"


def test_breakdown_total_matches_calculate_cost():
    args = ("claude-3-5-haiku", 1234, 5678, 999, 4242)
    total = calculate_cost(*args)
    breakdown = calculate_cost_breakdown(*args)
    assert math.isclose(breakdown["total_cost"], total, abs_tol=1e-12)


def test_breakdown_components_sum_to_total():
    breakdown = calculate_cost_breakdown(
        "claude-3-opus", 1000, 2000, 500, 1500
    )
    component_sum = (
        breakdown["input_cost"]
        + breakdown["output_cost"]
        + breakdown["cache_write_cost"]
        + breakdown["cache_read_cost"]
    )
    assert math.isclose(component_sum, breakdown["total_cost"], abs_tol=1e-12)


def test_breakdown_individual_components_values():
    breakdown = calculate_cost_breakdown(
        "claude-3-7-sonnet", 1_000_000, 1_000_000, 1_000_000, 1_000_000
    )
    assert math.isclose(breakdown["input_cost"], 3.0, abs_tol=1e-9)
    assert math.isclose(breakdown["output_cost"], 15.0, abs_tol=1e-9)
    assert math.isclose(breakdown["cache_write_cost"], 3.75, abs_tol=1e-9)
    assert math.isclose(breakdown["cache_read_cost"], 0.30, abs_tol=1e-9)


def test_breakdown_validates_inputs():
    with pytest.raises(ValueError):
        calculate_cost_breakdown("claude-3-7-sonnet", -1, 0)
    with pytest.raises(ValueError):
        calculate_cost_breakdown("", 1, 1)
    with pytest.raises(ValueError):
        calculate_cost_breakdown("unknown-model", 1, 1)


# ---------------------------------------------------------------------------
# MODEL_PRICING table integrity
# ---------------------------------------------------------------------------
def test_model_pricing_contains_expected_families():
    expected = {
        "claude-3-7-sonnet",
        "claude-3-5-sonnet",
        "claude-3-5-haiku",
        "claude-3-opus",
        "claude-3-sonnet",
        "claude-3-haiku",
    }
    assert expected.issubset(set(MODEL_PRICING.keys()))


@pytest.mark.parametrize("family", list(MODEL_PRICING.keys()))
def test_each_pricing_entry_has_input_and_output(family):
    entry = MODEL_PRICING[family]
    assert "input_per_mtok" in entry
    assert "output_per_mtok" in entry
    assert entry["input_per_mtok"] > 0
    assert entry["output_per_mtok"] > 0


@pytest.mark.parametrize("family", list(MODEL_PRICING.keys()))
def test_each_known_family_resolves_and_computes(family):
    # Sanity: every entry in MODEL_PRICING is reachable via calculate_cost.
    cost = calculate_cost(family, 1_000_000, 0)
    expected = MODEL_PRICING[family]["input_per_mtok"]
    assert math.isclose(cost, expected, abs_tol=1e-9)


# ---------------------------------------------------------------------------
# Large counts: numerical sanity (no overflow, monotonic)
# ---------------------------------------------------------------------------
def test_large_token_counts_finite():
    cost = calculate_cost("claude-3-opus", 10_000_000_000, 10_000_000_000)
    assert math.isfinite(cost)
    assert cost > 0


def test_monotonic_in_input_tokens():
    a = calculate_cost("claude-3-7-sonnet", 100, 0)
    b = calculate_cost("claude-3-7-sonnet", 101, 0)
    assert b > a