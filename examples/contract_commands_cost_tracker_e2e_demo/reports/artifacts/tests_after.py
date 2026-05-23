

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
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent
SRC = ROOT / "src"

from edit_file_tool.cost_tracker_utility_after import (
    calculate_cost,
    calculate_cost_breakdown,
    MODEL_PRICING,
)


# ---------------------------------------------------------------------------
# R3: Cost formula correctness
# ---------------------------------------------------------------------------
def _expected_cost(model_key, i, o, cw=0, cr=0):
    rates = MODEL_PRICING[model_key]
    ir = rates["input_per_mtok"] / 1_000_000.0
    or_ = rates["output_per_mtok"] / 1_000_000.0
    return i * ir + o * or_ + cw * ir * 1.25 + cr * ir * 0.10


def test_haiku_one_million_input_tokens_matches_input_rate():
    # R3: 1M input tokens for claude-3-5-haiku => exactly input_per_mtok USD
    expected = MODEL_PRICING["claude-3-5-haiku"]["input_per_mtok"]
    actual = calculate_cost("claude-3-5-haiku-20241022",
                            input_tokens=1_000_000, output_tokens=0)
    assert math.isclose(actual, expected, rel_tol=1e-12, abs_tol=1e-15)


def test_zero_tokens_returns_zero():
    assert calculate_cost("claude-3-opus", 0, 0, 0, 0) == 0.0


@pytest.mark.parametrize("model_key", list(MODEL_PRICING.keys()))
def test_cost_matches_formula_each_family(model_key):
    actual = calculate_cost(model_key, 1234, 567, 89, 12)
    expected = _expected_cost(model_key, 1234, 567, 89, 12)
    assert math.isclose(actual, expected, rel_tol=1e-12, abs_tol=1e-15)


def test_cache_write_is_premium_over_input():
    # cache_write should be 1.25x input rate
    only_cw = calculate_cost("claude-3-opus", 0, 0, cache_write_tokens=1_000_000)
    base = MODEL_PRICING["claude-3-opus"]["input_per_mtok"]
    assert math.isclose(only_cw, base * 1.25, rel_tol=1e-12, abs_tol=1e-15)


def test_cache_read_is_discounted_from_input():
    only_cr = calculate_cost("claude-3-opus", 0, 0, cache_read_tokens=1_000_000)
    base = MODEL_PRICING["claude-3-opus"]["input_per_mtok"]
    assert math.isclose(only_cr, base * 0.10, rel_tol=1e-12, abs_tol=1e-15)


def test_versioned_model_resolves_to_family():
    v1 = calculate_cost("claude-3-7-sonnet-20250219", 100, 50, 10, 5)
    v2 = calculate_cost("claude-3-7-sonnet", 100, 50, 10, 5)
    assert v1 == v2


def test_longest_match_disambiguates_sonnet_versions():
    # claude-3-5-sonnet must not be matched as claude-3-sonnet
    v_35 = calculate_cost("claude-3-5-sonnet-20240620", 1000, 1000)
    expected_35 = _expected_cost("claude-3-5-sonnet", 1000, 1000)
    assert math.isclose(v_35, expected_35, rel_tol=1e-12, abs_tol=1e-15)


def test_dot_versioning_resolves():
    v_dot = calculate_cost("claude-3.5-sonnet", 1000, 500)
    v_dash = calculate_cost("claude-3-5-sonnet", 1000, 500)
    assert math.isclose(v_dot, v_dash, rel_tol=1e-12, abs_tol=1e-15)


def test_vendor_prefix_stripped():
    v_pref = calculate_cost("anthropic/claude-3-7-sonnet-20250219", 200, 100)
    v_plain = calculate_cost("claude-3-7-sonnet", 200, 100)
    assert math.isclose(v_pref, v_plain, rel_tol=1e-12, abs_tol=1e-15)


# ---------------------------------------------------------------------------
# R2: Input validation
# ---------------------------------------------------------------------------
@pytest.mark.parametrize("bad", [-1, -100, -1_000_000])
def test_negative_input_tokens_raise(bad):
    with pytest.raises(ValueError, match=r"input_tokens"):
        calculate_cost("claude-3-opus", bad, 0)


@pytest.mark.parametrize("field,bad", [
    ("input_tokens", -1),
    ("output_tokens", -5),
    ("cache_write_tokens", -10),
    ("cache_read_tokens", -2),
])
def test_negative_token_fields_raise(field, bad):
    kwargs = dict(input_tokens=0, output_tokens=0,
                  cache_write_tokens=0, cache_read_tokens=0)
    kwargs[field] = bad
    with pytest.raises(ValueError):
        calculate_cost("claude-3-opus", **kwargs)


@pytest.mark.parametrize("bad", [True, False])
def test_bool_tokens_rejected(bad):
    with pytest.raises(ValueError):
        calculate_cost("claude-3-haiku", bad, 0)


@pytest.mark.parametrize("bad", [1.5, 2.0, "100", None, [1], {"x": 1}])
def test_non_int_tokens_rejected(bad):
    with pytest.raises(ValueError):
        calculate_cost("claude-3-haiku", bad, 0)


@pytest.mark.parametrize("bad_model", ["", "   ", "\t\n"])
def test_empty_or_whitespace_model_raises(bad_model):
    with pytest.raises(ValueError):
        calculate_cost(bad_model, 1, 1)


@pytest.mark.parametrize("bad_model", [None, 123, 1.5, [], {}])
def test_non_string_model_raises(bad_model):
    with pytest.raises(ValueError):
        calculate_cost(bad_model, 1, 1)


# ---------------------------------------------------------------------------
# R4: Unknown model handling
# ---------------------------------------------------------------------------
def test_unknown_model_raises_with_supported_families():
    with pytest.raises(ValueError) as excinfo:
        calculate_cost("gpt-4o", 1, 1)
    msg = str(excinfo.value)
    assert "gpt-4o" in msg
    for fam in MODEL_PRICING.keys():
        assert fam in msg


def test_unknown_unrelated_model_raises():
    with pytest.raises(ValueError):
        calculate_cost("some-totally-unrelated-model", 10, 10)


# ---------------------------------------------------------------------------
# R5: Purity / determinism
# ---------------------------------------------------------------------------
def test_determinism_bitwise_equal():
    a = calculate_cost("claude-3-opus", 1234, 567, 89, 12)
    b = calculate_cost("claude-3-opus", 1234, 567, 89, 12)
    assert a == b


def test_repeated_calls_no_state_pollution():
    # Calling with one model should not affect another
    a1 = calculate_cost("claude-3-opus", 100, 100)
    _ = calculate_cost("claude-3-haiku", 999, 999, 999, 999)
    a2 = calculate_cost("claude-3-opus", 100, 100)
    assert a1 == a2


# ---------------------------------------------------------------------------
# Breakdown helper
# ---------------------------------------------------------------------------
def test_breakdown_total_matches_calculate_cost():
    bd = calculate_cost_breakdown("claude-3-5-sonnet",
                                  input_tokens=3000, output_tokens=1500,
                                  cache_write_tokens=200, cache_read_tokens=50)
    total = calculate_cost("claude-3-5-sonnet",
                           input_tokens=3000, output_tokens=1500,
                           cache_write_tokens=200, cache_read_tokens=50)
    assert math.isclose(bd["total_cost"], total, rel_tol=1e-12, abs_tol=1e-15)


def test_breakdown_keys_and_components():
    bd = calculate_cost_breakdown("claude-3-5-sonnet",
                                  input_tokens=1000, output_tokens=500,
                                  cache_write_tokens=100, cache_read_tokens=20)
    for key in ("input_cost", "output_cost", "cache_write_cost",
                "cache_read_cost", "total_cost"):
        assert key in bd
        assert bd[key] >= 0.0

    expected_total = (bd["input_cost"] + bd["output_cost"]
                      + bd["cache_write_cost"] + bd["cache_read_cost"])
    assert math.isclose(bd["total_cost"], expected_total,
                        rel_tol=1e-12, abs_tol=1e-15)


def test_breakdown_zero_cache_read():
    bd = calculate_cost_breakdown("claude-3-5-sonnet",
                                  input_tokens=10, output_tokens=10)
    assert bd["cache_read_cost"] == 0.0
    assert bd["cache_write_cost"] == 0.0


def test_breakdown_validates_inputs():
    with pytest.raises(ValueError):
        calculate_cost_breakdown("claude-3-opus", -1, 0)
    with pytest.raises(ValueError):
        calculate_cost_breakdown("unknown-model", 0, 0)


# ---------------------------------------------------------------------------
# Cache-only cost without standard tokens still works
# ---------------------------------------------------------------------------
def test_only_cache_tokens_charged_correctly():
    actual = calculate_cost("claude-3-haiku", 0, 0,
                            cache_write_tokens=400, cache_read_tokens=100)
    ir = MODEL_PRICING["claude-3-haiku"]["input_per_mtok"] / 1_000_000.0
    expected = 400 * ir * 1.25 + 100 * ir * 0.10
    assert math.isclose(actual, expected, rel_tol=1e-12, abs_tol=1e-15)


# ---------------------------------------------------------------------------
# Return type
# ---------------------------------------------------------------------------
def test_return_type_is_float():
    result = calculate_cost("claude-3-opus", 1, 1)
    assert isinstance(result, float)


def test_return_type_zero_is_float():
    result = calculate_cost("claude-3-opus", 0, 0)
    assert isinstance(result, float)


# ---------------------------------------------------------------------------
# Formal (Z3) check for cost formula non-negativity and linearity
# ---------------------------------------------------------------------------
def test_cost_formula_nonnegative_z3():
    z3 = pytest.importorskip("z3")
    i = z3.Int("i")
    o = z3.Int("o")
    cw = z3.Int("cw")
    cr = z3.Int("cr")
    Pi = z3.Real("Pi")
    Po = z3.Real("Po")

    cost = (i * Pi + o * Po
            + cw * Pi * z3.RealVal("1.25")
            + cr * Pi * z3.RealVal("0.10")) / z3.RealVal(1_000_000)

    s = z3.Solver()
    s.add(i >= 0, o >= 0, cw >= 0, cr >= 0, Pi >= 0, Po >= 0)
    s.add(cost < 0)
    assert s.check() == z3.unsat


def test_cost_doubles_with_doubled_inputs_z3():
    # Linearity: scaling all token counts by 2 doubles cost (for fixed prices)
    z3 = pytest.importorskip("z3")
    i, o, cw, cr = z3.Ints("i o cw cr")
    Pi, Po = z3.Reals("Pi Po")

    def cost_expr(a, b, c, d):
        return (a * Pi + b * Po
                + c * Pi * z3.RealVal("1.25")
                + d * Pi * z3.RealVal("0.10")) / z3.RealVal(1_000_000)

    s = z3.Solver()
    s.add(i >= 0, o >= 0, cw >= 0, cr >= 0, Pi >= 0, Po >= 0)
    s.add(cost_expr(2 * i, 2 * o, 2 * cw, 2 * cr) != 2 * cost_expr(i, o, cw, cr))
    assert s.check() == z3.unsat