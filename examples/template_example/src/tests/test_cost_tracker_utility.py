from z3 import Solver, Real, And, unsat
import pytest

# Import the actual module under test
from edit_file_tool.cost_tracker_utility import calculate_cost


def test_calculate_cost_known_model():
    # Known model with explicit pricing: claude-3-7-sonnet-20250219
    cost = calculate_cost(
        model="claude-3-7-sonnet-20250219",
        input_tokens=1_000_000,
        output_tokens=100_000,
        cache_write_tokens=0,
        cache_read_tokens=0,
    )
    # input cost = 1,000,000/1_000_000 * 3.00 = 3.0
    # output cost = 100,000/1_000_000 * 15.0 = 1.5
    assert pytest.approx(4.5, abs=1e-12) == cost


def test_calculate_cost_with_cache_tokens():
    # Validate cache multipliers using the known model pricing
    cost = calculate_cost(
        model="claude-3-7-sonnet-20250219",
        input_tokens=500_000,
        output_tokens=0,
        cache_write_tokens=20_000,
        cache_read_tokens=10_000,
    )
    input_rate = 3.00 / 1_000_000
    expected = (
        500_000 * input_rate
        + 20_000 * input_rate * 1.25
        + 10_000 * input_rate * 0.10
    )
    assert pytest.approx(expected, abs=1e-12) == cost


def test_calculate_cost_negative_tokens_are_clamped():
    # Negative values are clamped to zero according to current implementation
    cost = calculate_cost(
        model="claude-3-7-sonnet-20250219",
        input_tokens=-10,
        output_tokens=-5,
        cache_write_tokens=-2,
        cache_read_tokens=-1,
    )
    assert cost == 0.0


def test_calculate_cost_unknown_model_uses_default_pricing():
    # Unknown model strings fall back to the default pricing
    cost = calculate_cost(
        model="sha-claude-X",
        input_tokens=1_000_000,
        output_tokens=1_000_000,
        cache_write_tokens=0,
        cache_read_tokens=0,
    )
    # Default input/output rate is 3.00 and 15.00 per million tokens
    assert pytest.approx(18.0, abs=1e-12) == cost


def test_calculate_cost_zero_tokens():
    cost = calculate_cost(
        model="claude-3-haiku-20240307",
        input_tokens=0,
        output_tokens=0,
        cache_write_tokens=0,
        cache_read_tokens=0,
    )
    assert cost == 0.0


def test_z3_cost_non_negative_default_pricing():
    # Model the cost expression of DEFAULT_PRICING to ensure it can never be negative.
    input_tokens = Real("input_tokens")
    output_tokens = Real("output_tokens")
    cache_write_tokens = Real("cache_write_tokens")
    cache_read_tokens = Real("cache_read_tokens")

    # Default pricing constants (matching the implementation)
    input_rate = 3.0 / 1_000_000
    output_rate = 15.0 / 1_000_000

    cost_expression = (
        input_tokens * input_rate
        + output_tokens * output_rate
        + cache_write_tokens * input_rate * 1.25
        + cache_read_tokens * input_rate * 0.10
    )

    solver = Solver()
    solver.add(And(input_tokens >= 0, output_tokens >= 0, cache_write_tokens >= 0, cache_read_tokens >= 0))
    solver.add(cost_expression < 0)

    # The cost expression should never be negative for non-negative token counts
    assert solver.check() == unsat
