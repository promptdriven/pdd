"""Reference tests for cost_tracker contract coverage (deterministic, no LLM)."""
from __future__ import annotations

import pytest

# R1: validation
def test_R1_negative_tokens_raise():
    from edit_file_tool.cost_tracker_utility import calculate_cost

    with pytest.raises(ValueError):
        calculate_cost("claude-3-7-sonnet-20250219", -1, 0)


# R2: model family resolution
def test_R2_unknown_model_raises():
    from edit_file_tool.cost_tracker_utility import calculate_cost

    with pytest.raises(ValueError, match="supported"):
        calculate_cost("not-a-claude-model", 100, 0)


# R3: cache pricing multipliers (smoke — non-zero cache_write increases cost)
def test_R3_cache_write_increases_cost():
    from edit_file_tool.cost_tracker_utility import calculate_cost

    model = "claude-3-7-sonnet-20250219"
    base = calculate_cost(model, 1000, 0, 0, 0)
    with_cache = calculate_cost(model, 1000, 0, 1000, 0)
    assert with_cache > base
