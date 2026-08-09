"""Tests for the time-to-effort helper.

Kept separate from the llm_invoke and cli test files so the helper's
contract is pinned without requiring the rest of either module to import.
"""

import pytest

from pdd.reasoning import time_to_effort_level


@pytest.mark.parametrize(
    "time, expected",
    [
        (0.0, "low"),
        (0.1, "low"),
        (0.3, "low"),      # strict > on the boundary
        (0.31, "medium"),
        (0.5, "medium"),
        (0.7, "medium"),   # strict > on the boundary
        (0.71, "high"),
        (0.85, "high"),
        (1.0, "high"),
    ],
)
def test_time_to_effort_level_boundaries(time, expected):
    assert time_to_effort_level(time) == expected
