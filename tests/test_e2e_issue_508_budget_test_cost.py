"""Tests for issue #508: Budget tracker drops test/test_extend costs due to wrong tuple index.

The bug: sync_orchestration.py line 1752 uses `result[-2]` to extract cost from operation
results. For 4-tuples (returned by cmd_test_main), `result[-2]` is the model name string,
not the cost float, so isinstance(..., (int, float)) fails and cost defaults to $0.00.

Secondary bug: line 1777 only checks `operation == 'test'`, missing `test_extend`.
"""

import pytest


class TestBudgetCostExtraction:
    """Test the cost extraction logic at sync_orchestration.py:1752."""

    def _extract_cost_like_line_1752(self, result):
        """Replicates the exact buggy logic from line 1752."""
        cost = result[-2] if len(result) >= 2 and isinstance(result[-2], (int, float)) else 0.0
        return cost

    def _extract_cost_fixed(self, result, operation):
        """What the fixed logic should do."""
        if operation in ('test', 'test_extend') and len(result) >= 4:
            cost = result[1] if isinstance(result[1], (int, float)) else 0.0
        else:
            cost = result[-2] if len(result) >= 2 and isinstance(result[-2], (int, float)) else 0.0
        return cost

    def test_4_tuple_test_cost_extraction(self):
        """Bug: 4-tuple from cmd_test_main has cost at index 1, but result[-2] gives index 2 (model name).

        cmd_test_main returns: (content, cost, model, agentic_success)
        result[-2] for a 4-tuple = result[2] = model name (string) → isinstance check fails → $0.00
        """
        # Simulate cmd_test_main 4-tuple return
        result = ("test content", 0.0007821, "gpt-4o-mini", True)

        cost = self._extract_cost_like_line_1752(result)

        # This assertion demonstrates the bug: cost should be 0.0007821 but is 0.0
        assert cost == pytest.approx(0.0007821), (
            f"Cost should be {result[1]} but got {cost}. "
            f"result[-2] = {result[-2]!r} (type={type(result[-2]).__name__}) is the model name, not cost."
        )

    def test_4_tuple_test_extend_cost_extraction(self):
        """Same bug for test_extend operation which also calls cmd_test_main."""
        result = ("test content", 0.0012345, "claude-sonnet-4-5", False)

        cost = self._extract_cost_like_line_1752(result)

        assert cost == pytest.approx(0.0012345), (
            f"test_extend cost should be {result[1]} but got {cost}."
        )

    def test_3_tuple_generate_cost_extraction(self):
        """3-tuple operations (generate, etc.) work correctly with result[-2] — regression guard."""
        # 3-tuple: (content, cost, model)
        result = ("generated code", 0.0005551, "gpt-4o-mini")

        cost = self._extract_cost_like_line_1752(result)

        # For 3-tuples, result[-2] = result[1] = cost float — this works by accident
        assert cost == pytest.approx(0.0005551)

    def test_budget_enforcement_with_test_costs(self):
        """Budget check underestimates spend when test costs are dropped.

        Simulates a sync loop where generate costs $0.05 and test costs $0.10.
        With budget=$0.12, sync should stop after test. But since test cost is
        dropped to $0.00, the budget check sees only $0.05 and keeps going.
        """
        budget = 0.12
        current_cost = 0.0

        # Operation 1: generate (3-tuple) — cost extracted correctly
        generate_result = ("code", 0.05, "gpt-4o-mini")
        cost = self._extract_cost_like_line_1752(generate_result)
        current_cost += cost

        # Operation 2: test (4-tuple) — cost dropped due to bug
        test_result = ("tests", 0.10, "gpt-4o-mini", True)
        cost = self._extract_cost_like_line_1752(test_result)
        current_cost += cost

        # With the bug, current_cost is only 0.05 (test cost dropped)
        # It should be 0.15, exceeding the budget of 0.12
        assert current_cost >= budget, (
            f"Total cost should be $0.15 (exceeding budget ${budget}) "
            f"but tracker shows ${current_cost:.4f} due to dropped test cost."
        )


class TestLoggingSectionTestExtendGap:
    """Test the secondary bug: logging at line 1777 misses test_extend."""

    def _extract_logging_cost_like_line_1777(self, result, operation):
        """Replicates the logging cost extraction logic from lines 1777-1782."""
        if operation == 'test' and len(result) >= 4:
            actual_cost = result[1] if isinstance(result[1], (int, float)) else 0.0
        else:
            actual_cost = result[-2] if isinstance(result[-2], (int, float)) else 0.0
        return actual_cost

    def test_logging_test_extend_cost(self):
        """Bug: logging section only checks operation == 'test', not 'test_extend'.

        test_extend also returns a 4-tuple from cmd_test_main, so the same
        explicit indexing should apply.
        """
        result = ("tests", 0.0012345, "claude-sonnet-4-5", True)

        actual_cost = self._extract_logging_cost_like_line_1777(result, operation='test_extend')

        assert actual_cost == pytest.approx(0.0012345), (
            f"Logging cost for test_extend should be {result[1]} but got {actual_cost}. "
            f"The logging section only checks operation == 'test', missing 'test_extend'."
        )
