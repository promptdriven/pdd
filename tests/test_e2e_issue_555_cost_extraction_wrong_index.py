"""Tests for issue #555: cost extraction reads wrong tuple index for generate/crash/fix/verify.

The bug: sync_orchestration.py lines 1857-1858 and 1889-1890 always read result[1] as cost
and result[2] as model, but each operation returns a different tuple format:

- generate: (content, was_incremental, cost, model) — cost at index 2, model at index 3
- crash: (success, final_code, final_program, attempts, cost, model) — cost at index 4, model at index 5
- fix: (success, fixed_unit_test, fixed_code, attempts, total_cost, model_name) — cost at index 4, model at index 5
- verify: (success, final_program, final_code, attempts, total_cost, model_name) — cost at index 4, model at index 5

Secondary bug: operation_log.py lines 339-340 has the same incorrect extraction logic.

Bool quirk: Python's bool subclasses int, so isinstance(False, (int, float)) returns True.
For generate, result[1] is was_incremental (bool), which silently passes the isinstance check
and cost becomes int(False)=0 or int(True)=1 instead of the actual cost at result[2].
"""

import pytest

from pdd.sync_orchestration import _extract_cost_from_result, _extract_model_from_result


class TestCostExtractionBudgetAccumulation:
    """Test cost extraction via _extract_cost_from_result helper (fixes sync_orchestration.py:1857-1858).

    The old buggy code always read result[1] as cost with no operation-specific branching.
    The fix dispatches to the correct index per operation.
    """

    def test_generate_cost_extraction(self):
        """generate returns (content, was_incremental, cost, model) — cost is at index 2, not 1.

        Bug: result[1] is was_incremental (bool). Since bool subclasses int,
        isinstance(False, (int, float)) is True → cost becomes 0 instead of 0.0421.
        """
        # code_generator_main return format: (content, was_incremental, cost, model)
        result = ("generated code", False, 0.0421, "claude-sonnet-4-6")

        cost = _extract_cost_from_result('generate', result)

        assert cost == pytest.approx(0.0421), (
            f"generate cost should be {result[2]} (index 2) but got {cost}. "
            f"result[1] = {result[1]!r} (was_incremental) was read as cost due to bool⊂int."
        )

    def test_crash_cost_extraction(self):
        """crash returns (success, final_code, final_program, attempts, cost, model) — cost at index 4.

        Bug: result[1] is final_code (str), isinstance fails → cost defaults to 0.0.
        """
        # crash_main return format: (success, final_code, final_program, attempts, cost, model)
        result = (True, "code content", "program content", 2, 0.0315, "gpt-4o-mini")

        cost = _extract_cost_from_result('crash', result)

        assert cost == pytest.approx(0.0315), (
            f"crash cost should be {result[4]} (index 4) but got {cost}. "
            f"result[1] = {result[1]!r} (final_code string) is not a number."
        )

    def test_fix_cost_extraction(self):
        """fix returns (success, fixed_unit_test, fixed_code, attempts, total_cost, model) — cost at index 4.

        Bug: result[1] is fixed_unit_test (str), isinstance fails → cost defaults to 0.0.
        """
        # fix_main return format: (success, fixed_unit_test, fixed_code, attempts, total_cost, model_name)
        result = (True, "fixed test code", "fixed source code", 3, 0.0892, "claude-sonnet-4-6")

        cost = _extract_cost_from_result('fix', result)

        assert cost == pytest.approx(0.0892), (
            f"fix cost should be {result[4]} (index 4) but got {cost}. "
            f"result[1] = {result[1]!r} (fixed_unit_test string) is not a number."
        )

    def test_verify_cost_extraction(self):
        """verify returns (success, final_program, final_code, attempts, total_cost, model) — cost at index 4.

        Bug: result[1] is final_program (str), isinstance fails → cost defaults to 0.0.
        """
        # fix_verification_main return format: (success, final_program, final_code, attempts, total_cost, model_name)
        result = (True, "program content", "code content", 1, 0.0267, "gpt-4o-mini")

        cost = _extract_cost_from_result('verify', result)

        assert cost == pytest.approx(0.0267), (
            f"verify cost should be {result[4]} (index 4) but got {cost}. "
            f"result[1] = {result[1]!r} (final_program string) is not a number."
        )


class TestCostExtractionLogging:
    """Test cost/model extraction via helpers (fixes sync_orchestration.py:1885-1890 log entry).

    The old buggy code read result[1] as cost and result[2] as model for all non-test operations,
    which is wrong for generate (cost=[2], model=[3]) and crash/fix/verify (cost=[4], model=[5]).
    """

    def test_generate_logging_cost_and_model(self):
        """generate: cost should be result[2], model should be result[3].

        Bug: Reads result[1] (was_incremental=False) as cost → 0 (bool→int).
        Reads result[2] (0.0421 float) as model → 'unknown' (not a string).
        """
        result = ("generated code", False, 0.0421, "claude-sonnet-4-6")

        actual_cost = _extract_cost_from_result('generate', result)
        model_name = _extract_model_from_result('generate', result)

        assert actual_cost == pytest.approx(0.0421), (
            f"generate log cost should be {result[2]} but got {actual_cost}. "
            f"result[1] = {result[1]!r} (was_incremental bool) was misread as cost."
        )
        assert model_name == "claude-sonnet-4-6", (
            f"generate log model should be '{result[3]}' but got '{model_name}'. "
            f"result[2] = {result[2]!r} (cost float) was misread as model."
        )

    def test_crash_logging_cost_and_model(self):
        """crash: cost should be result[4], model should be result[5].

        Bug: Reads result[1] (final_code str) as cost → 0.0 (isinstance fails).
        Reads result[2] (final_program str) as model → uses wrong string.
        """
        result = (True, "code content", "program content", 2, 0.0315, "gpt-4o-mini")

        actual_cost = _extract_cost_from_result('crash', result)
        model_name = _extract_model_from_result('crash', result)

        assert actual_cost == pytest.approx(0.0315), (
            f"crash log cost should be {result[4]} but got {actual_cost}."
        )
        assert model_name == "gpt-4o-mini", (
            f"crash log model should be '{result[5]}' but got '{model_name}'. "
            f"result[2] = {result[2]!r} (final_program string) was misread as model."
        )

    def test_fix_logging_cost_and_model(self):
        """fix: cost should be result[4], model should be result[5].

        Bug: Reads result[1] (fixed_unit_test str) as cost → 0.0 (isinstance fails).
        Reads result[2] (fixed_code str) as model → uses wrong string.
        """
        result = (True, "fixed test code", "fixed source code", 3, 0.0892, "claude-sonnet-4-6")

        actual_cost = _extract_cost_from_result('fix', result)
        model_name = _extract_model_from_result('fix', result)

        assert actual_cost == pytest.approx(0.0892), (
            f"fix log cost should be {result[4]} but got {actual_cost}."
        )
        assert model_name == "claude-sonnet-4-6", (
            f"fix log model should be '{result[5]}' but got '{model_name}'. "
            f"result[2] = {result[2]!r} (fixed_code string) was misread as model."
        )

    def test_verify_logging_cost_and_model(self):
        """verify: cost should be result[4], model should be result[5].

        Bug: Reads result[1] (final_program str) as cost → 0.0 (isinstance fails).
        Reads result[2] (final_code str) as model → uses wrong string.
        """
        result = (True, "program content", "code content", 1, 0.0267, "gpt-4o-mini")

        actual_cost = _extract_cost_from_result('verify', result)
        model_name = _extract_model_from_result('verify', result)

        assert actual_cost == pytest.approx(0.0267), (
            f"verify log cost should be {result[4]} but got {actual_cost}."
        )
        assert model_name == "gpt-4o-mini", (
            f"verify log model should be '{result[5]}' but got '{model_name}'. "
            f"result[2] = {result[2]!r} (final_code string) was misread as model."
        )


class TestBoolSubclassesIntQuirk:
    """Test that bool values are not silently accepted as cost values.

    Python's bool subclasses int: isinstance(False, int) is True.
    For generate, result[1] = was_incremental (bool). The fixed helper
    explicitly excludes bool with `not isinstance(val, bool)`.
    """

    def test_bool_false_not_accepted_as_cost(self):
        """The fix must reject bool values — generate's was_incremental should not sneak through.

        When was_incremental=False, the old code set cost to 0 (int value of False).
        The fix reads index 2 instead.
        """
        # generate 4-tuple: (content, was_incremental, cost, model)
        result = ("generated code", False, 0.0421, "claude-sonnet-4-6")

        cost = _extract_cost_from_result('generate', result)

        assert not isinstance(cost, bool), (
            f"Cost = {cost!r} is a bool (was_incremental), not a real cost value."
        )
        assert cost == pytest.approx(0.0421), (
            f"Cost should be {result[2]} but got {cost}."
        )

    def test_bool_true_not_misread_as_cost_one_dollar(self):
        """When was_incremental=True, the fix must NOT record cost as $1.00.

        True == 1 in Python, so float(True) = 1.0. The old code would record
        an incremental generate that costs $0.0053 as costing $1.00.
        """
        # generate 4-tuple with was_incremental=True
        result = ("generated code", True, 0.0053, "gpt-4o-mini")

        cost = _extract_cost_from_result('generate', result)

        assert cost == pytest.approx(0.0053), (
            f"Cost should be {result[2]} but got {cost} (True → int 1). "
            f"was_incremental=True was interpreted as cost=$1.00."
        )


class TestRegressionGuards:
    """Ensure operations that already extract cost correctly continue to work.

    These operations have cost at index 1, model at index 2:
    - example: (content, cost, model) — 3-tuple
    - test: (content, cost, model, agentic_success) — 4-tuple
    - test_extend: (content, cost, model, agentic_success) — 4-tuple
    """

    def test_example_cost_extraction(self):
        """example returns (content, cost, model) — cost at index 1 works correctly."""
        result = ("example content", 0.0023, "gpt-4o-mini")

        cost = _extract_cost_from_result('example', result)
        model = _extract_model_from_result('example', result)

        assert cost == pytest.approx(0.0023)
        assert model == "gpt-4o-mini"

    def test_test_cost_extraction(self):
        """test returns (content, cost, model, agentic_success) — cost at index 1 works correctly."""
        result = ("test content", 0.0078, "claude-sonnet-4-6", True)

        cost = _extract_cost_from_result('test', result)
        model = _extract_model_from_result('test', result)

        assert cost == pytest.approx(0.0078)
        assert model == "claude-sonnet-4-6"

    def test_test_extend_cost_extraction(self):
        """test_extend returns same format as test — cost at index 1 works correctly."""
        result = ("test content", 0.0045, "gpt-4o-mini", False)

        cost = _extract_cost_from_result('test_extend', result)
        model = _extract_model_from_result('test_extend', result)

        assert cost == pytest.approx(0.0045)
        assert model == "gpt-4o-mini"


class TestBudgetAccumulationAllOperations:
    """E2E test: budget accumulation across all operation types in a sync loop.

    With the bug, generate/crash/fix/verify costs are lost or wrong,
    so the total accumulated cost is much lower than actual spend.
    """

    def test_total_budget_with_all_operations(self):
        """Simulate sync loop with all 6 operations — total cost should sum correctly.

        With the old bug:
        - example: 0.01 (correct)
        - generate: 0 (was_incremental=False → bool treated as 0)
        - crash: 0.0 (string at [1] fails isinstance)
        - test: 0.02 (correct)
        - fix: 0.0 (string at [1] fails isinstance)
        - verify: 0.0 (string at [1] fails isinstance)
        Buggy total: ~0.03 instead of 0.23
        """
        operations_and_results = [
            ('example', ("content", 0.01, "gpt-4o-mini")),
            ('generate', ("code", False, 0.05, "claude-sonnet-4-6")),
            ('crash', (True, "code", "program", 2, 0.03, "gpt-4o-mini")),
            ('test', ("tests", 0.02, "gpt-4o-mini", True)),
            ('fix', (True, "fixed test", "fixed code", 1, 0.08, "claude-sonnet-4-6")),
            ('verify', (True, "program", "code", 1, 0.04, "gpt-4o-mini")),
        ]

        expected_total = 0.01 + 0.05 + 0.03 + 0.02 + 0.08 + 0.04  # = 0.23

        current_cost = 0.0
        for operation, result in operations_and_results:
            cost = _extract_cost_from_result(operation, result)
            current_cost += cost

        assert current_cost == pytest.approx(expected_total), (
            f"Total cost should be ${expected_total:.2f} but got ${current_cost:.4f}. "
            f"generate/crash/fix/verify costs are lost due to wrong tuple index."
        )


class TestOperationLogDecoratorBug:
    """Test the identical bug fix in operation_log.py:339-340.

    The log_operation decorator now uses the same _extract_cost_from_result and
    _extract_model_from_result helpers, fixing the operation-specific dispatch.
    """

    def test_generate_decorator_extraction(self):
        """Decorator reads correct index for generate: cost at [2], model at [3]."""
        result = ("generated code", False, 0.0421, "claude-sonnet-4-6")

        cost = _extract_cost_from_result('generate', result)
        model = _extract_model_from_result('generate', result)

        assert cost == pytest.approx(0.0421), (
            f"Decorator cost for generate should be {result[2]} but got {cost}. "
            f"result[1] = {result[1]!r} (bool) was cast to float."
        )
        assert model == "claude-sonnet-4-6", (
            f"Decorator model for generate should be '{result[3]}' but got '{model}'."
        )

    def test_fix_decorator_extraction(self):
        """Decorator reads correct index for fix: cost at [4], model at [5]."""
        result = (True, "fixed test code", "fixed source code", 3, 0.0892, "claude-sonnet-4-6")

        cost = _extract_cost_from_result('fix', result)
        model = _extract_model_from_result('fix', result)

        assert cost == pytest.approx(0.0892), (
            f"Decorator cost for fix should be {result[4]} but got {cost}."
        )
        assert model == "claude-sonnet-4-6", (
            f"Decorator model for fix should be '{result[5]}' but got '{model}'."
        )
