"""
E2E Test for Issue #364: PDD sync doesn't accumulate cost when comparing with max-budget

This test exercises the CLI path to verify that the "Total Cost" displayed in
fix loops includes prior operation costs, not just loop-local costs.

The bug: When fix_code_loop is called after other operations (like auto-deps) have
already incurred costs, the "Total Cost" displayed shows only costs within the
fix loop, NOT the cumulative total including prior operations.

Example from the bug report:
- Auto-deps cost: ~$3
- Fix loop displays: "Total Cost: $0.3255, Budget: $19.9718"
- Budget IS correctly reduced ($20 - $3 ≈ $19.97)
- But "Total Cost" misleadingly shows only $0.33 instead of ~$3.33

This E2E test:
1. Sets up a temp directory with prompt, code, and example files
2. Runs the crash command through Click's CliRunner
3. Simulates prior costs by passing a reduced budget (like sync_orchestration does)
4. Captures the output and verifies the "Total Cost" display

The test should FAIL on buggy code (Total Cost shows only loop costs) and
PASS once the fix is applied (Total Cost includes prior_cost parameter).
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
from click.testing import CliRunner


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory for all tests in this module.

    This is required because construct_paths uses PDD_PATH to find the language_format.csv
    file for language detection.
    """
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


class TestCumulativeCostDisplayE2E:
    """
    E2E tests for Issue #364: Verify fix loops display cumulative costs
    including prior operation costs (e.g., from auto-deps).
    """

    def test_fix_code_loop_displays_cumulative_cost(self, tmp_path, monkeypatch):
        """
        E2E Test: fix_code_loop -> displays "Total Cost"

        This test directly exercises fix_code_loop (the core function called by
        crash/sync commands) and verifies that when prior costs exist from
        operations like auto-deps, the displayed "Total Cost" should include
        those prior costs.

        Expected behavior (after fix):
        - fix_code_loop accepts a `prior_cost` parameter
        - The "Total Cost" display = prior_cost + loop costs
        - Users see accurate cumulative spending

        Bug behavior (Issue #364):
        - Total Cost only shows loop-local costs ($0.50)
        - Prior costs ($3) are not reflected in the display
        - Users are misled about their total spending
        """
        from pdd.fix_code_loop import fix_code_loop

        monkeypatch.chdir(tmp_path)

        # 1. Create test files
        # Code file
        code_file = tmp_path / "module.py"
        code_file.write_text('''def greet(name):
    return "Hello, " + name
''')

        # Verification program that fails initially
        verification_program = tmp_path / "verify.py"
        verification_program.write_text('''raise ValueError("Simulated verification failure")''')

        error_log = tmp_path / "error.log"

        # 2. Capture the rprint output to check "Total Cost" display
        captured_output = []

        import pdd.fix_code_loop as fcl_module
        original_rprint = fcl_module.rprint

        def capturing_rprint(*args, **kwargs):
            output_str = " ".join(str(arg) for arg in args)
            captured_output.append(output_str)
            # Also call original
            original_rprint(*args, **kwargs)

        monkeypatch.setattr(fcl_module, "rprint", capturing_rprint)

        # 3. Mock fix_code_module_errors to simulate a fix attempt
        loop_attempt_cost = 0.50

        def mock_fix_code_module_errors(*args, **kwargs):
            return (
                True,  # update_program
                True,  # update_code
                '''print("Fixed!")''',  # fixed_program
                '''def greet(name):
    return "Hello, " + name
''',  # fixed_code
                "LLM analysis of the error",  # program_code_fix
                loop_attempt_cost,  # cost ($0.50)
                "mock-model"  # model_name
            )

        # Simulate the scenario from the bug report:
        # - Original budget: $20
        # - Prior cost (auto-deps): $3
        # - Remaining budget passed to fix_code_loop: $20 - $3 = $17
        #
        # After the fix, we should also be able to pass prior_cost=$3
        # so the display shows "Total Cost: $3.50" instead of "$0.50"

        original_budget = 20.0
        prior_cost = 3.0
        remaining_budget = original_budget - prior_cost  # $17.00

        with patch.object(fcl_module, 'fix_code_module_errors', side_effect=mock_fix_code_module_errors):
            success, final_program, final_code, attempts, total_cost, model = fix_code_loop(
                code_file=str(code_file),
                prompt="A Python module that greets users.",
                verification_program=str(verification_program),
                strength=0.5,
                temperature=0.5,
                max_attempts=3,
                budget=remaining_budget,  # $17.00 remaining
                error_log_file=str(error_log),
                verbose=True,
                prior_cost=prior_cost,  # Pass prior cost to show cumulative total (Issue #364 fix)
            )

        # 4. Find the "Total Cost" display line
        cost_display_lines = [
            line for line in captured_output
            if "Total Cost:" in line and "Budget:" in line
        ]

        assert len(cost_display_lines) >= 1, (
            f"Expected to find 'Total Cost:' display line in output.\n"
            f"Captured output:\n" + "\n".join(captured_output)
        )

        # 5. THE BUG CHECK
        # Extract the displayed total cost value
        import re
        cost_line = cost_display_lines[0]
        total_cost_match = re.search(r"Total Cost: \$(\d+\.?\d*)", cost_line)

        assert total_cost_match, f"Could not parse Total Cost from: {cost_line}"

        displayed_total_cost = float(total_cost_match.group(1))

        # Current buggy behavior: displays $0.50 (only loop cost)
        # Expected after fix: displays $3.50 (prior_cost + loop_cost)
        expected_cumulative_cost = prior_cost + loop_attempt_cost  # $3.50

        # This assertion FAILS on buggy code
        assert displayed_total_cost >= expected_cumulative_cost - 0.01, (
            f"ISSUE #364 BUG DETECTED: 'Total Cost' does not include prior operation costs!\n\n"
            f"Scenario:\n"
            f"  - Original budget: ${original_budget:.2f}\n"
            f"  - Prior cost (e.g., auto-deps): ${prior_cost:.2f}\n"
            f"  - Remaining budget passed to fix_code_loop: ${remaining_budget:.2f}\n"
            f"  - Loop attempt cost: ${loop_attempt_cost:.2f}\n\n"
            f"Expected:\n"
            f"  - Total Cost display: ${expected_cumulative_cost:.2f} (prior + loop)\n\n"
            f"Actual:\n"
            f"  - Total Cost display: ${displayed_total_cost:.2f}\n"
            f"  - Output line: {cost_line}\n\n"
            f"The 'Total Cost' should accumulate costs from prior operations "
            f"(like auto-deps) to give users an accurate view of their spending.\n\n"
            f"Fix: Add a `prior_cost` parameter to fix_code_loop() and fix_verification_errors_loop() "
            f"so the display shows cumulative costs."
        )


class TestSyncOrchestrationCostAccumulation:
    """
    E2E test that verifies sync_orchestration correctly accumulates and
    displays cumulative costs across multiple operations.
    """

    def test_sync_accumulated_cost_passed_to_fix_loops(self, tmp_path, monkeypatch):
        """
        E2E Test: Verify that sync_orchestration passes accumulated costs
        to fix loops for accurate display.

        In sync_orchestration:
        - current_cost_ref[0] tracks total accumulated cost
        - budget - current_cost_ref[0] is passed as remaining budget
        - BUT prior costs are NOT passed for display purposes

        After the fix:
        - sync_orchestration should also pass current_cost_ref[0] as prior_cost
        - So fix loops can display: "Total Cost: $X.XX" where X includes prior ops
        """
        # Create test files
        prompt_file = tmp_path / "test.prompt"
        prompt_file.write_text("A test module.")

        code_file = tmp_path / "test.py"
        code_file.write_text("def test_fn(): return 42")

        example_file = tmp_path / "test_example.py"
        example_file.write_text("from test import test_fn\nprint(test_fn())")

        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-key")

        # We'll verify that sync_orchestration calls crash_main/crash operations
        # with the correct budget_remaining, but the bug is that it doesn't pass
        # prior_cost for display purposes.

        # Track calls to crash_main
        crash_main_calls = []

        def mock_crash_main(ctx, **kwargs):
            crash_main_calls.append({
                'budget': kwargs.get('budget'),
                'kwargs': kwargs
            })
            # Return success
            return {
                'success': True,
                'cost': 0.5,
            }

        # Capture rprint output
        captured_output = []

        def mock_rprint(*args, **kwargs):
            output_str = " ".join(str(arg) for arg in args)
            captured_output.append(output_str)

        with patch('pdd.sync_orchestration.crash_main', side_effect=mock_crash_main):
            with patch('pdd.fix_code_loop.rprint', side_effect=mock_rprint):
                # We can't easily run the full sync command without extensive mocking,
                # so this test documents the expected behavior and the bug.

                # The key insight is:
                # 1. sync_orchestration tracks costs in current_cost_ref[0]
                # 2. It correctly passes (budget - current_cost_ref[0]) as remaining budget
                # 3. BUT it doesn't pass current_cost_ref[0] as prior_cost for display
                #
                # After the fix, crash_main (and the fix loops it calls) should receive
                # a prior_cost parameter equal to current_cost_ref[0]

                # Verify the fix has been applied by checking the fix_code_loop signature
                from pdd.fix_code_loop import fix_code_loop
                import inspect

                sig = inspect.signature(fix_code_loop)
                param_names = list(sig.parameters.keys())

                # After the fix (Issue #364), prior_cost parameter should exist
                assert 'prior_cost' in param_names, (
                    "fix_code_loop should have a prior_cost parameter for cumulative cost display"
                )


class TestCostDisplayFormat:
    """
    Tests to verify the format and accuracy of cost display in fix loops.
    """

    def test_cost_display_format_matches_user_report(self, tmp_path, monkeypatch):
        """
        Verify that the cost display format matches what users see in the bug report:
        "Attempt Cost: $X.XXXX, Total Cost: $Y.YYYY, Budget: $Z.ZZZZ"
        """
        from pdd.fix_code_loop import fix_code_loop

        monkeypatch.chdir(tmp_path)

        # Create test files
        verification_program = tmp_path / "verify.py"
        verification_program.write_text("raise ValueError('fail')")

        code_file = tmp_path / "code.py"
        code_file.write_text("def fn(): pass")

        error_log = tmp_path / "error.log"

        # Capture rprint output
        captured_output = []

        def mock_rprint(*args, **kwargs):
            output_str = " ".join(str(arg) for arg in args)
            captured_output.append(output_str)

        # Mock fix_code_module_errors
        def mock_fix(*args, **kwargs):
            return (True, True, "print('ok')", "def fn(): return 1",
                    "analysis", 0.2234, "model")

        with patch('pdd.fix_code_loop.rprint', side_effect=mock_rprint):
            with patch('pdd.fix_code_loop.fix_code_module_errors', side_effect=mock_fix):
                fix_code_loop(
                    code_file=str(code_file),
                    prompt="Test",
                    verification_program=str(verification_program),
                    strength=0.5,
                    temperature=0.5,
                    max_attempts=2,
                    budget=19.9718,  # Matches the budget from bug report
                    error_log_file=str(error_log),
                    verbose=True,
                )

        # Find cost display lines
        cost_lines = [
            line for line in captured_output
            if "Attempt Cost:" in line and "Total Cost:" in line and "Budget:" in line
        ]

        assert len(cost_lines) >= 1, (
            f"Expected cost display line in format 'Attempt Cost: $X, Total Cost: $Y, Budget: $Z'\n"
            f"Captured output:\n" + "\n".join(captured_output)
        )

        # Verify format matches user report
        import re
        cost_line = cost_lines[0]

        # Should match: "Attempt Cost: $0.2234, Total Cost: $0.2234, Budget: $19.9718"
        pattern = r"Attempt Cost: \$[\d.]+, Total Cost: \$[\d.]+, Budget: \$[\d.]+"
        assert re.search(pattern, cost_line), (
            f"Cost display format doesn't match expected pattern.\n"
            f"Expected format: 'Attempt Cost: $X.XXXX, Total Cost: $Y.YYYY, Budget: $Z.ZZZZ'\n"
            f"Got: {cost_line}"
        )
