"""
E2E regression tests for Issue #485: Warning count causes false Success:False and
unnecessary agentic fallback.

These tests exercise the full code path from pytest subprocess execution through
warning counting to success determination. They create real test files that pass but
trigger Python warnings (via warnings.warn) or emit warning-like strings in stdout,
which pytest displays in its output.

Historically, the naive `.lower().count("warning")` in pytest_output.py counted these
non-pytest framework warnings, causing false failure. These tests now serve as
regression coverage to ensure the fixed warning-counting logic continues to treat
such output correctly and does not reintroduce the original Issue #485 behavior.
"""

import textwrap
from unittest.mock import patch


class TestIssue485WarningFalseNegativeE2E:
    """
    E2E tests verifying that Python warnings in subprocess output don't cause
    false test failures in the fix error loop.
    """

    def test_run_pytest_on_file_with_print_warnings_reports_zero_warnings(self, tmp_path):
        """
        E2E: Create a real test file that prints warning-like messages to stdout
        (mimicking library log output from LiteLLM, Pydantic, PDD logs), run it
        through run_pytest_on_file(), and verify warnings == 0.

        The buggy code's naive .count("warning") picks up any "warning" substring
        in stdout, including print() output that contains the word "warning".
        The fix parses only the pytest summary line for actual warning counts.
        """
        test_file = tmp_path / "test_calc.py"
        test_file.write_text(textwrap.dedent("""\
            def test_passes_but_prints_warning_strings():
                # These simulate real library log output that appears in captured stdout
                # (LiteLLM, Pydantic, PDD WARNING: log messages)
                print("WARNING: Cloud fallback triggered for model")
                print("UserWarning: LiteLLM has moved to using _client")
                print("PydanticSerializationUnexpectedValue warning raised")
                assert 1 + 1 == 2

            def test_also_passes():
                assert True
        """))

        from pdd.fix_error_loop import run_pytest_on_file

        failures, errors, warnings_count, logs = run_pytest_on_file(str(test_file))

        assert failures == 0, f"Expected 0 failures, got {failures}"
        assert errors == 0, f"Expected 0 errors, got {errors}"
        # BUG: The buggy code counts every "warning" substring in stdout.
        # Print output containing "warning" should not be counted as pytest warnings.
        assert warnings_count == 0, (
            f"Expected 0 warnings (printed warning-like strings should not be counted as "
            f"pytest framework warnings), got {warnings_count}. "
            f"This is the bug from issue #485: naive warning counting."
        )

    def test_fix_error_loop_success_with_python_warnings(self, tmp_path):
        """
        E2E: Run the full fix_error_loop on a passing test that emits Python warnings,
        and verify it returns success=True without triggering agentic fallback.

        This exercises the complete user-facing code path:
        subprocess pytest -> warnings.warn() displayed -> naive count -> success gate
        """
        test_file = tmp_path / "test_calc.py"
        test_file.write_text(textwrap.dedent("""\
            import warnings

            def test_add():
                warnings.warn("LiteLLM proxy deprecation", UserWarning)
                warnings.warn("Cloud fallback triggered", UserWarning)
                assert 2 + 2 == 4

            def test_subtract():
                assert 5 - 3 == 2
        """))

        code_file = tmp_path / "calc.py"
        code_file.write_text("def add(a, b): return a + b\ndef subtract(a, b): return a - b\n")

        prompt_file = tmp_path / "calc_python.prompt"
        prompt_file.write_text("Create a calculator with add and subtract\n")

        error_log = tmp_path / "error_log.txt"

        from pdd.fix_error_loop import fix_error_loop

        # Mock the LLM calls but let the pytest subprocess run for real
        with patch("pdd.fix_error_loop._safe_run_agentic_fix") as mock_agentic, \
             patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_llm:
            mock_agentic.return_value = (False, "not called", 0.0, "none", [])
            # Return unchanged files so the loop can iterate without real LLM
            test_content = test_file.read_text()
            code_content = code_file.read_text()
            mock_llm.return_value = (test_content, code_content, test_content, code_content, "no changes", 0.001, "mock")

            success, final_test, final_code, attempts, cost, model = fix_error_loop(
                unit_test_file=str(test_file),
                code_file=str(code_file),
                prompt_file=str(prompt_file),
                prompt="Create a calculator",
                verification_program="",
                strength=0.0,
                temperature=0.0,
                max_attempts=1,
                budget=0.01,
                error_log_file=str(error_log),
                agentic_fallback=False,
            )

        # BUG: The buggy code sets success=False because warnings > 0 from naive counting
        assert success is True, (
            "Expected success=True (all tests pass), but got False. "
            "This is the bug from issue #485: Python warnings cause false failure."
        )
        mock_agentic.assert_not_called()
