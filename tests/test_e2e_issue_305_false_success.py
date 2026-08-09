"""
E2E Test for Issue #305: False success reporting when LLM call fails during pdd verify.

This test exercises the full verify loop path to verify that when an LLM call fails
(e.g., "Insufficient credits", API timeout), the system correctly reports failure
instead of falsely claiming success with "0 verification issues found".

The bug (now fixed): When the cloud endpoint times out and local LLM fails with an
exception, `fix_verification_errors()` was returning `verification_issues_count: 0`
instead of `-1`. The loop checks for `-1` to detect errors, so `0` was misinterpreted
as "0 issues = success".

The fix: All error paths in fix_verification_errors.py now return
`verification_issues_count: -1` to signal an error state.

These E2E tests verify the fix is working by:
1. Mocking only the llm_invoke function (not fix_verification_errors itself)
2. Simulating LLM failures (exceptions)
3. Verifying fix_verification_errors returns -1 and the loop reports failure

All tests PASS when the fix is correctly applied.
"""

import pytest
from pathlib import Path
from unittest.mock import patch


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory for all tests in this module."""
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


class TestVerifyLoopFalseSuccessE2E:
    """
    E2E tests for Issue #305: Verify loop correctly handles LLM failures.

    These tests exercise the full fix_verification_errors_loop path with minimal mocking:
    - Real file I/O
    - Real loop logic
    - Real fix_verification_errors function (not mocked)
    - Only mock llm_invoke to simulate LLM failures

    After the fix is applied to fix_verification_errors.py, all error paths return
    verification_issues_count: -1, which the loop correctly detects as an error.

    All tests PASS when the fix is correctly applied.
    """

    def test_llm_error_returns_negative_one_and_loop_fails(self, tmp_path, monkeypatch):
        """
        E2E Test for Issue #305: Verify that when LLM call fails, fix_verification_errors
        returns -1 (error signal) and the loop correctly reports failure.

        This test exercises the REAL fix_verification_errors function (not mocked) through
        the loop, with only the LLM calls mocked to simulate failure scenarios.

        After the fix is applied to fix_verification_errors.py:
        1. Initial assessment succeeds, finds 2 issues
        2. In the fix loop, LLM call fails (e.g., "Insufficient credits")
        3. fix_verification_errors returns -1 (the fix)
        4. Loop detects -1 as error signal and reports failure

        This test PASSES when the fix is correctly applied.
        """
        from pdd.fix_verification_errors_loop import fix_verification_errors_loop
        from pdd.fix_verification_errors import VerificationOutput

        # Create real test files in tmp_path
        program_content = '''
# Test program that exercises the code module
from code_module import hello
print(hello())
'''
        code_content = '''
def hello():
    return "Hello, World!"
'''
        verification_program_content = '''
# Simple verification program
import sys
sys.exit(0)  # Always pass for this test
'''
        prompt_content = "Write a hello world function"

        program_file = tmp_path / "program.py"
        code_file = tmp_path / "code_module.py"
        verification_file = tmp_path / "verify_program.py"
        prompt_file = tmp_path / "prompt.txt"
        log_file = tmp_path / "verification.log"

        program_file.write_text(program_content)
        code_file.write_text(code_content)
        verification_file.write_text(verification_program_content)
        prompt_file.write_text(prompt_content)

        monkeypatch.chdir(tmp_path)

        # Track LLM call sequence
        llm_call_count = [0]

        def mock_llm_invoke(**kwargs):
            """
            Mock the LLM invoke to simulate:
            - First call (initial assessment): Succeeds, finds 2 issues
            - Second call (in loop): Fails with "Insufficient credits" exception

            This tests the REAL fix_verification_errors exception handling path.
            """
            llm_call_count[0] += 1

            if llm_call_count[0] == 1:
                # Initial assessment succeeds, finds 2 issues
                return {
                    'result': VerificationOutput(issues_count=2, details="Found 2 issues: missing import and incorrect return value"),
                    'cost': 0.01,
                    'model_name': 'test-model'
                }
            else:
                # Subsequent calls fail with "Insufficient credits"
                raise Exception("Insufficient credits")

        # Mock only llm_invoke to simulate LLM failures, let fix_verification_errors run for real
        with patch('pdd.fix_verification_errors.llm_invoke', side_effect=mock_llm_invoke):
            result = fix_verification_errors_loop(
                program_file=str(program_file),
                code_file=str(code_file),
                prompt=prompt_content,
                prompt_file=str(prompt_file),
                verification_program=str(verification_file),
                strength=0.5,
                temperature=0.0,
                max_attempts=3,
                budget=5.0,
                verification_log_file=str(log_file),
                verbose=False,
                agentic_fallback=False,  # Disable to test core loop behavior
            )

        # After the fix: fix_verification_errors returns -1 on LLM exception,
        # and the loop correctly detects this as an error and reports failure
        assert result["success"] == False, (
            f"Loop should report failure when fix_verification_errors returns -1 error signal.\n"
            f"This verifies the fix for GitHub issue #305 is working correctly.\n"
            f"Result: {result}"
        )

    def test_initial_assessment_llm_failure_returns_error(self, tmp_path, monkeypatch):
        """
        E2E Test for Issue #305: Verify initial assessment LLM failure is handled correctly.

        This test simulates the exact scenario from the bug report where the very first
        LLM call fails (e.g., cloud times out, local fails with "Insufficient credits").

        After the fix:
        1. LLM call fails immediately with "Insufficient credits"
        2. fix_verification_errors returns -1 (error signal)
        3. Loop detects error in initial assessment
        4. Loop reports failure appropriately

        This test PASSES when the fix is correctly applied.
        """
        from pdd.fix_verification_errors_loop import fix_verification_errors_loop

        # Create test files
        program_file = tmp_path / "program.py"
        code_file = tmp_path / "code.py"
        verification_file = tmp_path / "verify.py"
        prompt_file = tmp_path / "prompt.txt"
        log_file = tmp_path / "verify.log"

        program_file.write_text("print('test')")
        code_file.write_text("# test code")
        verification_file.write_text("import sys; sys.exit(0)")
        prompt_file.write_text("test prompt")

        monkeypatch.chdir(tmp_path)

        def mock_llm_invoke_fails(**kwargs):
            """
            Simulates the exact scenario from issue #305:
            - LLM call fails (e.g., "Insufficient credits")

            This tests the REAL fix_verification_errors exception handling.
            """
            raise Exception("Insufficient credits")

        # Mock only llm_invoke, let fix_verification_errors run for real
        with patch('pdd.fix_verification_errors.llm_invoke', side_effect=mock_llm_invoke_fails):
            result = fix_verification_errors_loop(
                program_file=str(program_file),
                code_file=str(code_file),
                prompt="test prompt",
                prompt_file=str(prompt_file),
                verification_program=str(verification_file),
                strength=1.0,  # Same as in bug report
                temperature=0.0,  # Same as in bug report
                max_attempts=3,
                budget=5.0,
                verification_log_file=str(log_file),
                verbose=False,
                use_cloud=False,
                agentic_fallback=False,
            )

        # After the fix: fix_verification_errors returns -1 on LLM exception,
        # and the loop correctly detects this as an error in initial assessment
        assert result["success"] == False, (
            f"Loop should report failure when initial LLM call fails.\n"
            f"This verifies the fix for GitHub issue #305 is working correctly.\n"
            f"Result: {result}"
        )

    def test_correct_error_signal_stops_loop(self, tmp_path, monkeypatch):
        """
        E2E Test: Verifies the EXPECTED behavior after the fix is applied.

        After the fix:
        - fix_verification_errors returns verification_issues_count: -1 on error
        - The loop checks `current_issues_count == -1` and detects the error
        - Loop correctly reports failure

        This test verifies the loop correctly handles the -1 error signal.
        """
        from pdd.fix_verification_errors_loop import fix_verification_errors_loop

        program_file = tmp_path / "program.py"
        code_file = tmp_path / "code.py"
        verification_file = tmp_path / "verify.py"
        prompt_file = tmp_path / "prompt.txt"
        log_file = tmp_path / "verify.log"

        program_file.write_text("print('test')")
        code_file.write_text("# code")
        verification_file.write_text("import sys; sys.exit(0)")
        prompt_file.write_text("prompt")

        monkeypatch.chdir(tmp_path)

        call_count = [0]

        def mock_fix_returns_correct_error_signal(**kwargs):
            """
            After the fix is applied, fix_verification_errors should return -1 on error.
            This test verifies the loop correctly handles that signal.
            """
            call_count[0] += 1

            if call_count[0] == 1:
                # Initial assessment works
                return {
                    "explanation": "Found issues",
                    "fixed_program": kwargs.get("program", ""),
                    "fixed_code": kwargs.get("code", ""),
                    "total_cost": 0.01,
                    "model_name": "test-model",
                    "verification_issues_count": 2,
                }
            else:
                # Subsequent call returns CORRECT error signal (-1)
                # This is the EXPECTED behavior after the fix is applied
                return {
                    "explanation": None,
                    "fixed_program": kwargs.get("program", ""),
                    "fixed_code": kwargs.get("code", ""),
                    "total_cost": 0.0,
                    "model_name": None,
                    "verification_issues_count": -1,  # CORRECT ERROR SIGNAL
                }

        with patch('pdd.fix_verification_errors_loop.fix_verification_errors', side_effect=mock_fix_returns_correct_error_signal):
            result = fix_verification_errors_loop(
                program_file=str(program_file),
                code_file=str(code_file),
                prompt="test",
                prompt_file=str(prompt_file),
                verification_program=str(verification_file),
                strength=0.5,
                temperature=0.0,
                max_attempts=3,
                budget=5.0,
                verification_log_file=str(log_file),
                verbose=False,
                agentic_fallback=False,
            )

        # Loop should detect -1 error signal and report failure
        assert result["success"] == False, (
            f"Loop should report failure when fix_verification_errors returns -1 error signal.\n"
            f"This test verifies the loop's error detection at line 815 works correctly.\n"
            f"Result: {result}"
        )

        # Status should indicate error
        status_msg = result.get("statistics", {}).get("status_message", "")
        assert "Error" in status_msg or "invalid" in status_msg.lower(), (
            f"Status message should indicate error state. Got: '{status_msg}'"
        )

    def test_exception_propagation_also_reports_failure(self, tmp_path, monkeypatch):
        """
        E2E Test: When exceptions propagate (not caught internally), loop should fail.

        This is a separate code path from the bug. When fix_verification_errors
        raises an exception instead of catching it, the loop has its own try/except
        that should handle it.
        """
        from pdd.fix_verification_errors_loop import fix_verification_errors_loop

        program_file = tmp_path / "program.py"
        code_file = tmp_path / "code.py"
        verification_file = tmp_path / "verify.py"
        prompt_file = tmp_path / "prompt.txt"
        log_file = tmp_path / "verify.log"

        program_file.write_text("print('test')")
        code_file.write_text("# code")
        verification_file.write_text("import sys; sys.exit(0)")
        prompt_file.write_text("prompt")

        monkeypatch.chdir(tmp_path)

        call_count = [0]

        def mock_fix_raises_exception(**kwargs):
            """Simulates an exception that propagates (not caught internally)."""
            call_count[0] += 1
            if call_count[0] == 1:
                # Initial assessment works
                return {
                    "explanation": "Found issues",
                    "fixed_program": kwargs.get("program", ""),
                    "fixed_code": kwargs.get("code", ""),
                    "total_cost": 0.01,
                    "model_name": "test-model",
                    "verification_issues_count": 2,
                }
            else:
                # Exception propagates (different from the bug where it's caught)
                raise Exception("API Error: Service unavailable")

        with patch('pdd.fix_verification_errors_loop.fix_verification_errors', side_effect=mock_fix_raises_exception):
            result = fix_verification_errors_loop(
                program_file=str(program_file),
                code_file=str(code_file),
                prompt="test",
                prompt_file=str(prompt_file),
                verification_program=str(verification_file),
                strength=0.5,
                temperature=0.0,
                max_attempts=3,
                budget=5.0,
                verification_log_file=str(log_file),
                verbose=False,
                agentic_fallback=False,
            )

        # Must not report success when exception occurred
        assert result["success"] == False, (
            f"Should not report success when exception propagated.\n"
            f"Result: {result}"
        )
