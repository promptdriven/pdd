import os
import shutil
import subprocess
import tempfile
import time
import pytest
from unittest.mock import patch, MagicMock

# Import the function under test
# Adjust the import below if your actual package or file structure is different.
from pdd.fix_code_loop import fix_code_loop, run_process_with_output

@pytest.fixture
def temp_workspace():
    """
    Creates a temporary directory for test files and cleans up afterward.
    """
    with tempfile.TemporaryDirectory() as tmpdir:
        current_dir = os.getcwd()
        try:
            os.chdir(tmpdir)
            yield tmpdir
        finally:
            os.chdir(current_dir)

def write_file(filename: str, content: str):
    """
    Helper to write content to a file.
    """
    with open(filename, "w", encoding="utf-8") as f:
        f.write(content)

def read_file(filename: str) -> str:
    """
    Helper to read and return content from a file.
    """
    with open(filename, "r", encoding="utf-8") as f:
        return f.read()

@pytest.mark.parametrize("verbose_flag", [True, False])
def test_fix_code_loop_runs_successfully_first_try(temp_workspace, verbose_flag):
    """
    Test that fix_code_loop immediately succeeds when the verification program
    runs without errors. No attempts to "fix" the code should be necessary.
    """
    # Create a dummy verification program that always succeeds
    verification_program_path = "verify_success.py"
    verification_program_text = """
print("Verification passed successfully.")
"""
    write_file(verification_program_path, verification_program_text)

    # Create a dummy code file (though it won't really be run in this scenario)
    code_file_path = "dummy_code.py"
    code_file_text = """
def dummy_function():
    return "OK"
"""
    write_file(code_file_path, code_file_text)

    # Call fix_code_loop
    success, final_program, final_code, total_attempts, total_cost, model_name = fix_code_loop(
        code_file=code_file_path,
        prompt="A dummy prompt",
        verification_program=verification_program_path,
        strength=0.5,
        temperature=0.5,
        max_attempts=3,
        budget=10.0,
        error_log_file="error_code.log",
        verbose=verbose_flag,
    )

    # Validate results
    assert success is True, "The code should have succeeded on the first try."
    assert total_attempts == 0, "No fix attempts should have been made."
    assert total_cost == 0.0, "No cost should be incurred."
    assert "Verification passed successfully." in final_program
    assert "def dummy_function()" in final_code

def test_fix_code_loop_missing_verification_program(temp_workspace):
    """
    Test that fix_code_loop returns an immediate False if the verification
    program does not exist.
    """
    # Create a code file
    code_file_path = "dummy_code.py"
    write_file(code_file_path, "print('Hello from code!')")

    # Provide a verification path that doesn't exist
    verification_program_path = "missing_verify.py"

    success, final_program, final_code, total_attempts, total_cost, model_name = fix_code_loop(
        code_file=code_file_path,
        prompt="Prompt that generated code",
        verification_program=verification_program_path,
        strength=0.5,
        temperature=0.5,
        max_attempts=3,
        budget=10.0,
        error_log_file="error_code.log",
        verbose=False,
    )

    # Validate results
    assert success is False, "Should fail immediately if verification program is missing."
    assert total_attempts == 0, "No attempts should have been made."
    assert total_cost == 0.0, "No cost should be incurred because fix was never called."
    assert final_program == "", "No final program should be returned on failure."
    assert final_code == "", "No final code should be returned on failure."

@patch("pdd.fix_code_loop.fix_code_module_errors")
def test_fix_code_loop_needs_fixing(mock_fix_code_module_errors, temp_workspace):
    """
    Test that fix_code_loop attempts to fix the code when the verification program
    fails. The mock of fix_code_module_errors simulates a single successful fix.
    """
    # Create an initial verification program that fails
    verification_program_path = "verification_fail.py"
    verification_program_text = """
import sys

# We simulate an error
raise ValueError("Simulated verification failure!")
"""
    write_file(verification_program_path, verification_program_text)

    # Create a code file that presumably has an error
    code_file_path = "erroneous_code.py"
    code_file_text = """
def troublesome_function():
    raise Exception("Something is wrong")
"""
    write_file(code_file_path, code_file_text)

    # Mock fix_code_module_errors to simulate a single fix
    def mock_fix(*args, **kwargs):
        return (True, True,  # update_program, update_code
                "print('Fixed verification!')",  # fixed_program
                "def troublesome_function(): return 'All good now!'",  # fixed_code
                "LLM analysis of the error and fix suggestions",  # program_code_fix
                0.5,  # cost
                "mock-model-v1"  # model_name
               )

    mock_fix_code_module_errors.side_effect = mock_fix

    success, final_program, final_code, total_attempts, total_cost, model_name = fix_code_loop(
        code_file=code_file_path,
        prompt="Prompt for code that doesn't work",
        verification_program=verification_program_path,
        strength=0.5,
        temperature=0.5,
        max_attempts=5,
        budget=10.0,
        error_log_file="error_code.log",
        verbose=True,
    )

    # Validate results
    assert success is True, "Should succeed after the mock fix is applied."
    # The function attempts once, sees the error, then calls mock fix, so total_attempts should be 1
    assert total_attempts == 1, "Expected exactly one fix attempt."
    assert total_cost == 0.5, "Cost should sum up to the value returned by the mock fix."
    assert "Fixed verification!" in final_program, "Expected the updated verification program."
    assert "All good now!" in final_code, "Expected the updated code content."
    assert model_name == "mock-model-v1", "Should return the mocked model name."

@patch("pdd.fix_code_loop.fix_code_module_errors")
def test_fix_code_loop_exceed_budget(mock_fix_code_module_errors, temp_workspace):
    """
    Test that fix_code_loop stops if the total cost exceeds the budget.
    We simulate multiple failed fixes that each add cost.
    """
    # Create a verification program that fails
    verification_program_path = "verification_fail_budget.py"
    verification_program_text = """
raise RuntimeError("Always fails")
"""
    write_file(verification_program_path, verification_program_text)

    # Create a code file that presumably needs fixes
    code_file_path = "expensive_code.py"
    code_file_text = """
def expensive_problem():
    raise Exception("Needs fixing")
"""
    write_file(code_file_path, code_file_text)

    # Update the mock so each "fix" is still broken (force a continued failure)
    # and each fix attempt costs 6.0
    def mock_fix(*args, **kwargs):
        return (
            True, 
            True,
            "raise RuntimeError('Still broken verification')",
            "def expensive_problem(): raise Exception('Still not fixed')",
            "Detailed error analysis from LLM",  # program_code_fix
            6.0,  # cost each time
            "expensive-model"
        )

    mock_fix_code_module_errors.side_effect = mock_fix

    success, final_program, final_code, total_attempts, total_cost, model_name = fix_code_loop(
        code_file=code_file_path,
        prompt="Prompt for an expensive fix",
        verification_program=verification_program_path,
        strength=0.5,
        temperature=0.5,
        max_attempts=5,
        budget=10.0,  # Will be exceeded on the second fix
        error_log_file="error_code.log",
        verbose=True,
    )

    # Validate results
    assert success is False, "Should fail because the budget was exceeded."
    # After the first failing attempt: cost=6.0; second attempt also fails -> cost=12.0 > budget
    assert total_attempts == 2, "Should make two fix attempts before exceeding the budget."
    assert total_cost > 10.0, "Total cost should exceed the original budget."
    assert model_name == "expensive-model", "Should report the model name from the mock."

    # Check that the code was restored to the original (since fix eventually failed)
    restored_verification = read_file(verification_program_path)
    restored_code = read_file(code_file_path)
    assert "Always fails" in restored_verification, "Original verification program should be restored."
    assert "Needs fixing" in restored_code, "Original code should be restored."
    
def test_fix_code_loop_exceed_max_attempts(temp_workspace):
    """
    Test that fix_code_loop stops if the maximum attempts are reached, even if
    the budget is not exceeded.
    We substitute a failing verification program and no real fix attempts.
    """

    verification_program_path = "verify_to_fail.py"
    write_file(
        verification_program_path,
        "print('Attempting verification...'); raise RuntimeError('It fails every time')"
    )

    code_file_path = "broken_code.py"
    write_file(
        code_file_path,
        "raise Exception('Code is broken')"
    )

    # We patch fix_code_module_errors to do nothing or return no changes repeatedly
    with patch("pdd.fix_code_loop.fix_code_module_errors") as mock_fix:
        # Always return no changes needed - to simulate repeated attempts with no improvement
        mock_fix.return_value = (False, False, "", "", "No changes recommended", 1.0, "mocked_model")

        success, final_program, final_code, total_attempts, total_cost, model_name = fix_code_loop(
            code_file=code_file_path,
            prompt="Prompt for broken code",
            verification_program=verification_program_path,
            strength=0.5,
            temperature=0.5,
            max_attempts=2,  # Limit attempts
            budget=100.0,    # Substantial budget, so we can check attempts
            error_log_file="error_code.log",
            verbose=False,
        )

        # After each failure, we see no changes needed => fix_code_loop should break immediately,
        # or continue until max_attempts if it tries to bypass "no changes" logic.
        # The code checks for "if not update_program and not update_code" => break immediately.
        # So we may see total_attempts = 1 with success=False if it tries once and sees no changes.
        # This test ensures it doesn't loop infinitely.
        assert success is False, "Should not succeed because errors were never fixed."
        assert total_attempts <= 2, "Should not exceed max_attempts."
        assert total_cost == pytest.approx(1.0, abs=1e-9), (
            "Expected cost is the sum from the single call to fix_code_module_errors."
        )
        assert model_name == "mocked_model", "Should capture the mocked model name."
        assert final_program == "", "Verification program was never updated."
        assert final_code == "", "Code was never updated."


class TestRunProcessWithOutputTimeout:
    """
    Tests for run_process_with_output to ensure thread joins have proper
    timeouts and don't hang indefinitely.

    Bug: Lines 152-153 in fix_code_loop.py had t_out.join() and t_err.join()
    without timeouts, causing indefinite hangs when subprocess doesn't properly
    close its pipes.
    """

    def test_thread_join_completes_when_subprocess_times_out(self):
        """
        Verify that run_process_with_output completes within reasonable time
        even when subprocess needs to be killed due to timeout.

        This test would hang indefinitely before the fix if thread joins
        don't have timeouts.
        """
        start_time = time.time()

        # Create a subprocess that runs longer than the timeout
        # Use unbuffered output (-u) and flush to ensure output is captured
        returncode, stdout, stderr = run_process_with_output(
            ["python", "-u", "-c",
             "import sys; print('start', flush=True); import time; time.sleep(60)"],
            timeout=2  # Short timeout - subprocess should be killed
        )

        elapsed = time.time() - start_time

        # Should complete within timeout + reasonable grace period for cleanup
        # Before fix: would hang forever
        # After fix: should complete within ~5-10 seconds max
        assert elapsed < 15, f"Function took {elapsed:.1f}s, expected < 15s (hung indefinitely before fix)"

        # Should have timeout indication or killed process
        assert returncode != 0 or "[Timeout]" in stderr, "Should indicate timeout or non-zero return"

    def test_normal_subprocess_still_works(self):
        """
        Verify that normal subprocesses that complete quickly still work correctly
        after adding thread join timeouts.
        """
        returncode, stdout, stderr = run_process_with_output(
            ["python", "-c", "print('hello'); import sys; print('error', file=sys.stderr)"],
            timeout=30
        )

        assert returncode == 0, f"Expected success, got returncode={returncode}"
        assert "hello" in stdout, f"Expected 'hello' in stdout, got: {stdout}"
        assert "error" in stderr, f"Expected 'error' in stderr, got: {stderr}"

    def test_subprocess_with_lots_of_output(self):
        """
        Verify thread handling works correctly when subprocess produces
        significant output that needs to be captured.
        """
        # Generate 1000 lines of output
        code = "for i in range(1000): print(f'line {i}')"
        returncode, stdout, stderr = run_process_with_output(
            ["python", "-c", code],
            timeout=30
        )

        assert returncode == 0, f"Expected success, got returncode={returncode}"
        assert "line 0" in stdout, "Should capture first line"
        assert "line 999" in stdout, "Should capture last line"

    def test_subprocess_that_fails_immediately(self):
        """
        Verify proper handling when subprocess fails immediately with error output.
        """
        returncode, stdout, stderr = run_process_with_output(
            ["python", "-c", "raise ValueError('test error')"],
            timeout=30
        )

        assert returncode != 0, "Should have non-zero return code for failed subprocess"
        assert "ValueError" in stderr or "test error" in stderr, \
            f"Should capture error in stderr, got: {stderr}"

    def test_subprocess_with_child_process_that_hangs(self):
        """
        Test that demonstrates the hang bug: when a subprocess spawns a child
        that inherits pipes but doesn't close them, thread joins hang forever.

        This test replicates the scenario where Claude CLI (or another tool)
        spawns background processes that keep the pipes open.

        Before fix: This test will hang indefinitely
        After fix: Should complete within timeout + grace period
        """
        start_time = time.time()

        # Create a subprocess that forks a child which inherits the pipes
        # The child sleeps forever, keeping pipes open even after parent exits
        code = '''
import os
import sys
import time

pid = os.fork()
if pid == 0:
    # Child process: keep pipes inherited and sleep forever
    time.sleep(3600)  # Sleep for 1 hour
else:
    # Parent: exit immediately
    print("parent done", flush=True)
    sys.exit(0)
'''
        returncode, stdout, stderr = run_process_with_output(
            ["python", "-c", code],
            timeout=2
        )

        elapsed = time.time() - start_time

        # If threads don't have timeouts, this will hang forever waiting
        # for the orphaned child to close the pipes
        # With timeout fix, should complete in ~15 seconds max
        assert elapsed < 20, (
            f"Function took {elapsed:.1f}s, expected < 20s. "
            "Thread joins likely hanging on inherited pipes from child process."
        )


class TestAgenticFallbackBugs:
    """
    Tests for agentic fallback bugs that were causing silent failures.

    Bug 1: _safe_run_agentic_crash was passing 'cwd' parameter to run_agentic_crash()
           but run_agentic_crash() doesn't accept that parameter, causing TypeError.

    Bug 2: The error message from failed agentic calls was being discarded (_msg)
           instead of being logged, making failures silent.
    """

    def test_safe_run_agentic_crash_does_not_pass_cwd(self):
        """
        Verify that _safe_run_agentic_crash doesn't pass 'cwd' to run_agentic_crash.

        Before fix: Would raise TypeError: run_agentic_crash() got an unexpected
                    keyword argument 'cwd'
        After fix: Should call run_agentic_crash without cwd parameter
        """
        from pdd.fix_code_loop import _safe_run_agentic_crash

        # Mock run_agentic_crash to capture what arguments it receives
        with patch('pdd.fix_code_loop.run_agentic_crash') as mock_run:
            mock_run.return_value = (True, "success", 0.0, "test-model", [])

            # Call with cwd parameter
            result = _safe_run_agentic_crash(
                prompt_file="/tmp/test.prompt",
                code_file="/tmp/test.py",
                program_file="/tmp/program.py",
                crash_log_file="/tmp/crash.log",
                cwd="/tmp"  # This should NOT be passed to run_agentic_crash
            )

            # Verify run_agentic_crash was called
            assert mock_run.called, "run_agentic_crash should have been called"

            # Verify 'cwd' was NOT in the call arguments
            call_kwargs = mock_run.call_args.kwargs
            assert 'cwd' not in call_kwargs, (
                f"'cwd' should not be passed to run_agentic_crash, but got kwargs: {call_kwargs}"
            )

    def test_safe_run_agentic_crash_returns_error_on_empty_prompt(self):
        """
        Verify that _safe_run_agentic_crash returns a proper error message
        when prompt_file is empty, not just silently failing.
        """
        from pdd.fix_code_loop import _safe_run_agentic_crash

        success, msg, cost, model, changed_files = _safe_run_agentic_crash(
            prompt_file="",  # Empty prompt file
            code_file="/tmp/test.py",
            program_file="/tmp/program.py",
            crash_log_file="/tmp/crash.log",
        )

        assert success is False, "Should fail with empty prompt_file"
        assert "prompt file" in msg.lower(), f"Error message should mention prompt file: {msg}"
        assert cost == 0.0, "No cost should be incurred"

    def test_safe_run_agentic_crash_captures_exception_message(self):
        """
        Verify that when run_agentic_crash raises an exception,
        the error message is captured and returned (not discarded).
        """
        from pdd.fix_code_loop import _safe_run_agentic_crash

        with patch('pdd.fix_code_loop.run_agentic_crash') as mock_run:
            # Simulate the old bug: TypeError from unexpected cwd argument
            mock_run.side_effect = TypeError("got an unexpected keyword argument 'cwd'")

            success, msg, cost, model, changed_files = _safe_run_agentic_crash(
                prompt_file="/tmp/test.prompt",
                code_file="/tmp/test.py",
                program_file="/tmp/program.py",
                crash_log_file="/tmp/crash.log",
            )

            assert success is False, "Should fail when exception is raised"
            assert "cwd" in msg or "failed" in msg.lower(), (
                f"Error message should contain exception info: {msg}"
            )


class TestAgenticVerifyFallbackBugs:
    """
    Tests for agentic verify fallback bugs.
    """

    def test_safe_run_agentic_verify_does_not_pass_cwd(self):
        """
        Verify that _safe_run_agentic_verify doesn't pass 'cwd' to run_agentic_verify.

        Before fix: Would raise TypeError: run_agentic_verify() got an unexpected
                    keyword argument 'cwd'
        After fix: Should call run_agentic_verify without cwd parameter
        """
        from pdd.fix_verification_errors_loop import _safe_run_agentic_verify

        with patch('pdd.fix_verification_errors_loop.run_agentic_verify') as mock_run:
            mock_run.return_value = (True, "success", 0.0, "test-model", [])

            result = _safe_run_agentic_verify(
                prompt_file="/tmp/test.prompt",
                code_file="/tmp/test.py",
                program_file="/tmp/program.py",
                verification_log_file="/tmp/verify.log",
                verbose=False,
                cwd="/tmp"  # This should NOT be passed to run_agentic_verify
            )

            assert mock_run.called, "run_agentic_verify should have been called"

            call_kwargs = mock_run.call_args.kwargs
            assert 'cwd' not in call_kwargs, (
                f"'cwd' should not be passed to run_agentic_verify, but got kwargs: {call_kwargs}"
            )

    def test_safe_run_agentic_verify_returns_error_on_empty_prompt(self):
        """
        Verify proper error message when prompt_file is empty.
        """
        from pdd.fix_verification_errors_loop import _safe_run_agentic_verify

        success, msg, cost, model, changed_files = _safe_run_agentic_verify(
            prompt_file="",
            code_file="/tmp/test.py",
            program_file="/tmp/program.py",
            verification_log_file="/tmp/verify.log",
        )

        assert success is False, "Should fail with empty prompt_file"
        assert "prompt file" in msg.lower(), f"Error message should mention prompt file: {msg}"


class TestBackupLocation:
    """
    Tests to verify that backup files (including example/program files) are stored
    in .pdd/backups/ instead of polluting the working directory.
    """

    @patch("pdd.fix_code_loop.fix_code_module_errors")
    def test_program_backup_stored_in_pdd_backups(self, mock_fix_code_module_errors, tmp_path, monkeypatch):
        """
        Test that when fix_code_loop runs, the verification program (example file)
        backups are stored in .pdd/backups/ and NOT in the working directory.

        This prevents versioned files like foo_example_1.py from polluting
        the examples directory and being picked up by glob patterns.
        """
        # Change to temp directory
        monkeypatch.chdir(tmp_path)

        # Create .pdd directory
        pdd_dir = tmp_path / ".pdd"
        pdd_dir.mkdir()

        # Create a verification program (simulating an example file)
        example_file = tmp_path / "my_module_example.py"
        example_file.write_text("print('Example that will fail')\nraise ValueError('fail')")

        # Create a code file
        code_file = tmp_path / "my_module.py"
        code_file.write_text("def my_func(): return 'broken'")

        # Mock fix_code_module_errors to simulate a fix attempt
        def mock_fix(*args, **kwargs):
            return (
                True, True,  # update_program, update_code
                "print('Fixed example')",  # fixed_program
                "def my_func(): return 'fixed'",  # fixed_code
                "LLM analysis",
                0.5,  # cost
                "mock-model"
            )
        mock_fix_code_module_errors.side_effect = mock_fix

        # Run fix_code_loop
        success, final_program, final_code, attempts, cost, model = fix_code_loop(
            code_file=str(code_file),
            prompt="Test prompt",
            verification_program=str(example_file),
            strength=0.5,
            temperature=0.5,
            max_attempts=2,
            budget=10.0,
            error_log_file=str(tmp_path / "error.log"),
            verbose=False,
        )

        # Verify backups are in .pdd/backups/, NOT in the working directory
        backup_base = tmp_path / ".pdd" / "backups" / "my_module"
        assert backup_base.exists(), f"Backup directory should exist at {backup_base}"

        # Find the timestamp subdirectory
        backup_dirs = list(backup_base.glob("*"))
        assert len(backup_dirs) >= 1, f"Should have at least one backup timestamp dir, found: {backup_dirs}"

        backup_dir = backup_dirs[0]

        # Check that program (example) backup exists in .pdd/backups/
        program_backups = list(backup_dir.glob("program_*.py"))
        assert len(program_backups) >= 1, f"Should have program backup in {backup_dir}, found: {list(backup_dir.glob('*'))}"

        # Check that code backup exists in .pdd/backups/
        code_backups = list(backup_dir.glob("code_*.py"))
        assert len(code_backups) >= 1, f"Should have code backup in {backup_dir}"

        # IMPORTANT: Verify NO versioned files in working directory
        # Old behavior would create my_module_example_1.py in the working directory
        old_style_backups = list(tmp_path.glob("my_module_example_*.py"))
        assert len(old_style_backups) == 0, (
            f"Should NOT have versioned example files in working directory, "
            f"but found: {old_style_backups}"
        )

        # Also check no versioned code files in working directory
        old_style_code_backups = list(tmp_path.glob("my_module_*.py"))
        # Filter out the original file
        old_style_code_backups = [f for f in old_style_code_backups if f.name != "my_module.py" and f.name != "my_module_example.py"]
        assert len(old_style_code_backups) == 0, (
            f"Should NOT have versioned code files in working directory, "
            f"but found: {old_style_code_backups}"
        )


class TestNonPythonAgenticFallback:
    """Tests for non-Python language handling and agentic fallback."""

    def test_non_python_no_verify_command_triggers_agentic_fallback(self, tmp_path, monkeypatch):
        """
        When a non-Python file (e.g., Java) has no verify command available,
        fix_code_loop should trigger agentic fallback directly instead of raising ValueError.
        """
        # Create a Java code file
        code_file = tmp_path / "Calculator.java"
        code_file.write_text("public class Calculator { public int add(int a, int b) { return a + b; } }")

        # Create a Java example file
        example_file = tmp_path / "CalculatorExample.java"
        example_file.write_text("public class CalculatorExample { public static void main(String[] args) {} }")

        # Create a prompt file
        prompt_file = tmp_path / "calculator.prompt"
        prompt_file.write_text("Create a calculator class")

        error_log = tmp_path / "error.log"

        # Mock default_verify_cmd_for to return None (no verify command for Java without maven/gradle)
        monkeypatch.setattr(
            "pdd.fix_code_loop.default_verify_cmd_for",
            lambda lang, program: None
        )

        # Mock get_language to return 'java'
        monkeypatch.setattr(
            "pdd.fix_code_loop.get_language",
            lambda ext: "java"
        )

        # Mock _safe_run_agentic_crash to return success
        mock_agentic_called = []
        def mock_agentic(**kwargs):
            mock_agentic_called.append(kwargs)
            return True, "Fixed successfully", 0.5, "claude-agentic", []

        monkeypatch.setattr(
            "pdd.fix_code_loop._safe_run_agentic_crash",
            mock_agentic
        )

        monkeypatch.chdir(tmp_path)

        # Call fix_code_loop - should NOT raise ValueError
        success, final_program, final_code, attempts, cost, model = fix_code_loop(
            code_file=str(code_file),
            prompt="Create a calculator class",
            verification_program=str(example_file),
            strength=0.5,
            temperature=0.1,
            max_attempts=3,
            budget=5.0,
            error_log_file=str(error_log),
            verbose=False,
            prompt_file=str(prompt_file),
            agentic_fallback=True
        )

        # Verify agentic fallback was called
        assert len(mock_agentic_called) == 1, "Agentic fallback should be called once"
        assert success is True
        assert "agentic" in model.lower()

    def test_non_python_no_verify_command_creates_error_log(self, tmp_path, monkeypatch):
        """
        When triggering agentic fallback for non-Python without verify command,
        an error log should be created if it doesn't exist.
        """
        code_file = tmp_path / "Calculator.java"
        code_file.write_text("public class Calculator {}")

        example_file = tmp_path / "CalculatorExample.java"
        example_file.write_text("public class CalculatorExample {}")

        prompt_file = tmp_path / "calculator.prompt"
        prompt_file.write_text("Create a calculator")

        error_log = tmp_path / "error.log"

        monkeypatch.setattr("pdd.fix_code_loop.default_verify_cmd_for", lambda lang, program: None)
        monkeypatch.setattr("pdd.fix_code_loop.get_language", lambda ext: "java")
        monkeypatch.setattr("pdd.fix_code_loop._safe_run_agentic_crash",
                          lambda **kwargs: (True, "Fixed", 0.5, "claude", []))

        monkeypatch.chdir(tmp_path)

        fix_code_loop(
            code_file=str(code_file),
            prompt="test",
            verification_program=str(example_file),
            strength=0.5,
            temperature=0.1,
            max_attempts=3,
            budget=5.0,
            error_log_file=str(error_log),
            verbose=False,
            prompt_file=str(prompt_file),
            agentic_fallback=True
        )

        # Error log should exist and contain meaningful content
        assert error_log.exists()
        content = error_log.read_text()
        assert "java" in content.lower() or "verification" in content.lower()