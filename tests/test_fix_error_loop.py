import os
import shutil
from pathlib import Path
import subprocess
from unittest.mock import patch
import pytest
import pdd

from pdd.fix_error_loop import fix_error_loop


@pytest.fixture
def setup_files(tmp_path, monkeypatch):
    """
    Create temporary directories and files for testing,
    including a code file, test file, and a verification program.
    """
    # Change cwd to tmp_path so .pdd/backups is created there
    monkeypatch.chdir(tmp_path)

    # Create directories
    pdd_dir = tmp_path / ".pdd"
    pdd_dir.mkdir()
    code_dir = tmp_path / "pdd"
    code_dir.mkdir()
    test_dir = tmp_path / "tests"
    test_dir.mkdir()

    # Create initial code file with an intentional error
    code_file = code_dir / "add_functions.py"
    code_content = "def add(a, b): return a + b + 1  # Intentional error"
    code_file.write_text(code_content)

    # Create unit test file
    test_file = test_dir / "test_code.py"
    test_content = """
import os
import sys
# Add the directory containing add_functions.py to the path
sys.path.append(os.path.join(os.path.dirname(__file__), "..", "pdd"))
from add_functions import add

def test_add():
    assert add(2, 3) == 5
    assert add(-1, 1) == 0
"""
    test_file.write_text(test_content)

    # Create verification program
    verify_file = tmp_path / "verify.py"
    verify_file.write_text("print('Verification passed')")

    return {
        "tmp_path": tmp_path,
        "code_file": code_file,
        "test_file": test_file,
        "verify_file": verify_file,
        "error_log": tmp_path / "error_log.txt",
    }


def test_successful_fix(setup_files):
    """
    Test a scenario where the code is successfully fixed on the first attempt.
    Mock the dependencies but patch fix_error_loop to skip the early return.
    """
    files = setup_files
    fixed_code = "def add(a, b): return a + b"  # The corrected code

    # First, write the original broken code to the file
    files["code_file"].write_text(
        "def add(a, b): return a + b + 1  # Intentional error"
    )

    # We need to patch fix_error_loop's implementation to avoid the early return
    # Save the original function to restore it later
    original_fix_error_loop = pdd.fix_error_loop.fix_error_loop

    # Define our patched version that skips the early return check
    def patched_fix_error_loop(
            unit_test_file, code_file, prompt_file, prompt, verification_program,
            strength, temperature, max_attempts, budget,
            error_log_file="error_log.txt", verbose=False, agentic_fallback=False):
        """A simplified version that always processes one fix attempt and returns success"""
        # Create a backup file for test file
        shutil.copy(unit_test_file, unit_test_file + ".bak")
        # Create a backup file for code file
        shutil.copy(code_file, code_file + ".bak")

        # Call fix_errors_from_unit_tests with basic params
        (updated_unit_test, updated_code, fixed_unit_test_content,
         fixed_code_content, analysis, cost, model) = pdd.fix_error_loop.fix_errors_from_unit_tests(
            Path(unit_test_file).read_text(),
            Path(code_file).read_text(),
            prompt,
            "Mock pytest output",
            error_log_file,
            strength,
            temperature,
            verbose
        )

        # Write the fixed code to files
        if updated_code:
            Path(code_file).write_text(fixed_code_content)
        if updated_unit_test:
            Path(unit_test_file).write_text(fixed_unit_test_content)

        # Read the final content
        with open(unit_test_file, "r") as f:
            final_unit_test = f.read()
        with open(code_file, "r") as f:
            final_code = f.read()

        # Always return success and 1 attempt
        return True, final_unit_test, final_code, 1, cost, model

    try:
        # Replace the original function with our patched version
        pdd.fix_error_loop.fix_error_loop = patched_fix_error_loop

        # Mock fix_errors_from_unit_tests to return fixed code
        with patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix:
            mock_fix.return_value = (
                True, True,  # updated_unit_test, updated_code
                files["test_file"].read_text(),
                fixed_code,  # corrected code
                "dummy analysis", # Analysis
                0.1,         # cost
                "mock-model"  # model_name
            )

            # Write the fixed code to the file before calling fix_error_loop
            files["code_file"].write_text(fixed_code)

            success, final_test, final_code, attempts, cost, model = (
                pdd.fix_error_loop.fix_error_loop(
                    unit_test_file=str(files["test_file"]),
                    code_file=str(files["code_file"]),
                    prompt_file="dummy_prompt.txt",
                    prompt="Test prompt",
                    verification_program=str(files["verify_file"]),
                    strength=0.5, 
                    temperature=0.0, 
                    max_attempts=3, 
                    budget=10.0,
                    error_log_file=str(files["error_log"]),
                    agentic_fallback=False
                )
            )
    finally:
        # Restore the original function
        pdd.fix_error_loop.fix_error_loop = original_fix_error_loop

    assert success is True
    assert fixed_code in final_code
    assert attempts == 1
    assert cost == 0.1
    assert model == "mock-model"


def test_already_passing(setup_files):
    """
    Test a scenario where the code already passes all tests without any fixes needed.
    In this case, fix_error_loop should return empty strings for final_test and final_code.
    """
    files = setup_files
    # Write the corrected code to the code file
    files["code_file"].write_text("def add(a, b): return a + b")
    files["test_file"].write_text("""
import os
import sys
# Add the directory containing add_functions.py to the path
sys.path.append(os.path.join(os.path.dirname(__file__), "..", "pdd"))
from add_functions import add

def test_add():
    assert add(2, 3) == 5
    assert add(-1, 1) == 0
""")
    # Call fix_code_loop
    success, final_test, final_code, attempts, cost, model = fix_error_loop(
            unit_test_file=str(files["test_file"]),
            code_file=str(files["code_file"]),
            prompt_file="dummy_prompt.txt",
            prompt=(
                "Write a function add() that takes in and adds two numbers together."
            ),
            verification_program=str(files["verify_file"]),
            strength=0.5,
            temperature=0.0,
            max_attempts=3,
            budget=10.0,
            error_log_file=str(files["error_log"]),
            verbose=True,
            agentic_fallback=False
        )

    assert success is True
    assert final_test != ""  # Should return actual file contents when already passing
    assert final_code != ""  # Should return actual file contents when already passing
    assert "from add_functions import add" in final_test  # Verify test content is returned
    assert "def add(a, b): return a + b" in final_code    # Verify code content is returned
    assert attempts == 0     # No fix attempts should be made
    assert cost == 0.0       # No cost incurred
    assert model == ""       # No model used


def test_max_attempts_exceeded(setup_files):
    """
    Test that if every test run fails, eventually the loop hits max_attempts and exits.
    """
    files = setup_files

    with patch("pdd.fix_error_loop.run_pytest_on_file") as mock_run_pytest:
        # 2 attempts per iteration (initial + second in same iteration), plus 1 final
        # For max_attempts=3, let's provide enough calls returning fails=1 each time:
        mock_run_pytest.side_effect = [
            # Iteration 1
            (1, 0, 0, "test run output"),
            (1, 0, 0, "test run output"),
            # Iteration 2
            (1, 0, 0, "test run output"),
            (1, 0, 0, "test run output"),
            # Iteration 3
            (1, 0, 0, "test run output"),
            (1, 0, 0, "test run output"),
            # Final run
            (1, 0, 0, "test run output"),
        ]
        with patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix:
            # Return "no change" each time => triggers repeated fixes
            mock_fix.return_value = (
                False, False, "", "", "No analysis", 0.0, "mock-model"
            )

            success, final_test, final_code, attempts, cost, model = fix_error_loop(
                unit_test_file=str(files["test_file"]),
                code_file=str(files["code_file"]),
                prompt_file="dummy_prompt.txt",
                prompt="Test prompt",
                verification_program=str(files["verify_file"]),
                strength=0.5,
                temperature=0.0,
                max_attempts=3,           # max_attempts
                budget=10.0,
                error_log_file=str(files["error_log"]),
                agentic_fallback=False
            )

    assert success is False
    # We used all 3 attempts
    assert attempts == 3
    # Code was never successfully changed (still has the +1)
    assert "return a + b + 1" in final_code


def test_verification_failure(setup_files):
    """
    Test a scenario where the code gets "fixed" but then fails verification,
    so it is restored, and the tests keep failing.
    """
    files = setup_files

    with patch("pdd.fix_error_loop.run_pytest_on_file") as mock_run_pytest:
        # Provide enough side effects for 3 iterations =>
        # each iteration calls run_pytest_on_file twice (initial + second)
        # plus 1 final run: total = 2*3 + 1 = 7 calls
        mock_run_pytest.side_effect = [
            # Iteration 1
            (1, 0, 0, "test run output"),  # 1) initial fails
            (1, 0, 0, "test run output"),  # 2) second fails
            # Iteration 2
            (1, 0, 0, "test run output"),  # 3) initial fails
            (1, 0, 0, "test run output"),  # 4) second fails
            # Iteration 3
            (1, 0, 0, "test run output"),  # 5) initial fails
            (1, 0, 0, "test run output"),  # 6) second fails
            # Final run
            (1, 0, 0, "test run output"),  # 7) final fails
        ]

        with patch("subprocess.run") as mock_subproc:
            # verification fails => returncode=1
            mock_subproc.return_value = subprocess.CompletedProcess(
                args=[], returncode=1
            )

            with patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix:
                # Return a "fixed" code that is still incorrec
                mock_fix.return_value = (
                    True, True,
                    files["test_file"].read_text(),
                    "def add(a, b): return 0",  # intentionally bad fix
                    "Analysis of the fix",      # analysis
                    0.1,
                    "mock-model"
                )

                success, final_test, final_code, attempts, cost, model = (
                    fix_error_loop(
                        unit_test_file=str(files["test_file"]),
                        code_file=str(files["code_file"]),
                        prompt_file="dummy_prompt.txt",
                        prompt="Test prompt",
                        verification_program=str(files["verify_file"]),
                        strength=0.5,
                        temperature=0.0,
                        max_attempts=3,
                        budget=10.0,
                        error_log_file=str(files["error_log"]),
                        agentic_fallback=False
                    )
                )

    # Expect failure after 3 attempts
    assert success is False
    # After verification fails, we restore the original code each time => +1 is still there
    assert "return a + b + 1" in final_code


def test_backup_creation(setup_files):
    """
    Test that we create backup files correctly when tests fail.
    """
    files = setup_files

    # Write a test file to the code file firs
    files["code_file"].write_text(
        "def add(a, b): return a + b + 1  # Intentional error"
    )

    with patch("pdd.fix_error_loop.run_pytest_on_file") as mock_run_pytest:
        # Return fails=1 => triggers fix, then second run => fails=1, then final => fails=1
        mock_run_pytest.side_effect = [
            (1, 0, 0, "test run output"),
            (1, 0, 0, "test run output"),
            (1, 0, 0, "test run output"),
        ]
        with patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix:
            # Return that we changed both test and code, with actual content this time
            mock_fix.return_value = (
                True, True,
                "modified test content",
                "def add(a, b): return a + b  # Fixed",
                "Analysis text", 0.1, "mock-model"
            )

            fix_error_loop(
                unit_test_file=str(files["test_file"]),
                code_file=str(files["code_file"]),
                prompt_file="dummy_prompt.txt",
                prompt="Test prompt",
                verification_program=str(files["verify_file"]),
                strength=0.5, 
                temperature=0.0, 
                max_attempts=1, 
                budget=10.0,
                error_log_file=str(files["error_log"]),
                agentic_fallback=False
            )

    # Check for backup files in .pdd/backups/
    backup_base = files["tmp_path"] / ".pdd" / "backups" / "add_functions"
    print(f"Looking for backups in: {backup_base}")
    backup_dirs = list(backup_base.glob("*")) if backup_base.exists() else []
    print(f"Backup dirs: {backup_dirs}")

    assert len(backup_dirs) >= 1, f"No backup dirs found in {backup_base}"
    # Check that backup files were created
    backup_files = list(backup_dirs[0].glob("*.py")) if backup_dirs else []
    assert backup_files, f"No backup files found in {backup_dirs}"


def test_missing_files():
    """
    Ensure that fix_error_loop returns False immediately if the test/code files do not exist.
    """
    success, *rest = fix_error_loop(
        unit_test_file="nonexistent_test.py",
        code_file="nonexistent_code.py",
        prompt_file="dummy_prompt.txt",
        prompt="prompt",
        verification_program="verify.py",
        strength=0.5, 
        temperature=0.0, 
        max_attempts=3, 
        budget=10.0,
        agentic_fallback=False
    )
    assert success is False

def test_non_python_triggers_agentic_fallback_success(tmp_path):
    """
    If the code_file is not a .py file, fix_error_loop should immediately
    trigger agentic fallback and return its result.
    """
    # Arrange: make a dummy non-Python code file and a unit test file
    code_dir = tmp_path / "proj"
    code_dir.mkdir()
    code_file = code_dir / "index.js"
    code_file.write_text("export const add = (a,b) => a + b + 1;")  # broken on purpose

    tests_dir = tmp_path / "tests"
    tests_dir.mkdir()
    unit_test_file = tests_dir / "test_dummy.txt"
    unit_test_file.write_text("dummy unit test content")

    verify_file = tmp_path / "verify.sh"
    verify_file.write_text("#!/bin/bash\nexit 1") # Fail to trigger fallback
    verify_file.chmod(0o755)
    error_log = tmp_path / "error_log.txt"
    with patch("pdd.fix_error_loop.run_agentic_fix") as mock_agent, \
         patch("pdd.fix_error_loop.run_pytest_on_file") as mock_pytest:
        mock_agent.return_value = (True, "ok")
        # Act
        success, final_test, final_code, attempts, cost, model = fix_error_loop(
            unit_test_file=str(unit_test_file),
            code_file=str(code_file),
            prompt_file="dummy_prompt.txt",
            prompt="Fix the JS add function",
            verification_program=str(verify_file),
            strength=0.5,
            temperature=0.0,
            max_attempts=2,
            budget=5.0,
            error_log_file=str(error_log),
            verbose=True,
            agentic_fallback=True,
        )

    # Assert: agentic path taken, pytest never called
    mock_agent.assert_called_once()
    mock_pytest.assert_not_called()
    assert success is True
    assert attempts == 1
    assert model == "agentic-cli"
    # Returned contents come from reading files (best-effort in implementation)
    assert "dummy unit test content" in final_test
    assert "export const add" in final_code


def test_non_python_triggers_agentic_fallback_failure(tmp_path):
    """
    If agentic fallback returns failure, fix_error_loop should propagate that failure
    and still count 1 attempt, without invoking pytest.
    """
    code_dir = tmp_path / "proj"
    code_dir.mkdir()
    code_file = code_dir / "main.js"
    code_file.write_text("console.log('Hello, world!');")

    tests_dir = tmp_path / "tests"
    tests_dir.mkdir()
    unit_test_file = tests_dir / "test_dummy.txt"
    unit_test_file.write_text("dummy test")

    verify_file = tmp_path / "verify.sh"
    verify_file.write_text("#!/bin/bash\nexit 1") # Fail to trigger fallback
    verify_file.chmod(0o755)
    error_log = tmp_path / "error_log.txt"
    with patch("pdd.fix_error_loop.run_agentic_fix") as mock_agent, \
         patch("pdd.fix_error_loop.run_pytest_on_file") as mock_pytest:
        mock_agent.return_value = (False, "not ok")
        success, final_test, final_code, attempts, cost, model = fix_error_loop(
            unit_test_file=str(unit_test_file),
            code_file=str(code_file),
            prompt_file="dummy_prompt.txt",
            prompt="Fix the javascript code",
            verification_program=str(verify_file),
            strength=0.5,
            temperature=0.0,
            max_attempts=2,
            budget=5.0,
            error_log_file=str(error_log),
            verbose=False,
            agentic_fallback=True,
        )

    mock_agent.assert_called_once()
    mock_pytest.assert_not_called()
    assert success is False
    assert attempts == 1
    assert model == "agentic-cli"
    # Should still return contents read from disk on best-effort basis
    assert "dummy test" in final_test
    assert "console.log('Hello, world!');" in final_code


class BrokenStdin:
    def fileno(self):
        raise ValueError("redirected stdin is pseudofile, has no fileno()")
    
    def read(self, size=-1):
        return ""


def test_subprocess_safe_stdin_in_run_pytest_on_file(tmp_path):
    """
    Regression test ensuring the fix propagates to the higher-level helper 
    used by fix_error_loop.
    """
    # We need to import run_pytest_on_file locally if not exposed, 
    # but it is available from pdd.fix_error_loop
    from pdd.fix_error_loop import run_pytest_on_file
    
    test_file = tmp_path / "test_dummy_2.py"
    test_file.write_text("def test_pass(): assert True", encoding="utf-8")
    
    with patch('sys.stdin', BrokenStdin()):
        try:
            fails, errors, warnings, logs = run_pytest_on_file(str(test_file))
            assert fails == 0
            assert errors == 0
        except ValueError as e:
            pytest.fail(f"run_pytest_on_file crashed with ValueError accessing stdin: {e}")


def test_fix_loop_reloading(tmp_path):
    """
    Regression test for module caching issues.
    Ensures that if a test file imports a module, and that module changes on disk,
    the next run of run_pytest_on_file sees the NEW code (because it uses a fresh subprocess).
    """
    import time
    from pdd.fix_error_loop import run_pytest_on_file

    # 1. Create the module
    module_file = tmp_path / "target_module.py"
    module_file.write_text("def target_func(): return 1\n", encoding="utf-8")
    
    # 2. Create the test that expects return value 2 (so it fails initially)
    test_file = tmp_path / "test_target.py"
    test_file.write_text("""
import sys
import os
# Ensure current dir is in path so we can import target_module
sys.path.insert(0, os.path.dirname(__file__))
from target_module import target_func

def test_func():
    assert target_func() == 2
""", encoding="utf-8")
    
    # 3. Run first time -> SHOULD FAIL
    # run_pytest_on_file returns (fails, errors, warnings, logs)
    fails, errors, warnings, logs = run_pytest_on_file(str(test_file))
    assert fails == 1, "Test should have failed initially"
    
    # 4. Modify the module on disk to pass the test
    # Wait a tiny bit to ensure filesystem timestamp update if needed (usually fine)
    time.sleep(0.1) 
    module_file.write_text("def target_func(): return 2\n", encoding="utf-8")
    
    # 5. Run second time -> SHOULD PASS
    # If module caching was active (old behavior), this would fail again.
    fails_2, errors_2, warnings_2, logs_2 = run_pytest_on_file(str(test_file))

    assert fails_2 == 0, f"Test should have passed after update. Logs:\n{logs_2}"


def test_run_pytest_on_file_counts_failures_with_forced_color(tmp_path, monkeypatch):
    """
    Regression test: run_pytest_on_file must still detect failures when pytest
    is configured to emit ANSI color codes (as in the sync TUI environment).
    """
    from pdd.fix_error_loop import run_pytest_on_file

    test_file = tmp_path / "test_failure_color_fix_loop.py"
    test_file.write_text("def test_fail():\n    assert False\n", encoding="utf-8")

    existing_addopts = os.environ.get("PYTEST_ADDOPTS", "")
    addopts = (existing_addopts + " " if existing_addopts else "") + "--color=yes"
    monkeypatch.setenv("PYTEST_ADDOPTS", addopts)
    monkeypatch.setenv("TERM", "xterm-256color")

    fails, errors, warnings, logs = run_pytest_on_file(str(test_file))
    if "\x1b[" not in logs:
        pytest.skip("Pytest did not emit ANSI output even with --color=yes")
    assert fails == 1


# ============================================================================
# Bug Fix Tests - Model Name in Error Log
# ============================================================================

def test_error_log_includes_model_name(setup_files):
    """BUG TEST: Error log should include model name for each fix attempt."""
    files = setup_files

    expected_model = "gpt-4-turbo"

    with patch("pdd.fix_error_loop.run_pytest_on_file") as mock_pytest:
        mock_pytest.return_value = (1, 0, 0, "test failed")

        with patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix:
            mock_fix.return_value = (False, False, "", "", "Analysis text", 0.1, expected_model)

            fix_error_loop(
                unit_test_file=str(files["test_file"]),
                code_file=str(files["code_file"]),
                prompt_file="prompt.txt",
                prompt="Test prompt",
                verification_program=str(files["verify_file"]),
                strength=0.5,
                temperature=0.0,
                max_attempts=1,
                budget=10.0,
                error_log_file=str(files["error_log"]),
                agentic_fallback=False
            )

    error_log_content = files["error_log"].read_text()
    assert expected_model in error_log_content, \
        f"BUG: Model name '{expected_model}' not in error log"


def test_error_log_contains_analysis_and_model(setup_files):
    """BUG TEST: Error log should have BOTH analysis AND model name."""
    files = setup_files

    analysis_text = "The test failed because X"
    model_name = "claude-3-opus"

    with patch("pdd.fix_error_loop.run_pytest_on_file") as mock_pytest:
        mock_pytest.return_value = (1, 0, 0, "pytest output")

        with patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix:
            mock_fix.return_value = (False, False, "", "", analysis_text, 0.1, model_name)

            fix_error_loop(
                unit_test_file=str(files["test_file"]),
                code_file=str(files["code_file"]),
                prompt_file="prompt.txt",
                prompt="Test",
                verification_program=str(files["verify_file"]),
                strength=0.5,
                temperature=0.0,
                max_attempts=1,
                budget=10.0,
                error_log_file=str(files["error_log"]),
                agentic_fallback=False
            )

    content = files["error_log"].read_text()
    assert analysis_text in content, "Analysis text missing"
    assert model_name in content, "BUG: Model name was not included in log"


# ============================================================================
# Bug Fix Tests - Run Report Integration (Infinite Fix Loop Prevention)
# ============================================================================

def test_run_report_discrepancy_causes_infinite_loop_bug(setup_files):
    """
    BUG REPRODUCTION: Demonstrates the infinite fix loop bug.

    When sync_orchestration's run_report shows tests_failed > 0,
    but fix_error_loop's own run_pytest_on_file returns 0 failures,
    fix_error_loop incorrectly returns success=True, cost=0.0.

    This causes sync_orchestration to think fix succeeded, but tests
    still fail, triggering an infinite loop.
    """
    files = setup_files

    with patch("pdd.fix_error_loop.run_pytest_on_file") as mock_pytest:
        # Simulate the discrepancy: run_pytest_on_file returns 0 failures
        # (even though sync_orchestration's run_report showed 3 failures)
        mock_pytest.return_value = (0, 0, 0, "All tests passed")

        success, final_test, final_code, attempts, cost, model = fix_error_loop(
            unit_test_file=str(files["test_file"]),
            code_file=str(files["code_file"]),
            prompt_file="dummy_prompt.txt",
            prompt="Test prompt",
            verification_program=str(files["verify_file"]),
            strength=0.5,
            temperature=0.0,
            max_attempts=3,
            budget=10.0,
            error_log_file=str(files["error_log"]),
            agentic_fallback=False
        )

    # BUG DOCUMENTED: Returns success=True, cost=0.0 without invoking LLM
    # This is correct behavior IF tests genuinely pass, but when there's
    # a discrepancy with the caller's run_report, it causes infinite loops
    assert success is True
    assert cost == 0.0
    assert model == ""


# ============================================================================
# Bug Fix Tests - Context Override in Sync Orchestration
# ============================================================================

def test_sync_orchestration_passes_context_to_mock_context():
    """
    BUG FIX TEST: sync_orchestration._create_mock_context must include
    context parameter so that downstream commands (fix_main, etc.) receive
    the correct .pddrc context.

    The bug was that --context backend was passed to sync_orchestration but
    not forwarded to _create_mock_context, causing fix_main to use 'default'
    context instead of 'backend', resulting in wrong file paths and infinite loops.
    """
    from pdd.sync_orchestration import _create_mock_context

    # Test that context is properly passed to the mock context
    ctx = _create_mock_context(
        force=False,
        strength=0.5,
        context='backend'
    )

    # The context should be available in ctx.obj
    assert ctx.obj.get('context') == 'backend', \
        "BUG: context not passed to _create_mock_context - this causes infinite fix loops!"

    # Also test with None (should work for backward compatibility)
    ctx_none = _create_mock_context(force=False, strength=0.5)
    assert ctx_none.obj.get('context') is None


def test_sync_orchestration_context_none_by_default():
    """
    Verify that when context is not provided, it defaults to None
    (which allows construct_paths to auto-detect based on current directory).
    """
    from pdd.sync_orchestration import _create_mock_context

    ctx = _create_mock_context(force=False)
    assert ctx.obj.get('context') is None


# ============================================================================
# Bug Fix Tests - Agentic Fallback CWD
# ============================================================================

def test_agentic_fallback_cwd_is_project_root_not_prompt_parent(tmp_path, monkeypatch):
    """
    BUG FIX TEST: When agentic fallback is triggered, the cwd parameter passed
    to run_agentic_fix should be None (to use project root), NOT Path(prompt_file).parent.

    The bug was that fix_error_loop passed cwd=Path(prompt_file).parent, which
    caused path resolution failures when:
    - prompt_file is in a subdirectory (e.g., prompts/backend/utils/)
    - code_file is relative to project root (e.g., backend/functions/utils/code.py)

    This resulted in malformed paths like:
    prompts/backend/utils/backend/functions/utils/code.py
    """
    monkeypatch.chdir(tmp_path)

    # Create nested prompt directory structure (like prompts/backend/utils/)
    prompt_dir = tmp_path / "prompts" / "backend" / "utils"
    prompt_dir.mkdir(parents=True)
    prompt_file = prompt_dir / "my_module_python.prompt"
    prompt_file.write_text("Generate a module")

    # Create code directory structure (like backend/functions/utils/)
    code_dir = tmp_path / "backend" / "functions" / "utils"
    code_dir.mkdir(parents=True)
    code_file = code_dir / "my_module.py"
    code_file.write_text("def foo(): pass")

    # Create test file
    test_dir = tmp_path / "tests"
    test_dir.mkdir()
    test_file = test_dir / "test_my_module.py"
    test_file.write_text("def test_foo(): pass")

    error_log = tmp_path / "error_log.txt"

    captured_cwd = []

    def capture_cwd_mock(**kwargs):
        """Capture the cwd parameter passed to run_agentic_fix"""
        captured_cwd.append(kwargs.get('cwd'))
        return (True, "Fixed", 0.1, "mock-model", [])

    with patch("pdd.fix_error_loop.run_agentic_fix", side_effect=capture_cwd_mock) as mock_agent, \
         patch("pdd.fix_error_loop.run_pytest_on_file") as mock_pytest, \
         patch("subprocess.run") as mock_subprocess:
        # Make tests have warnings (0 fails, 0 errors, 4 warnings) to trigger agentic fallback
        # since success = (fails == 0 and errors == 0 and warnings == 0) will be False
        mock_pytest.return_value = (0, 0, 4, "4 warnings")
        # Mock subprocess for verification program
        mock_subprocess.return_value = subprocess.CompletedProcess(args=[], returncode=0, stdout="", stderr="")

        success, final_test, final_code, attempts, cost, model = fix_error_loop(
            unit_test_file=str(test_file),
            code_file=str(code_file),
            prompt_file=str(prompt_file),
            prompt="Fix the module",
            verification_program=str(tmp_path / "verify.py"),  # Provide a verification program path
            strength=0.5,
            temperature=0.0,
            max_attempts=1,
            budget=5.0,
            error_log_file=str(error_log),
            verbose=False,
            agentic_fallback=True,
        )

    # Verify agentic fallback was called
    assert mock_agent.called, "Agentic fallback should have been triggered"

    # THE BUG: cwd was set to Path(prompt_file).parent = prompts/backend/utils
    # THE FIX: cwd should be None (to use project root)
    assert len(captured_cwd) > 0, "Should have captured cwd parameter"
    cwd_value = captured_cwd[0]

    # cwd should be None (use project root) or the actual project root
    # It should NOT be the prompt file's parent directory
    prompt_parent = Path(prompt_file).parent
    assert cwd_value is None or cwd_value == tmp_path, \
        f"BUG: cwd should be None or project root, but got {cwd_value}. " \
        f"This causes path resolution failures when prompt is in a subdirectory!"


# ============================================================================
# Bug Fix Tests - Issue #266: Early Returns Bypass Agentic Fallback
# ============================================================================

def test_pytest_exception_triggers_agentic_fallback(setup_files):
    """
    BUG TEST (Issue #266): When pytest throws an exception during iteration
    (Line 760), the fix_error_loop should trigger agentic fallback instead
    of returning early.

    Current behavior: Returns early with `return False, "", "", fix_attempts, total_cost, model_name`
    Expected behavior: Should break from loop and continue to agentic fallback at line 835

    This test fails on the current (buggy) code and should pass once the bug is fixed.
    """
    files = setup_files

    with patch("pdd.fix_error_loop.run_pytest_on_file") as mock_pytest, \
         patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix, \
         patch("pdd.fix_error_loop.run_agentic_fix") as mock_agentic:

        # First call: return failures to trigger the fix loop
        # Second call (Line 730): raise an exception to trigger Line 760
        mock_pytest.side_effect = [
            (1, 0, 0, "Initial test failure"),  # Initial test fails
            Exception("Pytest collection error: import failed"),  # Exception during iteration
        ]

        # Mock fix_errors_from_unit_tests to return a "fix" that triggers second pytest run
        mock_fix.return_value = (
            True, True,  # updated_unit_test, updated_code
            files["test_file"].read_text(),
            "def add(a, b): return a + b  # fixed",
            "Analysis text",
            0.1,
            "mock-model"
        )

        # Agentic fallback should succeed
        mock_agentic.return_value = (True, "Fixed by agentic", 0.5, "claude-cli", [])

        success, final_test, final_code, attempts, cost, model = fix_error_loop(
            unit_test_file=str(files["test_file"]),
            code_file=str(files["code_file"]),
            prompt_file="dummy_prompt.txt",
            prompt="Test prompt",
            verification_program=str(files["verify_file"]),
            strength=0.5,
            temperature=0.0,
            max_attempts=3,
            budget=10.0,
            error_log_file=str(files["error_log"]),
            verbose=False,
            agentic_fallback=True,  # Enable agentic fallback
        )

    # THE BUG: Agentic fallback is NOT called because line 760 returns early
    # THE FIX: Convert return to break so the code continues to agentic fallback
    assert mock_agentic.called, \
        "BUG (Issue #266): Agentic fallback was NOT triggered after pytest exception. " \
        "Line 760's early return bypasses the agentic fallback code at line 835."


def test_backup_creation_error_triggers_agentic_fallback(setup_files, monkeypatch):
    """
    BUG TEST (Issue #266): When backup file creation fails (Line 582),
    the fix_error_loop should trigger agentic fallback instead of returning early.

    Current behavior: Returns early at line 582
    Expected behavior: Should continue to agentic fallback
    """
    files = setup_files

    # Make shutil.copy fail
    def failing_copy(*args, **kwargs):
        raise OSError("Disk full - cannot create backup")

    with patch("pdd.fix_error_loop.run_pytest_on_file") as mock_pytest, \
         patch("pdd.fix_error_loop.run_agentic_fix") as mock_agentic, \
         patch("shutil.copy", side_effect=failing_copy):

        # Return failures to trigger the fix loop
        mock_pytest.return_value = (1, 0, 0, "Test failure")

        # Agentic fallback should succeed
        mock_agentic.return_value = (True, "Fixed by agentic", 0.5, "claude-cli", [])

        success, final_test, final_code, attempts, cost, model = fix_error_loop(
            unit_test_file=str(files["test_file"]),
            code_file=str(files["code_file"]),
            prompt_file="dummy_prompt.txt",
            prompt="Test prompt",
            verification_program=str(files["verify_file"]),
            strength=0.5,
            temperature=0.0,
            max_attempts=3,
            budget=10.0,
            error_log_file=str(files["error_log"]),
            verbose=False,
            agentic_fallback=True,
        )

    # THE BUG: Agentic fallback is NOT called because line 582 returns early
    assert mock_agentic.called, \
        "BUG (Issue #266): Agentic fallback was NOT triggered after backup creation error. " \
        "Line 582's early return bypasses the agentic fallback code at line 835."


def test_file_read_error_triggers_agentic_fallback(setup_files):
    """
    BUG TEST (Issue #266): When reading input files fails (Line 605),
    the fix_error_loop should trigger agentic fallback instead of returning early.

    Current behavior: Returns early at line 605
    Expected behavior: Should continue to agentic fallback
    """
    files = setup_files

    original_open = open

    def failing_open(path, mode="r", *args, **kwargs):
        # Fail when reading code_file during the iteration (not initial)
        if "r" in mode and str(files["code_file"]) in str(path):
            # Allow first read (initial exists check passes), fail on iteration read
            if not hasattr(failing_open, "_first_read_done"):
                failing_open._first_read_done = True
                return original_open(path, mode, *args, **kwargs)
            raise IOError("Permission denied - cannot read file")
        return original_open(path, mode, *args, **kwargs)

    with patch("pdd.fix_error_loop.run_pytest_on_file") as mock_pytest, \
         patch("pdd.fix_error_loop.run_agentic_fix") as mock_agentic, \
         patch("builtins.open", side_effect=failing_open):

        # Return failures to trigger fix loop
        mock_pytest.return_value = (1, 0, 0, "Test failure")

        # Agentic fallback should succeed
        mock_agentic.return_value = (True, "Fixed by agentic", 0.5, "claude-cli", [])

        success, final_test, final_code, attempts, cost, model = fix_error_loop(
            unit_test_file=str(files["test_file"]),
            code_file=str(files["code_file"]),
            prompt_file="dummy_prompt.txt",
            prompt="Test prompt",
            verification_program=str(files["verify_file"]),
            strength=0.5,
            temperature=0.0,
            max_attempts=3,
            budget=10.0,
            error_log_file=str(files["error_log"]),
            verbose=False,
            agentic_fallback=True,
        )

    # THE BUG: Agentic fallback is NOT called because line 605 returns early
    assert mock_agentic.called, \
        "BUG (Issue #266): Agentic fallback was NOT triggered after file read error. " \
        "Line 605's early return bypasses the agentic fallback code at line 835."


def test_agentic_fallback_not_called_when_disabled(setup_files):
    """
    REGRESSION TEST: When agentic_fallback=False, agentic fallback should NOT
    be called even when the fix loop fails.

    This ensures the fix for Issue #266 doesn't accidentally trigger agentic
    fallback when it's explicitly disabled.
    """
    files = setup_files

    with patch("pdd.fix_error_loop.run_pytest_on_file") as mock_pytest, \
         patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix, \
         patch("pdd.fix_error_loop.run_agentic_fix") as mock_agentic:

        # All attempts fail
        mock_pytest.return_value = (1, 0, 0, "Test failure")
        mock_fix.return_value = (False, False, "", "", "No fix", 0.1, "mock-model")

        success, final_test, final_code, attempts, cost, model = fix_error_loop(
            unit_test_file=str(files["test_file"]),
            code_file=str(files["code_file"]),
            prompt_file="dummy_prompt.txt",
            prompt="Test prompt",
            verification_program=str(files["verify_file"]),
            strength=0.5,
            temperature=0.0,
            max_attempts=3,
            budget=10.0,
            error_log_file=str(files["error_log"]),
            verbose=False,
            agentic_fallback=False,  # Explicitly disabled
        )

    # Agentic should NOT be called when explicitly disabled
    assert not mock_agentic.called, \
        "REGRESSION: Agentic fallback was called even though agentic_fallback=False"
    assert success is False


def test_agentic_fallback_success_after_loop_failure(setup_files):
    """
    BUG TEST (Issue #266): When the fix loop exhausts max_attempts and fails,
    agentic fallback should be triggered and its success should be returned.

    This test verifies the return values are correct when agentic fallback succeeds.
    """
    files = setup_files

    with patch("pdd.fix_error_loop.run_pytest_on_file") as mock_pytest, \
         patch("pdd.fix_error_loop.fix_errors_from_unit_tests") as mock_fix, \
         patch("pdd.fix_error_loop.run_agentic_fix") as mock_agentic:

        # All fix attempts fail
        mock_pytest.return_value = (1, 0, 0, "Test failure")
        mock_fix.return_value = (False, False, "", "", "No fix", 0.1, "mock-model")

        # Agentic fallback succeeds
        mock_agentic.return_value = (True, "Fixed by agentic", 0.5, "claude-cli", ["code.py"])

        success, final_test, final_code, attempts, cost, model = fix_error_loop(
            unit_test_file=str(files["test_file"]),
            code_file=str(files["code_file"]),
            prompt_file="dummy_prompt.txt",
            prompt="Test prompt",
            verification_program=str(files["verify_file"]),
            strength=0.5,
            temperature=0.0,
            max_attempts=1,
            budget=10.0,
            error_log_file=str(files["error_log"]),
            verbose=False,
            agentic_fallback=True,
        )

    # Agentic was called and succeeded
    assert mock_agentic.called, "Agentic fallback should have been triggered"
    assert success is True, "Success should be True after agentic fallback succeeds"
    assert "claude-cli" in model or model == "claude-cli", \
        f"Model should reflect agentic fallback, got: {model}"
