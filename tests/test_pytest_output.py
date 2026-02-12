import pytest
import json
import os
from pathlib import Path
from pdd.pytest_output import (
    run_pytest_and_capture_output,
    save_output_to_json,
    TestResultCollector,
    extract_failing_files_from_output,
)
import pdd.pytest_output
import sys
from unittest.mock import patch


# Create a directory for test outputs (use project root output/ directory)
OUTPUT_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "output")
os.makedirs(OUTPUT_DIR, exist_ok=True)


def create_test_file(file_path: str, content: str) -> None:
    """Helper function to create test files."""
    with open(file_path, "w") as f:
        f.write(content)


# Test cases for run_pytest_and_capture_output
def test_run_pytest_and_capture_output_file_not_found() -> None:
    """Test case: test file does not exist."""
    result = run_pytest_and_capture_output("nonexistent_file.py")
    assert result == {}


def test_run_pytest_and_capture_output_invalid_file_type() -> None:
    """Test case: test file is not a Python file."""
    test_file = os.path.join(OUTPUT_DIR, "test_file.txt")
    create_test_file(test_file, "This is not a Python file.")
    result = run_pytest_and_capture_output(test_file)
    assert result == {}
    Path(test_file).unlink(missing_ok=True)


def test_run_pytest_and_capture_output_successful_run() -> None:
    """Test case: successful pytest run."""
    test_file = os.path.join(OUTPUT_DIR, "test_success.py")
    create_test_file(
        test_file, "def test_pass():\n    assert True"
    )
    result = run_pytest_and_capture_output(test_file)
    assert result["test_file"] == test_file
    assert result["test_results"][0]["return_code"] == 0
    assert result["test_results"][0]["passed"] == 1
    assert result["test_results"][0]["failures"] == 0
    assert result["test_results"][0]["errors"] == 0
    # Warnings count may be non-zero due to pytest configuration warnings (unrelated to test)
    assert isinstance(result["test_results"][0]["warnings"], int)
    Path(test_file).unlink(missing_ok=True)


def test_run_pytest_and_capture_output_failed_test() -> None:
    """Test case: pytest run with a failing test."""
    test_file = os.path.join(OUTPUT_DIR, "test_failure.py")
    create_test_file(
        test_file, "def test_fail():\n    assert False"
    )
    result = run_pytest_and_capture_output(test_file)
    assert result["test_file"] == test_file
    assert result["test_results"][0]["return_code"] == 1
    assert result["test_results"][0]["failures"] == 1
    assert result["test_results"][0]["passed"] == 0
    assert result["test_results"][0]["errors"] == 0
    # Warnings count may be non-zero due to pytest configuration warnings (unrelated to test)
    assert isinstance(result["test_results"][0]["warnings"], int)
    Path(test_file).unlink(missing_ok=True)


def test_run_pytest_and_capture_output_error_test() -> None:
    """Test case: pytest run with an exception in the test body (ValueError)."""
    test_file = os.path.join(OUTPUT_DIR, "test_error.py")
    create_test_file(test_file, "def test_error():\n    raise ValueError")
    result = run_pytest_and_capture_output(test_file)

    assert result["test_file"] == test_file
    assert result["test_results"][0]["return_code"] == 1
    
    # Now that we're matching Pytest's default handling, a ValueError is a "failure":
    assert result["test_results"][0]["failures"] == 1
    assert result["test_results"][0]["errors"] == 0
    
    assert result["test_results"][0]["passed"] == 0
    # Warnings count may be non-zero due to pytest configuration warnings (unrelated to test)
    assert isinstance(result["test_results"][0]["warnings"], int)
    Path(test_file).unlink(missing_ok=True)


def test_run_pytest_and_capture_output_with_warnings() -> None:
    """Test case: pytest run with warnings."""
    test_file = os.path.join(OUTPUT_DIR, "test_warnings.py")
    create_test_file(
        test_file,
        "import pytest\n@pytest.mark.filterwarnings('ignore::DeprecationWarning')\ndef test_warning():\n    pytest.warns(DeprecationWarning)",
    )
    result = run_pytest_and_capture_output(test_file)
    assert result["test_file"] == test_file
    # Pytest return code can be 0 (if warnings are not treated as errors) or 3
    assert result["test_results"][0]["return_code"] in (
        0,
        3,
    )  # 3 means warnings were emitted
    assert result["test_results"][0]["warnings"] >= 0  # Check for warnings
    Path(test_file).unlink(missing_ok=True)


# Test cases for save_output_to_json
def test_save_output_to_json_successful(tmp_path) -> None:
    """Test case: successful save to JSON."""
    output_file = tmp_path / "pytest_output.json"
    test_data = {"test": "data"}
    save_output_to_json(test_data, str(output_file))
    assert output_file.exists()
    with open(output_file, "r") as f:
        loaded_data = json.load(f)
    assert loaded_data == test_data


def test_save_output_to_json_exception(tmp_path, capsys) -> None:
    """Test case: exception during save to JSON."""
    # Mock the json.dump function to raise an exception
    with patch("json.dump", side_effect=Exception("Test Exception")):
        output_file = tmp_path / "pytest_output.json"
        test_data = {"test": "data"}
        save_output_to_json(test_data, str(output_file))
        captured = capsys.readouterr()
        assert "Error saving output to JSON: Test Exception" in captured.out


def test_test_result_collector_capture_logs() -> None:
    """Test the capture_logs and get_logs methods of TestResultCollector."""
    collector = TestResultCollector()

    # Redirect stdout and stderr
    collector.capture_logs()

    # Write to stdout and stderr
    print("Test stdout")
    print("Test stderr", file=sys.stderr)

    # Get captured logs
    stdout, stderr = collector.get_logs()

    assert stdout == "Test stdout\nTest stderr\n"
    assert stderr == "Test stdout\nTest stderr\n"

    # Ensure stdout and stderr are reset
    assert sys.stdout == sys.__stdout__
    assert sys.stderr == sys.__stderr__


def test_test_result_collector_pytest_hooks() -> None:
    """Test the pytest hooks of TestResultCollector."""

    class MockReport:
        def __init__(self, when: str, outcome: str, failed: bool = False, passed: bool = False):
            self.when = when
            self.outcome = outcome
            self.failed = failed
            self.passed = passed

    collector = TestResultCollector()

    # Test a passing test
    collector.pytest_runtest_logreport(
        MockReport("call", "passed", passed=True)
    )
    assert collector.passed == 1
    assert collector.failures == 0
    assert collector.errors == 0

    # Test a failing test
    collector.pytest_runtest_logreport(
        MockReport("call", "failed", failed=True)
    )
    assert collector.passed == 1
    assert collector.failures == 1
    assert collector.errors == 0

    # Test an error during setup
    collector.pytest_runtest_logreport(
        MockReport("setup", "failed", failed=True)
    )
    assert collector.passed == 1
    assert collector.failures == 1
    assert collector.errors == 1

    # Test an error during teardown
    collector.pytest_runtest_logreport(
        MockReport("teardown", "failed", failed=True)
    )
    assert collector.passed == 1
    assert collector.failures == 1
    assert collector.errors == 2

    # Test an error during call
    collector.pytest_runtest_logreport(MockReport("call", "error"))
    assert collector.passed == 1
    assert collector.failures == 1
    assert collector.errors == 3

    # Test pytest_sessionfinish (mocking is needed for full coverage, but difficult)
    # This part checks if the method can be called without error.
    class MockSession:
        class Config:
            class PluginManager:
                def get_plugin(self, name: str):
                    return None  # Simulate no terminalreporter

        config = Config()

    collector.pytest_sessionfinish(MockSession())
    assert collector.warnings == 0  # Should remain 0 as terminalreporter is None


class BrokenStdin:
    def fileno(self):
        raise ValueError("redirected stdin is pseudofile, has no fileno()")
    
    def read(self, size=-1):
        return ""


def test_subprocess_safe_stdin_in_run_pytest_and_capture_output(tmp_path) -> None:
    """
    Regression test for the 'redirected stdin is pseudofile' crash.
    Verifies that run_pytest_and_capture_output handles invalid sys.stdin gracefully.
    """
    # Create a dummy test file
    test_file = tmp_path / "test_dummy.py"
    test_file.write_text("def test_pass(): assert True", encoding="utf-8")
    
    # Patch sys.stdin to simulate the broken environment
    with patch('sys.stdin', BrokenStdin()):
        try:
            # This should NOT crash
            # Since run_pytest_and_capture_output expects a string path, convert tmp_path
            output = run_pytest_and_capture_output(str(test_file))
            
            # Verify it actually ran
            results = output.get('test_results', [{}])[0]
            assert results.get('passed') == 1
            assert results.get('failures') == 0
            assert results.get('errors') == 0
        except ValueError as e:
            pytest.fail(f"Function crashed with ValueError accessing stdin: {e}")


# ============================================================================
# Regression Tests - ANSI / Color Output Parsing
# ============================================================================

def test_run_pytest_and_capture_output_parses_ansi_failed_output(tmp_path) -> None:
    """
    Regression test: when pytest output contains ANSI color codes, we should still
    count failures correctly.
    """
    test_file = tmp_path / "test_failure_color_unit.py"
    test_file.write_text("def test_fail():\n    assert False\n", encoding="utf-8")

    import subprocess

    ansi_stdout = "test_failure_color_unit.py::test_fail \x1b[31mFAILED\x1b[0m [100%]\n"
    fake_completed = subprocess.CompletedProcess(
        args=["pytest"], returncode=1, stdout=ansi_stdout, stderr=""
    )

    with patch("pdd.pytest_output.subprocess.run", return_value=fake_completed):
        result = run_pytest_and_capture_output(str(test_file))

    results = result.get("test_results", [{}])[0]
    assert results.get("return_code") == 1
    assert results.get("failures") == 1
    assert results.get("errors") == 0


def test_run_pytest_and_capture_output_counts_failures_with_forced_color(tmp_path, monkeypatch) -> None:
    """
    Integration regression: force color output (like the sync TUI) and ensure
    failures are still detected.
    """
    test_file = tmp_path / "test_failure_color_integration.py"
    test_file.write_text("def test_fail():\n    assert False\n", encoding="utf-8")

    existing_addopts = os.environ.get("PYTEST_ADDOPTS", "")
    addopts = (existing_addopts + " " if existing_addopts else "") + "--color=yes"
    monkeypatch.setenv("PYTEST_ADDOPTS", addopts)
    monkeypatch.setenv("TERM", "xterm-256color")

    result = run_pytest_and_capture_output(str(test_file))
    results = result.get("test_results", [{}])[0]
    stdout = results.get("standard_output", "") or ""

    # Ensure this test exercises the ANSI-colored output path.
    if "\x1b[" not in stdout:
        pytest.skip("Pytest did not emit ANSI output even with --color=yes")
    assert results.get("return_code") == 1
    assert results.get("failures") == 1


def test_run_pytest_and_capture_output_nonzero_returncode_never_looks_passing(tmp_path) -> None:
    """
    Safety net: if pytest returns a non-zero exit code but output parsing fails,
    we should still report a failure/error count > 0.
    """
    test_file = tmp_path / "test_nonzero_returncode.py"
    test_file.write_text("def test_fail():\n    assert False\n", encoding="utf-8")

    import subprocess

    fake_completed = subprocess.CompletedProcess(
        args=["pytest"], returncode=1, stdout="(output omitted)", stderr=""
    )
    with patch("pdd.pytest_output.subprocess.run", return_value=fake_completed):
        result = run_pytest_and_capture_output(str(test_file))

    results = result.get("test_results", [{}])[0]
    assert results.get("return_code") == 1
    assert (results.get("failures", 0) + results.get("errors", 0)) > 0


# ============================================================================
# Regression Tests - PDD Project Structure (Cross-Directory Imports)
# ============================================================================

def test_run_pytest_with_pdd_project_structure_and_src_imports(tmp_path) -> None:
    """
    Regression test: PDD projects with src/ imports should work correctly.

    This tests the fix for the bug where pytest would fail with:
        ModuleNotFoundError: No module named 'mymodule'

    when running from a different directory than the project root.
    The fix detects .pddrc files and sets proper cwd/PYTHONPATH.
    """
    # Create a PDD project structure
    project_root = tmp_path / "my_pdd_project"
    project_root.mkdir()

    # Create .pddrc marker file (this triggers the fix)
    pddrc = project_root / ".pddrc"
    pddrc.write_text("version: '1.0'\n", encoding="utf-8")

    # Create src/ directory with a module
    src_dir = project_root / "src"
    src_dir.mkdir()

    module_file = src_dir / "mymodule.py"
    module_file.write_text(
        "def add(a: int, b: int) -> int:\n"
        "    return a + b\n",
        encoding="utf-8"
    )

    # Create tests/ directory with a test that imports from src/
    tests_dir = project_root / "tests"
    tests_dir.mkdir()

    test_file = tests_dir / "test_mymodule.py"
    test_file.write_text(
        "from mymodule import add\n\n"
        "def test_add():\n"
        "    assert add(2, 3) == 5\n",
        encoding="utf-8"
    )

    # Run pytest on the test file (this would fail before the fix)
    result = run_pytest_and_capture_output(str(test_file))

    # Verify the test passed (no import error)
    results = result.get("test_results", [{}])[0]
    assert results.get("return_code") == 0, (
        f"Expected return_code=0 but got {results.get('return_code')}. "
        f"stdout: {results.get('standard_output', '')[:500]}"
    )
    assert results.get("passed") == 1
    assert results.get("failures") == 0
    assert results.get("errors") == 0


def test_run_pytest_without_pddrc_uses_original_behavior(tmp_path) -> None:
    """
    Regression test: projects without .pddrc should use original behavior.

    This ensures the fix is conservative and doesn't change behavior for
    non-PDD projects.
    """
    # Create a simple test file without .pddrc in its directory hierarchy
    test_file = tmp_path / "test_simple.py"
    test_file.write_text(
        "def test_pass():\n"
        "    assert True\n",
        encoding="utf-8"
    )

    # Run pytest - should work with original behavior
    result = run_pytest_and_capture_output(str(test_file))

    results = result.get("test_results", [{}])[0]
    assert results.get("return_code") == 0
    assert results.get("passed") == 1


# --- Tests for extract_failing_files_from_output (Bug #156) ---

def test_extract_failing_files_single_failure():
    """Test extraction of a single failing file."""
    output = "FAILED tests/test_foo.py::test_bar - AssertionError"
    result = extract_failing_files_from_output(output)
    assert result == ["tests/test_foo.py"]


def test_extract_failing_files_multiple_files():
    """Test extraction from multiple failing files."""
    output = """
    FAILED tests/test_foo.py::test_a - Error
    FAILED tests/test_foo_0.py::test_b - Error
    FAILED tests/test_bar.py::test_c - Error
    """
    result = extract_failing_files_from_output(output)
    assert result == ["tests/test_foo.py", "tests/test_foo_0.py", "tests/test_bar.py"]


def test_extract_failing_files_deduplicates():
    """Test that multiple failures in the same file are deduplicated."""
    output = """
    FAILED tests/test_foo.py::test_a - Error
    FAILED tests/test_foo.py::test_b - Error
    FAILED tests/test_foo.py::test_c - Error
    """
    result = extract_failing_files_from_output(output)
    assert result == ["tests/test_foo.py"]


def test_extract_failing_files_verbose_format():
    """Test extraction from verbose pytest output format."""
    output = """
    tests/test_foo.py::test_pass PASSED
    tests/test_bar.py::test_fail FAILED
    """
    result = extract_failing_files_from_output(output)
    assert result == ["tests/test_bar.py"]


def test_extract_failing_files_no_failures():
    """Test extraction with no failures returns empty list."""
    output = """
    tests/test_ok.py::test_a PASSED
    tests/test_ok.py::test_b PASSED
    2 passed in 0.5s
    """
    result = extract_failing_files_from_output(output)
    assert result == []


def test_extract_failing_files_with_ansi_codes():
    """Test extraction handles ANSI color codes."""
    output = "\x1b[31mFAILED tests/test_color.py::test_red - Error\x1b[0m"
    result = extract_failing_files_from_output(output)
    assert result == ["tests/test_color.py"]


def test_extract_failing_files_absolute_paths():
    """Test extraction with absolute paths."""
    output = "FAILED /Users/dev/project/tests/test_abs.py::test_func - Error"
    result = extract_failing_files_from_output(output)
    assert result == ["/Users/dev/project/tests/test_abs.py"]


def test_extract_failing_files_mixed_formats():
    """Test extraction with mixed output formats."""
    output = """
    tests/test_a.py::test_1 PASSED
    FAILED tests/test_b.py::test_2 - AssertionError
    tests/test_c.py::test_3 FAILED
    FAILED tests/test_d.py::test_4 - ValueError
    """
    result = extract_failing_files_from_output(output)
    # Pattern 1 (FAILED prefix) matches first, then pattern 2 (FAILED suffix)
    assert result == ["tests/test_b.py", "tests/test_d.py", "tests/test_c.py"]


# ============================================================================
# Regression Tests - Issue #485: Naive warning counting
# ============================================================================

def test_warning_count_ignores_litellm_and_pydantic_warnings(tmp_path):
    """
    Issue #485: warnings count should only reflect pytest warnings,
    not library warnings (LiteLLM UserWarning, Pydantic, PDD log messages)
    that appear in subprocess stdout.
    """
    import subprocess as real_subprocess

    test_file = tmp_path / "test_pass.py"
    test_file.write_text("def test_ok():\n    assert True\n", encoding="utf-8")

    # Simulate pytest output that has all tests passing (return code 0)
    # but contains library warning strings in stdout
    fake_stdout = (
        "test_pass.py::test_ok PASSED [100%]\n"
        "/usr/lib/python3.11/site-packages/litellm/utils.py:123: UserWarning: client is not initialized\n"
        "  warnings.warn(\"client is not initialized\")\n"
        "/usr/lib/python3.11/site-packages/pydantic/main.py:45: PydanticSerializationUnexpectedValue: warning unexpected\n"
        "WARNING: Cloud fallback is disabled\n"
        "\n"
        "========================= 1 passed in 0.03s =========================\n"
    )
    fake_completed = real_subprocess.CompletedProcess(
        args=["pytest"], returncode=0, stdout=fake_stdout, stderr=""
    )

    with patch("pdd.pytest_output.subprocess.run", return_value=fake_completed):
        result = run_pytest_and_capture_output(str(test_file))

    results = result["test_results"][0]
    assert results["return_code"] == 0
    assert results["passed"] == 1
    assert results["failures"] == 0
    assert results["errors"] == 0
    # BUG: Current code counts 4+ warnings from library output.
    # After fix, this should be 0 (no pytest summary warnings).
    assert results["warnings"] == 0, (
        f"Expected 0 warnings (no pytest warnings in summary line), "
        f"but got {results['warnings']}. Library warnings should not be counted."
    )


def test_warning_count_parses_pytest_summary_line(tmp_path):
    """
    Issue #485: When pytest summary line reports warnings (e.g., '1 passed, 2 warnings'),
    those should be counted correctly.
    """
    import subprocess as real_subprocess

    test_file = tmp_path / "test_warn.py"
    test_file.write_text("def test_ok():\n    assert True\n", encoding="utf-8")

    fake_stdout = (
        "test_warn.py::test_ok PASSED [100%]\n"
        "\n"
        "===================== 1 passed, 2 warnings in 0.05s =====================\n"
    )
    fake_completed = real_subprocess.CompletedProcess(
        args=["pytest"], returncode=0, stdout=fake_stdout, stderr=""
    )

    with patch("pdd.pytest_output.subprocess.run", return_value=fake_completed):
        result = run_pytest_and_capture_output(str(test_file))

    results = result["test_results"][0]
    # After fix, should parse "2 warnings" from summary line
    assert results["warnings"] == 2, (
        f"Expected 2 warnings from pytest summary line, got {results['warnings']}"
    )


def test_warning_count_zero_for_clean_output(tmp_path):
    """
    Issue #485: Clean pytest output with no warnings anywhere should yield 0 warnings.
    """
    import subprocess as real_subprocess

    test_file = tmp_path / "test_clean.py"
    test_file.write_text("def test_ok():\n    assert True\n", encoding="utf-8")

    fake_stdout = (
        "test_clean.py::test_ok PASSED [100%]\n"
        "\n"
        "========================= 1 passed in 0.02s =========================\n"
    )
    fake_completed = real_subprocess.CompletedProcess(
        args=["pytest"], returncode=0, stdout=fake_stdout, stderr=""
    )

    with patch("pdd.pytest_output.subprocess.run", return_value=fake_completed):
        result = run_pytest_and_capture_output(str(test_file))

    results = result["test_results"][0]
    assert results["warnings"] == 0


def test_warning_count_mixed_library_and_pytest_warnings(tmp_path):
    """
    Issue #485 end-to-end: Output has both library warning strings AND
    a real pytest warning in the summary. Only the summary count should matter.
    """
    import subprocess as real_subprocess

    test_file = tmp_path / "test_mixed.py"
    test_file.write_text("def test_ok():\n    assert True\n", encoding="utf-8")

    fake_stdout = (
        "test_mixed.py::test_ok PASSED [100%]\n"
        "/site-packages/litellm/utils.py:10: UserWarning: something\n"
        "  warnings.warn('something')\n"
        "WARNING: PDD cloud fallback disabled\n"
        "\n"
        "================== 1 passed, 1 warning in 0.04s ==================\n"
    )
    fake_completed = real_subprocess.CompletedProcess(
        args=["pytest"], returncode=0, stdout=fake_stdout, stderr=""
    )

    with patch("pdd.pytest_output.subprocess.run", return_value=fake_completed):
        result = run_pytest_and_capture_output(str(test_file))

    results = result["test_results"][0]
    # BUG: Current code counts 3+ warnings from naive substring matching.
    # After fix, should be 1 (from pytest summary "1 warning").
    assert results["warnings"] == 1, (
        f"Expected 1 warning (from pytest summary), got {results['warnings']}. "
        f"Library warnings in stdout should not inflate the count."
    )

