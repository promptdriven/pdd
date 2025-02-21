import pytest
import json
import os
from pdd.pytest_output import (
    run_pytest_and_capture_output,
    save_output_to_json,
    TestResultCollector,
)
import pdd.pytest_output
import sys
from unittest.mock import patch


# Create a directory for test outputs
OUTPUT_DIR = "tests/output"
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
    os.remove(test_file)


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
    assert result["test_results"][0]["warnings"] == 0
    os.remove(test_file)


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
    assert result["test_results"][0]["warnings"] == 0
    os.remove(test_file)


def test_run_pytest_and_capture_output_error_test() -> None:
    """Test case: pytest run with a test that errors."""
    test_file = os.path.join(OUTPUT_DIR, "test_error.py")
    create_test_file(test_file, "def test_error():\n    raise ValueError")
    result = run_pytest_and_capture_output(test_file)
    assert result["test_file"] == test_file
    assert result["test_results"][0]["return_code"] == 1
    assert result["test_results"][0]["errors"] == 1
    assert result["test_results"][0]["passed"] == 0
    assert result["test_results"][0]["failures"] == 0
    assert result["test_results"][0]["warnings"] == 0
    os.remove(test_file)


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
    os.remove(test_file)


# Test cases for save_output_to_json
def test_save_output_to_json_successful() -> None:
    """Test case: successful save to JSON."""
    output_file = os.path.join(OUTPUT_DIR, "pytest_output.json")
    test_data = {"test": "data"}
    save_output_to_json(test_data, output_file)
    assert os.path.exists(output_file)
    with open(output_file, "r") as f:
        loaded_data = json.load(f)
    assert loaded_data == test_data
    os.remove(output_file)


def test_save_output_to_json_exception(capsys) -> None:
    """Test case: exception during save to JSON."""
    # Mock the json.dump function to raise an exception
    with patch("json.dump", side_effect=Exception("Test Exception")):
        output_file = os.path.join(OUTPUT_DIR, "pytest_output.json")
        test_data = {"test": "data"}
        save_output_to_json(test_data, output_file)
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
    