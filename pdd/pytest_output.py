import argparse
import json
import io
import re
import sys
import pytest
import subprocess
from pathlib import Path
from rich.console import Console
from rich.pretty import pprint
import os
from .python_env_detector import detect_host_python_executable

console = Console()


def _find_project_root(test_file: Path) -> Path | None:
    """
    Find the project root directory by looking for .pddrc (definitive PDD marker).

    Only .pddrc is used as the project marker to ensure we don't incorrectly
    identify project roots for non-PDD projects. This is a conservative approach
    that maintains backward compatibility.

    Args:
        test_file: Path to the test file

    Returns:
        The project root directory if .pddrc is found, None otherwise.
        When None is returned, the caller should use original behavior.
    """
    current = test_file.resolve().parent

    # Walk up the directory tree looking for .pddrc only
    while current != current.parent:
        if (current / ".pddrc").exists():
            return current
        current = current.parent

    # No .pddrc found - return None to signal original behavior should be used
    return None


_ANSI_ESCAPE_RE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")


def _strip_ansi(text: str) -> str:
    """Remove ANSI escape sequences from text for reliable parsing."""
    return _ANSI_ESCAPE_RE.sub("", text)


def extract_failing_files_from_output(pytest_output: str) -> list[str]:
    """
    Extract unique file paths from pytest FAILED output lines.

    Parses patterns like:
    - FAILED tests/test_foo.py::test_name - error message
    - tests/test_foo.py::test_name FAILED

    Args:
        pytest_output: The combined stdout/stderr from a pytest run

    Returns:
        List of unique file paths (without ::test_name suffix) that had failures,
        in the order they were first encountered.
    """
    cleaned_output = _strip_ansi(pytest_output)

    failing_files = []
    seen = set()

    # Pattern 1: FAILED path/file.py::test_name (with optional error)
    pattern1 = r'FAILED\s+([^\s:]+\.py)::'
    for match in re.finditer(pattern1, cleaned_output):
        file_path = match.group(1)
        if file_path not in seen:
            failing_files.append(file_path)
            seen.add(file_path)

    # Pattern 2: path/file.py::test_name FAILED (verbose output)
    pattern2 = r'([^\s:]+\.py)::\S+\s+FAILED'
    for match in re.finditer(pattern2, cleaned_output):
        file_path = match.group(1)
        if file_path not in seen:
            failing_files.append(file_path)
            seen.add(file_path)

    return failing_files


class TestResultCollector:
    __test__ = False  # Prevent pytest from collecting this plugin as a test

    def __init__(self):
        self.failures = 0
        self.errors = 0
        self.warnings = 0
        self.passed = 0
        self.logs = io.StringIO()
        self.stdout = ""
        self.stderr = ""

    def pytest_runtest_logreport(self, report):
        """
        Treat any failing 'call' phase as a test failure (matching what Pytest calls 'failed'),
        and only count setup/teardown failures (or 'report.outcome == "error"') as errors.
        """
        # 'report.when' can be "setup", "call", or "teardown"
        if report.when == "call":
            if report.passed:
                self.passed += 1
            elif report.failed:
                # All exceptions that occur in the test body are 'failures'
                self.failures += 1
            elif report.outcome == "error":
                # Not frequently used, but included for completeness
                self.errors += 1
        elif report.when in ("setup", "teardown") and report.failed:
            # Setup/teardown failures are 'errors'
            self.errors += 1

    def pytest_sessionfinish(self, session):
        """Capture warnings from pytest session."""
        if hasattr(session.config, 'pluginmanager'):
            terminal_reporter = session.config.pluginmanager.get_plugin("terminalreporter")
            if terminal_reporter:
                self.warnings = len(terminal_reporter.stats.get("warnings", []))

    def capture_logs(self):
        """Redirect stdout and stderr to capture logs."""
        sys.stdout = self.logs
        sys.stderr = self.logs

    def get_logs(self):
        """Return captured logs and reset stdout/stderr."""
        self.stdout = self.logs.getvalue()
        self.stderr = self.logs.getvalue()
        sys.stdout = sys.__stdout__
        sys.stderr = sys.__stderr__
        return self.stdout, self.stderr

def run_pytest_and_capture_output(test_file: str) -> dict:
    """
    Runs pytest on the given test file and captures the output.

    Args:
        test_file: The path to the test file.

    Returns:
        A dictionary containing the pytest output.
    """
    if not os.path.exists(test_file):
        console.print(f"[bold red]Error: Test file '{test_file}' not found.[/]")
        return {}

    if not test_file.endswith(".py"):
        console.print(
            f"[bold red]Error: Test file '{test_file}' must be a Python file (.py).[/]"
        )
        return {}

    # Use environment-aware Python executable for pytest execution
    python_executable = detect_host_python_executable()

    # Find the project root directory for proper pytest execution (PDD projects only)
    test_path = Path(test_file).resolve()
    project_root = _find_project_root(test_path)

    # Build subprocess kwargs - only modify cwd/env for PDD projects (.pddrc found)
    subprocess_kwargs = {
        "capture_output": True,
        "text": True,
        "timeout": 300,
        "stdin": subprocess.DEVNULL,
    }

    pytest_args = [python_executable, "-B", "-m", "pytest", str(test_path), "-v"]

    if project_root is not None:
        # PDD project detected - set up proper environment
        subprocess_kwargs["cwd"] = str(project_root)

        # Build PYTHONPATH with both project root and src/ if it exists
        paths_to_add = [str(project_root)]
        src_dir = project_root / "src"
        if src_dir.is_dir():
            paths_to_add.insert(0, str(src_dir))  # src/ takes priority

        env = os.environ.copy()
        existing_pythonpath = env.get("PYTHONPATH", "")
        if existing_pythonpath:
            paths_to_add.append(existing_pythonpath)
        env["PYTHONPATH"] = os.pathsep.join(paths_to_add)
        subprocess_kwargs["env"] = env

        # Add --rootdir to ensure pytest uses project's config
        pytest_args.append(f"--rootdir={project_root}")

    try:
        # Run pytest using subprocess with the detected Python executable
        # Use -B flag to disable bytecode caching, ensuring fresh imports
        result = subprocess.run(pytest_args, **subprocess_kwargs)
        
        stdout = result.stdout
        stderr = result.stderr
        return_code = result.returncode
        parse_stdout = _strip_ansi(stdout or "")
        
        # Parse the output to extract test results
        # Count passed, failed, and skipped tests from the output
        passed = parse_stdout.count(" PASSED")
        failures = parse_stdout.count(" FAILED") + parse_stdout.count(" ERROR")
        errors = 0  # Will be included in failures for subprocess execution
        warnings = parse_stdout.lower().count("warning")
        
        # If return code is 2, it indicates a pytest error
        if return_code == 2:
            errors = 1
        # Safety net: if parsing missed failures due to formatting (e.g., ANSI colors),
        # never report a passing result on a non-zero return code.
        if return_code != 0 and failures == 0 and errors == 0:
            if return_code == 1:
                failures = 1
            else:
                errors = 1

        return {
            "test_file": test_file,
            "test_results": [
                {
                    "standard_output": stdout,
                    "standard_error": stderr,
                    "return_code": return_code,
                    "warnings": warnings,
                    "errors": errors,
                    "failures": failures,
                    "passed": passed,
                }
            ],
        }
    except subprocess.TimeoutExpired:
        return {
            "test_file": test_file,
            "test_results": [
                {
                    "standard_output": "",
                    "standard_error": "Test execution timed out",
                    "return_code": -1,
                    "warnings": 0,
                    "errors": 1,
                    "failures": 0,
                    "passed": 0,
                }
            ],
        }
    except Exception as e:
        return {
            "test_file": test_file,
            "test_results": [
                {
                    "standard_output": "",
                    "standard_error": f"Error running pytest: {str(e)}",
                    "return_code": -1,
                    "warnings": 0,
                    "errors": 1,
                    "failures": 0,
                    "passed": 0,
                }
            ],
        }

def save_output_to_json(output: dict, output_file: str = "pytest.json"):
    """
    Saves the pytest output to a JSON file.

    Args:
        output: The dictionary containing the pytest output.
        output_file: The name of the output JSON file. Defaults to "pytest.json".
    """
    try:
        with open(output_file, "w", encoding="utf-8") as f:
            json.dump(output, f, indent=4)
        console.print(
            f"[green]Pytest output saved to '{output_file}'.[/green]"
        )
    except Exception as e:
        console.print(
            f"[bold red]Error saving output to JSON: {e}[/]"
        )

def main():
    """
    Main function for the pytest_output CLI tool.
    """
    parser = argparse.ArgumentParser(
        description="Capture pytest output and save it to a JSON file."
    )
    parser.add_argument(
        "test_file", type=str, help="Path to the test file."
    )
    parser.add_argument(
        "--json-only", action="store_true", help="Output only JSON to stdout."
    )
    args = parser.parse_args()

    pytest_output = run_pytest_and_capture_output(args.test_file)

    if args.json_only:
        # Print only valid JSON to stdout.
        print(json.dumps(pytest_output))
    else:
        console.print(f"Running pytest on: [blue]{args.test_file}[/blue]")
        pprint(pytest_output, console=console)  # Pretty print the output
        save_output_to_json(pytest_output)

if __name__ == "__main__":
    main()
