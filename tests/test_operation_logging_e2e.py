"""
E2E Regression Tests for Issue #277: Unified Operation Logging for PDD Commands.

These tests verify that CLI commands correctly log their operations with
invocation_mode="manual" when invoked directly (not via sync).

These are REAL E2E tests with actual LLM calls - no mocking.

Run with: pytest tests/test_operation_logging_e2e.py -v -m e2e
Skip in CI: pytest tests/ -v -m "not e2e"

Estimated cost per full run: ~$0.10-0.50 (using minimal prompts)
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, List, Any

import pytest


# Mark all tests in this module as e2e (slow, uses real LLM)
pytestmark = pytest.mark.e2e


class TestOperationLoggingE2E:
    """E2E tests verifying CLI commands log with invocation_mode='manual'."""

    @pytest.fixture
    def project_dir(self, tmp_path: Path) -> Path:
        """Create a minimal PDD project structure."""
        # Create directories
        (tmp_path / "prompts").mkdir()
        (tmp_path / "src").mkdir()
        (tmp_path / "tests").mkdir()
        (tmp_path / "examples").mkdir()

        return tmp_path

    def get_log_entries(
        self,
        project_dir: Path,
        basename: str,
        language: str = "python"
    ) -> List[Dict[str, Any]]:
        """Read all log entries from a module's sync log."""
        log_path = project_dir / ".pdd" / "meta" / f"{basename}_{language}_sync.log"
        if not log_path.exists():
            return []

        entries = []
        for line in log_path.read_text().splitlines():
            if line.strip():
                try:
                    entries.append(json.loads(line))
                except json.JSONDecodeError:
                    continue
        return entries

    def get_latest_entry(
        self,
        project_dir: Path,
        basename: str,
        language: str = "python"
    ) -> Dict[str, Any] | None:
        """Get the most recent log entry for a module."""
        entries = self.get_log_entries(project_dir, basename, language)
        return entries[-1] if entries else None

    def run_pdd_command(
        self,
        args: List[str],
        cwd: Path,
        timeout: int = 120
    ) -> subprocess.CompletedProcess:
        """Run a pdd command and return the result."""
        result = subprocess.run(
            ["pdd"] + args,
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=timeout,
            env={**os.environ, "PDD_FORCE": "1"}  # Skip interactive prompts
        )
        return result

    # =========================================================================
    # Test: generate command
    # =========================================================================
    def test_generate_logs_manual_invocation(self, project_dir: Path):
        """
        E2E: `pdd generate` should create log entry with invocation_mode='manual'.
        """
        # Create minimal prompt
        prompt_file = project_dir / "prompts" / "tiny_python.prompt"
        prompt_file.write_text(
            "% You are a Python engineer.\n"
            "% Write a function called `get_answer` that returns the integer 42.\n"
            "% The function takes no arguments.\n"
        )

        output_file = project_dir / "src" / "tiny.py"

        # Run generate
        result = self.run_pdd_command(
            ["generate", str(prompt_file), "--output", str(output_file)],
            cwd=project_dir,
            timeout=300  # 5 minutes for LLM API call (matches other E2E tests)
        )

        # Verify command succeeded
        assert result.returncode == 0, f"generate failed: {result.stderr}"
        assert output_file.exists(), "Output file not created"

        # Verify log entry
        entry = self.get_latest_entry(project_dir, "tiny")
        assert entry is not None, "No log entry created"
        assert entry["operation"] == "generate", f"Wrong operation: {entry['operation']}"
        assert entry["invocation_mode"] == "manual", f"Wrong mode: {entry['invocation_mode']}"
        assert entry["success"] is True, f"Operation marked as failed: {entry}"

    # =========================================================================
    # Test: test command
    # =========================================================================
    def test_test_logs_manual_invocation(self, project_dir: Path):
        """
        E2E: `pdd test` should create log entry with invocation_mode='manual'.
        """
        # Create prompt
        prompt_file = project_dir / "prompts" / "adder_python.prompt"
        prompt_file.write_text(
            "% You are a Python engineer.\n"
            "% Write a function called `add` that takes two integers and returns their sum.\n"
        )

        # Create code file (the test command needs existing code)
        code_file = project_dir / "src" / "adder.py"
        code_file.write_text(
            "def add(a: int, b: int) -> int:\n"
            "    return a + b\n"
        )

        output_file = project_dir / "tests" / "test_adder.py"

        # Run test generation
        result = self.run_pdd_command(
            ["test", str(prompt_file), str(code_file), "--output", str(output_file)],
            cwd=project_dir,
            timeout=300  # 5 minutes for LLM API call (matches other E2E tests)
        )

        # Verify command succeeded
        assert result.returncode == 0, f"test failed: {result.stderr}"
        assert output_file.exists(), "Test file not created"

        # Verify log entry
        entry = self.get_latest_entry(project_dir, "adder")
        assert entry is not None, "No log entry created"
        assert entry["operation"] == "test", f"Wrong operation: {entry['operation']}"
        assert entry["invocation_mode"] == "manual", f"Wrong mode: {entry['invocation_mode']}"

    # =========================================================================
    # Test: example command
    # =========================================================================
    def test_example_logs_manual_invocation(self, project_dir: Path):
        """
        E2E: `pdd example` should create log entry with invocation_mode='manual'.
        """
        # Create prompt
        prompt_file = project_dir / "prompts" / "greeter_python.prompt"
        prompt_file.write_text(
            "% You are a Python engineer.\n"
            "% Write a function called `greet` that takes a name string and returns 'Hello, {name}!'.\n"
        )

        # Create code file
        code_file = project_dir / "src" / "greeter.py"
        code_file.write_text(
            "def greet(name: str) -> str:\n"
            "    return f'Hello, {name}!'\n"
        )

        output_file = project_dir / "examples" / "greeter_example.py"

        # Run example generation
        result = self.run_pdd_command(
            ["example", str(prompt_file), str(code_file), "--output", str(output_file)],
            cwd=project_dir
        )

        # Verify command succeeded
        assert result.returncode == 0, f"example failed: {result.stderr}"
        assert output_file.exists(), "Example file not created"

        # Verify log entry
        entry = self.get_latest_entry(project_dir, "greeter")
        assert entry is not None, "No log entry created"
        assert entry["operation"] == "example", f"Wrong operation: {entry['operation']}"
        assert entry["invocation_mode"] == "manual", f"Wrong mode: {entry['invocation_mode']}"

    # =========================================================================
    # Test: crash command
    # =========================================================================
    def test_crash_logs_manual_invocation(self, project_dir: Path):
        """
        E2E: `pdd crash` should create log entry with invocation_mode='manual'.
        """
        # Create prompt
        prompt_file = project_dir / "prompts" / "divider_python.prompt"
        prompt_file.write_text(
            "% You are a Python engineer.\n"
            "% Write a function called `divide` that takes two numbers and returns their quotient.\n"
            "% Handle division by zero by returning None.\n"
        )

        # Create code file with a bug (doesn't handle division by zero)
        code_file = project_dir / "src" / "divider.py"
        code_file.write_text(
            "def divide(a: float, b: float) -> float:\n"
            "    return a / b  # Bug: no zero check\n"
        )

        # Create example that crashes
        example_file = project_dir / "examples" / "divider_example.py"
        example_file.write_text(
            "from src.divider import divide\n"
            "print(divide(10, 0))  # This will crash\n"
        )

        # Create error file
        error_file = project_dir / "error.txt"
        error_file.write_text(
            "Traceback (most recent call last):\n"
            "  File \"examples/divider_example.py\", line 2, in <module>\n"
            "    print(divide(10, 0))\n"
            "  File \"src/divider.py\", line 2, in divide\n"
            "    return a / b\n"
            "ZeroDivisionError: division by zero\n"
        )

        # Run crash fix (longer timeout for iterative fixing)
        result = self.run_pdd_command(
            ["crash", str(prompt_file), str(code_file), str(example_file), str(error_file)],
            cwd=project_dir,
            timeout=300  # 5 minutes for iterative fix loop
        )

        # crash may or may not fully succeed, but it should log
        # Verify log entry exists
        entry = self.get_latest_entry(project_dir, "divider")
        assert entry is not None, "No log entry created"
        assert entry["operation"] == "crash", f"Wrong operation: {entry['operation']}"
        assert entry["invocation_mode"] == "manual", f"Wrong mode: {entry['invocation_mode']}"

    # =========================================================================
    # Test: verify command
    # =========================================================================
    def test_verify_logs_manual_invocation(self, project_dir: Path):
        """
        E2E: `pdd verify` should create log entry with invocation_mode='manual'.
        """
        # Create prompt
        prompt_file = project_dir / "prompts" / "doubler_python.prompt"
        prompt_file.write_text(
            "% You are a Python engineer.\n"
            "% Write a function called `double` that takes an integer and returns it multiplied by 2.\n"
        )

        # Create code file
        code_file = project_dir / "src" / "doubler.py"
        code_file.write_text(
            "def double(n: int) -> int:\n"
            "    return n * 2\n"
        )

        # Create example
        example_file = project_dir / "examples" / "doubler_example.py"
        example_file.write_text(
            "from src.doubler import double\n"
            "print(double(21))  # Should print 42\n"
        )

        # Run verify (longer timeout for verification loop)
        result = self.run_pdd_command(
            ["verify", str(prompt_file), str(code_file), str(example_file)],
            cwd=project_dir,
            timeout=300  # 5 minutes for verification loop
        )

        # Verify log entry exists (verify may fail but should still log)
        entry = self.get_latest_entry(project_dir, "doubler")
        assert entry is not None, "No log entry created"
        assert entry["operation"] == "verify", f"Wrong operation: {entry['operation']}"
        assert entry["invocation_mode"] == "manual", f"Wrong mode: {entry['invocation_mode']}"

    # =========================================================================
    # Test: fix command (manual mode)
    # =========================================================================
    def test_fix_manual_logs_manual_invocation(self, project_dir: Path):
        """
        E2E: `pdd fix --manual` should create log entry with invocation_mode='manual'.
        """
        # Create prompt
        prompt_file = project_dir / "prompts" / "squarer_python.prompt"
        prompt_file.write_text(
            "% You are a Python engineer.\n"
            "% Write a function called `square` that takes an integer and returns its square.\n"
        )

        # Create code file with a bug
        code_file = project_dir / "src" / "squarer.py"
        code_file.write_text(
            "def square(n: int) -> int:\n"
            "    return n + n  # Bug: should be n * n\n"
        )

        # Create failing test
        test_file = project_dir / "tests" / "test_squarer.py"
        test_file.write_text(
            "from src.squarer import square\n"
            "\n"
            "def test_square():\n"
            "    assert square(5) == 25  # Will fail with buggy code\n"
        )

        # Create error file
        error_file = project_dir / "error.txt"
        error_file.write_text(
            "FAILED tests/test_squarer.py::test_square - AssertionError: assert 10 == 25\n"
        )

        # Run fix in manual mode
        result = self.run_pdd_command(
            ["fix", "--manual", str(prompt_file), str(code_file), str(test_file), str(error_file)],
            cwd=project_dir
        )

        # Verify log entry exists
        entry = self.get_latest_entry(project_dir, "squarer")
        assert entry is not None, "No log entry created"
        assert entry["operation"] == "fix", f"Wrong operation: {entry['operation']}"
        assert entry["invocation_mode"] == "manual", f"Wrong mode: {entry['invocation_mode']}"

    # =========================================================================
    # Test: update command (edge case - no prompt_file)
    # =========================================================================
    def test_update_silently_skips_logging(self, project_dir: Path):
        """
        E2E: `pdd update` has no prompt_file, so logging should be silently skipped.

        The decorator still runs but cannot infer module identity without prompt_file.
        """
        # Create a code file to update
        code_file = project_dir / "src" / "sample.py"
        code_file.write_text(
            "def sample():\n"
            "    return 'sample'\n"
        )

        # Run update on single file
        result = self.run_pdd_command(
            ["update", str(code_file)],
            cwd=project_dir
        )

        # Command should complete (may succeed or fail, but not crash)
        # The key assertion: no log entry for "update" operation should exist
        # because update doesn't have a prompt_file parameter

        # Check that no update operation was logged
        # (since there's no prompt_file, the decorator can't infer module identity)
        meta_dir = project_dir / ".pdd" / "meta"
        if meta_dir.exists():
            for log_file in meta_dir.glob("*_sync.log"):
                entries = []
                for line in log_file.read_text().splitlines():
                    if line.strip():
                        try:
                            entries.append(json.loads(line))
                        except json.JSONDecodeError:
                            continue
                update_entries = [e for e in entries if e.get("operation") == "update"]
                assert len(update_entries) == 0, \
                    f"update should not log without prompt_file, but found: {update_entries}"


class TestSyncLogsWithSyncMode:
    """Verify that sync-initiated operations log with invocation_mode='sync'."""

    @pytest.fixture
    def project_dir(self, tmp_path: Path) -> Path:
        """Create a minimal PDD project for sync testing."""
        (tmp_path / "prompts").mkdir()
        (tmp_path / "src").mkdir()
        return tmp_path

    def get_log_entries(
        self,
        project_dir: Path,
        basename: str,
        language: str = "python"
    ) -> List[Dict[str, Any]]:
        """Read all log entries from a module's sync log."""
        log_path = project_dir / ".pdd" / "meta" / f"{basename}_{language}_sync.log"
        if not log_path.exists():
            return []

        entries = []
        for line in log_path.read_text().splitlines():
            if line.strip():
                try:
                    entries.append(json.loads(line))
                except json.JSONDecodeError:
                    continue
        return entries

    def test_sync_logs_with_sync_mode(self, project_dir: Path):
        """
        E2E: Operations triggered by `pdd sync` should have invocation_mode='sync'.
        """
        # Create a simple prompt
        prompt_file = project_dir / "prompts" / "counter_python.prompt"
        prompt_file.write_text(
            "% You are a Python engineer.\n"
            "% Write a function called `count` that returns the length of a list.\n"
        )

        # Run sync (this will trigger generate internally)
        result = subprocess.run(
            ["pdd", "sync", "counter", "--skip-tests", "--skip-verify", "--budget", "2.0"],
            cwd=project_dir,
            capture_output=True,
            text=True,
            timeout=180,
            env={**os.environ, "PDD_FORCE": "1"}
        )

        # Check log entries - sync-initiated operations should have invocation_mode='sync'
        entries = self.get_log_entries(project_dir, "counter")

        # There should be at least one entry from sync
        sync_entries = [e for e in entries if e.get("invocation_mode") == "sync"]
        assert len(sync_entries) > 0, \
            f"Expected sync-mode entries, got: {[e.get('invocation_mode') for e in entries]}"
