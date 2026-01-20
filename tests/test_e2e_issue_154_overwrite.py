"""
E2E Test for Issue #154: Generation overwrite a file doesn't always happen

This test exercises the full CLI path from `pdd generate` to verify that when
the output path resolution fails (returns empty/None), the command either:
1. Raises an error BEFORE calling the expensive LLM, or
2. At minimum, returns a non-zero exit code

The bug: When generate_output_paths returns empty dict (due to empty basename),
output_file_paths.get("output") returns None/empty, and the file write is
silently skipped at code_generator_main.py:1087. The user may have confirmed
overwrite, the LLM is called (costing money), but the file is never written.

This E2E test:
1. Sets up a temp project with a prompt file that triggers the bug
2. Runs the generate command through Click's CliRunner
3. Mocks generate_output_paths to return empty dict (simulating the bug trigger)
4. Verifies the command fails with an error instead of silently skipping

The test should FAIL on buggy code (silent skip, exit code 0) and PASS once fixed.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import Dict, Any
from unittest.mock import patch, MagicMock

import pytest
from click.testing import CliRunner


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory for all tests in this module."""
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


class TestIssue154OverwriteE2E:
    """
    E2E tests for Issue #154: Verify that file generation fails explicitly
    when output path resolution fails, rather than silently skipping the write.

    These tests use Click's CliRunner to exercise the full CLI path.
    """

    @pytest.fixture
    def project_dir(self, tmp_path: Path) -> Path:
        """Create a minimal PDD project structure."""
        (tmp_path / "prompts").mkdir()
        (tmp_path / "src").mkdir()
        return tmp_path

    def test_generate_fails_when_output_path_is_empty(
        self, project_dir: Path, monkeypatch
    ):
        """
        E2E Test: `pdd generate` should fail explicitly when output path
        cannot be resolved, NOT silently skip the file write.

        This test simulates the bug trigger by mocking generate_output_paths
        to return an empty dict, which causes output_file_paths.get("output")
        to return None.

        Expected behavior (after fix):
        - Command should fail with non-zero exit code
        - Error message should indicate output path issue
        - LLM should NOT be called (to avoid wasting money)

        Bug behavior (Issue #154):
        - Command exits with code 0
        - File write is silently skipped
        - Only a warning is printed to console
        - LLM IS called (wasting money)
        """
        # Create a simple prompt file
        prompt_file = project_dir / "prompts" / "test_issue_154.prompt"
        prompt_file.write_text(
            "% You are a Python engineer.\n"
            "% Write a function that returns 42.\n"
        )

        monkeypatch.chdir(project_dir)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-openai-key-for-testing")

        # Track if LLM was called (it shouldn't be when output path is invalid)
        llm_called = False

        def mock_local_generator_func(*args, **kwargs):
            """Mock the local code generator to track if it was called."""
            nonlocal llm_called
            llm_called = True
            return ("def answer():\n    return 42", 0.01, "mock-model")

        def mock_construct_paths(*args, **kwargs):
            """
            Mock construct_paths to return falsy output path.

            This simulates the downstream effect: when generate_output_paths
            returns {}, construct_paths returns output_file_paths with
            "output" key being None or empty string.
            """
            return (
                {},  # resolved_config
                {"prompt_file": "test content"},  # input_files
                {"output": None},  # output_file_paths - THE BUG TRIGGER
                "python"  # language
            )

        with patch('pdd.code_generator_main.construct_paths', side_effect=mock_construct_paths):
            with patch('pdd.code_generator_main.local_code_generator_func', side_effect=mock_local_generator_func):
                from pdd import cli

                runner = CliRunner()
                result = runner.invoke(cli.cli, [
                    "--local",
                    "--force",
                    "generate",
                    str(prompt_file),
                ], catch_exceptions=False)

        # THE KEY ASSERTIONS - These FAIL on buggy code

        # BUG CHECK 1: Exit code should be non-zero when output path fails
        # CURRENT BUG: Exit code is 0 (success) even though file wasn't written
        assert result.exit_code != 0, (
            f"BUG DETECTED (Issue #154): Command exited with code 0 despite no file being written!\n\n"
            f"When output_path cannot be resolved, the generate command should fail explicitly.\n"
            f"Instead, it silently skipped the file write and exited successfully.\n\n"
            f"Exit code: {result.exit_code}\n"
            f"Output:\n{result.output}\n\n"
            f"Expected: Non-zero exit code indicating failure\n"
            f"Actual: Exit code 0 (success) with silent warning"
        )

        # BUG CHECK 2: LLM should NOT be called when output path is invalid
        # CURRENT BUG: LLM IS called, wasting money on code that won't be written
        assert not llm_called, (
            f"BUG DETECTED (Issue #154): LLM was called despite invalid output path!\n\n"
            f"The output path should be validated BEFORE calling the expensive LLM.\n"
            f"Currently, money is wasted generating code that will never be written.\n\n"
            f"Expected: LLM not called when output path is invalid\n"
            f"Actual: LLM was called"
        )

    def test_generate_fails_when_output_path_is_empty_string(
        self, project_dir: Path, monkeypatch
    ):
        """
        E2E Test: `pdd generate` should fail when output path is empty string.

        Similar to the None case, but tests the empty string "" path.
        This can happen when generate_output_paths returns {} and
        output_file_paths.get("output", "") is used.
        """
        prompt_file = project_dir / "prompts" / "test_issue_154_empty.prompt"
        prompt_file.write_text(
            "% You are a Python engineer.\n"
            "% Write a hello world function.\n"
        )

        monkeypatch.chdir(project_dir)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-openai-key-for-testing")

        def mock_local_generator_func(*args, **kwargs):
            return ("def hello():\n    print('Hello')", 0.01, "mock-model")

        def mock_construct_paths(*args, **kwargs):
            """Mock with empty string output path."""
            return (
                {},
                {"prompt_file": "test content"},
                {"output": ""},  # Empty string - also triggers the bug
                "python"
            )

        with patch('pdd.code_generator_main.construct_paths', side_effect=mock_construct_paths):
            with patch('pdd.code_generator_main.local_code_generator_func', side_effect=mock_local_generator_func):
                from pdd import cli

                runner = CliRunner()
                result = runner.invoke(cli.cli, [
                    "--local",
                    "--force",
                    "generate",
                    str(prompt_file),
                ], catch_exceptions=False)

        # Exit code should indicate failure
        assert result.exit_code != 0, (
            f"BUG DETECTED (Issue #154): Command succeeded with empty output path!\n\n"
            f"Exit code: {result.exit_code}\n"
            f"Output:\n{result.output}"
        )

    def test_generate_succeeds_when_output_path_is_valid(
        self, project_dir: Path, monkeypatch
    ):
        """
        Control test: Verify generate works correctly when output path is valid.

        This ensures the fix doesn't break normal operation.
        """
        prompt_file = project_dir / "prompts" / "test_valid.prompt"
        prompt_file.write_text(
            "% You are a Python engineer.\n"
            "% Write a simple function.\n"
        )

        output_file = project_dir / "src" / "test_valid.py"

        monkeypatch.chdir(project_dir)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-openai-key-for-testing")

        def mock_local_generator_func(*args, **kwargs):
            return ("def simple():\n    return True", 0.01, "mock-model")

        def mock_construct_paths(*args, **kwargs):
            """Mock with valid output path."""
            return (
                {},
                {"prompt_file": "test content"},
                {"output": str(output_file)},  # Valid path - should work
                "python"
            )

        with patch('pdd.code_generator_main.construct_paths', side_effect=mock_construct_paths):
            with patch('pdd.code_generator_main.local_code_generator_func', side_effect=mock_local_generator_func):
                from pdd import cli

                runner = CliRunner()
                result = runner.invoke(cli.cli, [
                    "--local",
                    "--force",
                    "generate",
                    str(prompt_file),
                ], catch_exceptions=False)

        # With valid output path, command should succeed
        assert result.exit_code == 0, (
            f"Generate should succeed with valid output path.\n"
            f"Exit code: {result.exit_code}\n"
            f"Output:\n{result.output}"
        )

        # File should be created
        assert output_file.exists(), (
            f"Output file should be created when path is valid.\n"
            f"Expected: {output_file}"
        )


class TestIssue154OverwriteConfirmationE2E:
    """
    E2E tests verifying that overwrite confirmation is NOT shown when
    the file write will be skipped anyway.

    This tests the architectural issue: overwrite confirmation happens in
    construct_paths, but the actual write happens later with additional
    conditional gates. If the write will be skipped, confirmation is misleading.
    """

    @pytest.fixture
    def project_dir(self, tmp_path: Path) -> Path:
        """Create a minimal PDD project structure."""
        (tmp_path / "prompts").mkdir()
        (tmp_path / "src").mkdir()
        return tmp_path

    def test_no_overwrite_prompt_when_output_path_invalid(
        self, project_dir: Path, monkeypatch
    ):
        """
        E2E Test: User should NOT be asked to confirm overwrite when the
        write will be skipped anyway due to invalid output path.

        This tests the architectural disconnect between confirmation and write.

        Bug behavior:
        - User confirms overwrite (or uses --force)
        - LLM generates code (costs money)
        - Write is silently skipped due to invalid output path
        - User was misled into thinking their file would be overwritten

        Expected fix:
        - Validate output path BEFORE showing overwrite confirmation
        - Or raise error immediately when output path is invalid
        """
        # Create an existing file that would normally trigger overwrite prompt
        existing_file = project_dir / "src" / "existing.py"
        existing_file.parent.mkdir(parents=True, exist_ok=True)
        existing_file.write_text("# This file already exists\n")
        original_content = existing_file.read_text()

        prompt_file = project_dir / "prompts" / "test_overwrite.prompt"
        prompt_file.write_text(
            "% You are a Python engineer.\n"
            "% Write a new implementation.\n"
        )

        monkeypatch.chdir(project_dir)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-openai-key-for-testing")

        overwrite_confirmed = False

        def mock_construct_paths(*args, **kwargs):
            """
            Mock construct_paths to:
            1. Simulate that overwrite confirmation was shown/passed
            2. Return invalid output path (simulating downstream bug)
            """
            nonlocal overwrite_confirmed
            # In the real code, construct_paths handles overwrite confirmation
            # We simulate that it passed (user said yes or --force was used)
            overwrite_confirmed = True
            return (
                {},
                {"prompt_file": "test content"},
                {"output": None},  # But output path is invalid!
                "python"
            )

        def mock_local_generator_func(*args, **kwargs):
            return ("def new_impl():\n    return 'new'", 0.01, "mock-model")

        with patch('pdd.code_generator_main.construct_paths', side_effect=mock_construct_paths):
            with patch('pdd.code_generator_main.local_code_generator_func', side_effect=mock_local_generator_func):
                from pdd import cli

                runner = CliRunner()
                result = runner.invoke(cli.cli, [
                    "--local",
                    "--force",  # Simulates user confirming overwrite
                    "generate",
                    str(prompt_file),
                ], catch_exceptions=False)

        # The existing file should NOT have been modified
        # (since write was skipped due to invalid output path)
        assert existing_file.read_text() == original_content, (
            "Existing file should not be modified when output path is invalid"
        )

        # But the command should have failed, not silently succeeded
        assert result.exit_code != 0, (
            f"BUG DETECTED (Issue #154): Command succeeded despite invalid output path!\n\n"
            f"The user was asked to confirm overwrite (or used --force),\n"
            f"but the file was never actually written.\n"
            f"This is misleading - if write will be skipped, don't ask for confirmation.\n\n"
            f"Exit code: {result.exit_code}\n"
            f"Output:\n{result.output}"
        )
