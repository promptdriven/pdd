"""
E2E Test for Issue #25: INFO logs and warnings appear when running pdd --version.

This test verifies that simple informational commands like `--version` and `--help`
do not trigger LLM infrastructure initialization (logging setup, cache configuration).

The Bug:
- Running `pdd --version` from outside a project directory shows:
  - UserWarning about project root (v0.0.49, now removed)
  - INFO logs about LLM model CSV and LiteLLM disk cache (still present)
- This happens because `pdd/cli.py` eagerly imports modules for backward compatibility
- The import chain triggers `pdd/llm_invoke.py` module-level execution

E2E Test Strategy:
- Use subprocess to run `pdd --version` and `pdd --help` in a fresh process
- Subprocess isolation is required because the bug is module-level side effects
- Run from a non-project directory (e.g., tmp_path) to maximize side effects
- Verify stdout/stderr contain ONLY the expected output, no INFO logs or warnings

The test should:
- FAIL on the current buggy code (INFO logs detected)
- PASS once the bug is fixed (clean output)
"""

import os
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest


def get_project_root() -> Path:
    """Get the project root directory."""
    current = Path(__file__).parent
    while current != current.parent:
        if (current / "pdd").is_dir() and (current / "pyproject.toml").is_file():
            return current
        current = current.parent
    raise RuntimeError("Could not find project root with pdd/ directory")


class TestVersionSideEffectsE2E:
    """E2E tests verifying that --version and --help do not trigger side effects."""

    def test_version_output_has_no_side_effects(self, tmp_path: Path):
        """
        E2E Test: `pdd --version` should ONLY output the version string, nothing else.

        This is the primary test for Issue #25.

        Expected behavior (after fix):
        - stdout contains only: "pdd, version X.Y.Z"
        - stderr is empty
        - No INFO logs about LLM model CSV or LiteLLM cache

        Bug behavior (Issue #25):
        - INFO logs appear before/after version output
        - UserWarning may appear (in older versions)

        We run from tmp_path (a non-project directory) to ensure we're not
        inside a PDD project, which is when the bug is most apparent.
        """
        project_root = get_project_root()

        # Run pdd --version via subprocess from a non-project directory
        # Use python -m pdd.cli to ensure we use the local development version
        result = subprocess.run(
            [sys.executable, "-m", "pdd.cli", "--version"],
            capture_output=True,
            text=True,
            cwd=str(tmp_path),  # Run from non-project directory
            env={
                **os.environ,
                "PYTHONPATH": str(project_root),
                # Clear PDD_PATH to ensure we're not inside a project
                "PDD_PATH": "",
            },
            timeout=30
        )

        # Combine stdout and stderr for checking
        all_output = result.stdout + result.stderr

        # The bug check: Look for INFO log patterns that indicate llm_invoke was loaded
        side_effect_patterns = [
            "INFO",
            "WARNING",
            "UserWarning",
            "LiteLLM",
            "litellm_cache",
            "LLM model CSV",
            "Could not determine project root",
            "pdd.llm_invoke",
            "disk cache configured",
        ]

        found_side_effects = []
        for pattern in side_effect_patterns:
            if pattern in all_output:
                found_side_effects.append(pattern)

        if found_side_effects:
            pytest.fail(
                f"BUG DETECTED (Issue #25): `pdd --version` has side effects!\n\n"
                f"Found unexpected patterns in output: {found_side_effects}\n\n"
                f"Full stdout:\n{result.stdout}\n\n"
                f"Full stderr:\n{result.stderr}\n\n"
                f"Expected: Only 'pdd, version X.Y.Z' with no logging output.\n\n"
                f"Root cause: cli.py eagerly imports modules that trigger llm_invoke.py\n"
                f"module-level initialization (logging setup, cache configuration)."
            )

        # Verify version string is present
        assert "pdd, version" in result.stdout or "pdd, version" in all_output, \
            f"Expected version string in output. Got stdout: {result.stdout}"

        # Verify exit code is 0
        assert result.returncode == 0, \
            f"Expected exit code 0, got {result.returncode}"

    def test_help_output_has_no_side_effects(self, tmp_path: Path):
        """
        E2E Test: `pdd --help` should not trigger LLM infrastructure initialization.

        Same as test_version_output_has_no_side_effects but for --help.
        """
        project_root = get_project_root()

        result = subprocess.run(
            [sys.executable, "-m", "pdd.cli", "--help"],
            capture_output=True,
            text=True,
            cwd=str(tmp_path),
            env={
                **os.environ,
                "PYTHONPATH": str(project_root),
                "PDD_PATH": "",
            },
            timeout=30
        )

        all_output = result.stdout + result.stderr

        side_effect_patterns = [
            "INFO",
            "WARNING",
            "UserWarning",
            "LiteLLM",
            "litellm_cache",
            "LLM model CSV",
            "pdd.llm_invoke",
            "disk cache configured",
        ]

        found_side_effects = []
        for pattern in side_effect_patterns:
            if pattern in all_output:
                found_side_effects.append(pattern)

        if found_side_effects:
            pytest.fail(
                f"BUG DETECTED (Issue #25): `pdd --help` has side effects!\n\n"
                f"Found unexpected patterns in output: {found_side_effects}\n\n"
                f"Full stdout:\n{result.stdout}\n\n"
                f"Full stderr:\n{result.stderr}\n\n"
                f"Expected: Only help text with no logging output."
            )

        # Verify help output is present
        assert "Usage:" in result.stdout or "Usage:" in all_output, \
            f"Expected 'Usage:' in help output. Got: {result.stdout}"

        assert result.returncode == 0

    def test_version_output_clean_inside_project_directory(self):
        """
        E2E Test: `pdd --version` should be clean even inside a project directory.

        This verifies the fix works regardless of whether we're inside a PDD project.
        """
        project_root = get_project_root()

        # Run from project root (which has .pdd, .pddrc, etc.)
        result = subprocess.run(
            [sys.executable, "-m", "pdd.cli", "--version"],
            capture_output=True,
            text=True,
            cwd=str(project_root),  # Run from project directory
            env={**os.environ, "PYTHONPATH": str(project_root)},
            timeout=30
        )

        all_output = result.stdout + result.stderr

        side_effect_patterns = [
            "INFO",
            "WARNING",
            "UserWarning",
            "LiteLLM",
            "litellm_cache",
            "LLM model CSV",
            "pdd.llm_invoke",
        ]

        found_side_effects = []
        for pattern in side_effect_patterns:
            if pattern in all_output:
                found_side_effects.append(pattern)

        if found_side_effects:
            pytest.fail(
                f"BUG DETECTED (Issue #25): `pdd --version` has side effects even inside project!\n\n"
                f"Found patterns: {found_side_effects}\n\n"
                f"stdout:\n{result.stdout}\n\nstderr:\n{result.stderr}"
            )

        assert "pdd, version" in result.stdout or "pdd, version" in all_output
        assert result.returncode == 0

    def test_cli_import_chain_for_version_does_not_trigger_llm_invoke(self, tmp_path: Path):
        """
        E2E Test: Importing pdd.core.cli should NOT trigger llm_invoke side effects.

        This test confirms that the minimal import path for --version
        (pdd.core.cli) does not cause the problematic imports.

        The bug is in pdd/cli.py which imports pdd.core.cli but also
        imports other modules for backward compatibility that trigger llm_invoke.
        """
        project_root = get_project_root()

        # Test script that imports pdd.core.cli and checks for llm_invoke
        test_script = '''
import sys

# Before import: check what pdd modules are loaded
pdd_modules_before = set(k for k in sys.modules.keys() if k.startswith("pdd"))

# Import only the core CLI module (the minimal path for --version)
import pdd.core.cli

# After import: check what pdd modules are now loaded
pdd_modules_after = set(k for k in sys.modules.keys() if k.startswith("pdd"))

# Check if llm_invoke was loaded (this is the problematic module)
llm_invoke_loaded = "pdd.llm_invoke" in pdd_modules_after

# Print result as simple text for parsing
if llm_invoke_loaded:
    print("POLLUTION_DETECTED: pdd.llm_invoke was loaded by importing pdd.core.cli")
    print(f"Loaded modules: {sorted(pdd_modules_after - pdd_modules_before)}")
else:
    print("CLEAN: pdd.llm_invoke was NOT loaded")
'''

        script_file = tmp_path / "check_import.py"
        script_file.write_text(test_script)

        result = subprocess.run(
            [sys.executable, str(script_file)],
            capture_output=True,
            text=True,
            cwd=str(tmp_path),
            env={**os.environ, "PYTHONPATH": str(project_root)},
            timeout=30
        )

        all_output = result.stdout + result.stderr

        # This test verifies the core.cli import is clean
        # If it fails, it means even the core module triggers llm_invoke
        if "POLLUTION_DETECTED" in all_output:
            pytest.fail(
                f"Importing pdd.core.cli triggers llm_invoke!\n\n"
                f"Output:\n{all_output}\n\n"
                f"This means even the minimal import path has side effects."
            )

    def test_version_command_performance(self, tmp_path: Path):
        """
        E2E Test (Optional): `pdd --version` should complete quickly.

        A command that only prints the version should not need to load
        heavy LLM infrastructure. This is a performance regression indicator.

        Note: This test is lenient (< 2 seconds) to avoid flakiness, but
        the real goal is << 1 second for a simple version command.
        """
        import time

        project_root = get_project_root()

        start_time = time.time()
        result = subprocess.run(
            [sys.executable, "-m", "pdd.cli", "--version"],
            capture_output=True,
            text=True,
            cwd=str(tmp_path),
            env={
                **os.environ,
                "PYTHONPATH": str(project_root),
                "PDD_PATH": "",
            },
            timeout=30
        )
        elapsed = time.time() - start_time

        # Version command should be fast (< 2 seconds as lenient threshold)
        # After fix, it should be much faster (< 0.5 seconds ideally)
        assert elapsed < 2.0, \
            f"`pdd --version` took {elapsed:.2f}s, expected < 2.0s. " \
            f"This may indicate unnecessary module loading."

        assert result.returncode == 0
