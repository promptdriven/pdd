"""
E2E Test (Subprocess-based) for Issue #505: CLI help text shows wrong
DEFAULT_STRENGTH (0.75 vs actual 1.0).

This is a true E2E test that uses subprocess to invoke the actual CLI binary,
exercising the full code path that a user would take.

Bug: When running ``pdd --help``, the ``--strength`` option displays
"Default: 0.75 or .pddrc value" but the actual default used at runtime
(``pdd.DEFAULT_STRENGTH``) is ``1.0``.  Users who rely on the help text
believe they are using a mid-tier model (0.75) but are actually charged
for the most powerful model (1.0).

E2E Test Strategy:
- Use subprocess to run ``python -m pdd.cli --help`` (like a real user)
- Parse the ``--strength`` help text from stdout
- Assert the documented default matches the canonical constant in
  ``pdd/__init__.py``
- Also run ``python -c "from pdd import DEFAULT_STRENGTH; print(DEFAULT_STRENGTH)"``
  to read the canonical value dynamically — no hardcoded expected value

The test should:
- FAIL on the current buggy code (help says 0.75, canonical says 1.0)
- PASS once the bug is fixed (help says 1.0, matching canonical)

Issue: https://github.com/promptdriven/pdd/issues/505
"""

import os
import re
import subprocess
import sys
from pathlib import Path

import pytest


def get_project_root() -> Path:
    """Get the project root directory."""
    current = Path(__file__).parent
    while current != current.parent:
        if (current / "pdd").is_dir() and (current / "pyproject.toml").exists():
            return current
        current = current.parent
    raise RuntimeError("Could not find project root with pdd/ directory")


@pytest.mark.e2e
class TestIssue505E2ESubprocess:
    """
    E2E tests using subprocess to verify the --strength default in CLI help.

    These tests exercise the full CLI path that users take when running
    ``pdd --help`` to check available options and their defaults.
    """

    def _run_pdd_help(self, timeout: int = 30) -> str:
        """Run ``pdd --help`` via subprocess and return combined output."""
        project_root = get_project_root()
        env = os.environ.copy()
        env["PYTHONPATH"] = str(project_root)
        # Prevent auto-update checks from interfering
        env["PDD_AUTO_UPDATE"] = "false"

        result = subprocess.run(
            [sys.executable, "-m", "pdd.cli", "--help"],
            capture_output=True,
            text=True,
            cwd=str(project_root),
            env=env,
            timeout=timeout,
        )
        return result.stdout + result.stderr

    def _get_canonical_default_strength(self, timeout: int = 10) -> str:
        """Read DEFAULT_STRENGTH from ``pdd/__init__.py`` via subprocess."""
        project_root = get_project_root()
        env = os.environ.copy()
        env["PYTHONPATH"] = str(project_root)

        result = subprocess.run(
            [
                sys.executable, "-c",
                "from pdd import DEFAULT_STRENGTH; print(DEFAULT_STRENGTH)",
            ],
            capture_output=True,
            text=True,
            cwd=str(project_root),
            env=env,
            timeout=timeout,
        )
        assert result.returncode == 0, (
            f"Failed to read DEFAULT_STRENGTH: {result.stderr}"
        )
        return result.stdout.strip()

    # ------------------------------------------------------------------
    # Test 1: The core user-facing bug
    # ------------------------------------------------------------------
    def test_pdd_help_strength_default_matches_canonical(self):
        """
        E2E: ``pdd --help`` must show the correct DEFAULT_STRENGTH value.

        User scenario:
        1. User runs ``pdd --help`` to see available options
        2. User reads the --strength option and its documented default
        3. User trusts the help text and does NOT explicitly set --strength

        Expected: Help text says "Default: 1.0" (the canonical value)
        Actual (bug): Help text says "Default: 0.75" (stale value)

        This test FAILS on buggy code, PASSES after fix.
        """
        canonical = self._get_canonical_default_strength()
        help_output = self._run_pdd_help()

        # Extract the strength help line
        # The help text contains something like:
        #   --strength ... Default: 0.75 or .pddrc value.
        expected_fragment = f"Default: {canonical}"
        assert expected_fragment in help_output, (
            f"BUG DETECTED (Issue #505): CLI --help does not show the correct "
            f"DEFAULT_STRENGTH.\n"
            f"  Expected to find: '{expected_fragment}'\n"
            f"  Canonical DEFAULT_STRENGTH: {canonical}\n\n"
            f"Users see incorrect default and may incur unexpected API costs.\n\n"
            f"Full --help output:\n{help_output}"
        )

    # ------------------------------------------------------------------
    # Test 2: Stale value must NOT appear
    # ------------------------------------------------------------------
    def test_pdd_help_does_not_show_stale_075(self):
        """
        E2E: ``pdd --help`` must NOT claim the strength default is 0.75.

        This guards against the specific stale value reported in the issue.

        This test FAILS on buggy code, PASSES after fix.
        """
        help_output = self._run_pdd_help()

        assert "Default: 0.75" not in help_output, (
            f"BUG DETECTED (Issue #505): CLI --help still contains the stale "
            f"'Default: 0.75' for --strength.\n"
            f"The actual DEFAULT_STRENGTH is 1.0.\n\n"
            f"Full --help output:\n{help_output}"
        )

    # ------------------------------------------------------------------
    # Test 3: Full round-trip — help text ↔ runtime default
    # ------------------------------------------------------------------
    def test_help_default_matches_runtime_config_resolution(self):
        """
        E2E: The default shown in ``--help`` must match what the config
        resolution layer actually uses when no ``--strength`` is provided.

        This exercises two separate code paths end-to-end:
        1. CLI help text rendering (``pdd/core/cli.py``)
        2. Config resolution (``pdd/core/config_resolution.py`` →
           ``pdd.DEFAULT_STRENGTH``)

        If these disagree, users are misled about which model tier they use.

        This test FAILS on buggy code, PASSES after fix.
        """
        project_root = get_project_root()
        env = os.environ.copy()
        env["PYTHONPATH"] = str(project_root)
        # Ensure no .pddrc override so config_resolution falls back to
        # DEFAULT_STRENGTH
        env.pop("PDD_STRENGTH", None)
        env["PDD_AUTO_UPDATE"] = "false"

        # Step 1: Get the canonical DEFAULT_STRENGTH
        canonical = self._get_canonical_default_strength()

        # Step 2: Get what config_resolution actually resolves to
        result = subprocess.run(
            [
                sys.executable, "-c",
                (
                    "import sys, os; "
                    "os.environ.pop('PDD_STRENGTH', None); "
                    "from pdd.core.config_resolution import resolve_strength; "
                    "print(resolve_strength(None, None))"
                ),
            ],
            capture_output=True,
            text=True,
            cwd=str(project_root),
            env=env,
            timeout=10,
        )
        resolved_strength = result.stdout.strip()

        # Step 3: Get the help text
        help_output = self._run_pdd_help()

        # All three must agree
        expected_fragment = f"Default: {canonical}"
        assert expected_fragment in help_output, (
            f"BUG DETECTED (Issue #505): Help text default doesn't match "
            f"canonical DEFAULT_STRENGTH.\n"
            f"  Canonical: {canonical}\n"
            f"  Resolved at runtime: {resolved_strength}\n"
            f"  Help text does not contain '{expected_fragment}'\n\n"
            f"Full --help output:\n{help_output}"
        )

        assert canonical == resolved_strength, (
            f"DEFAULT_STRENGTH ({canonical}) != resolved strength "
            f"({resolved_strength}) — config_resolution disagrees with "
            f"pdd/__init__.py"
        )
