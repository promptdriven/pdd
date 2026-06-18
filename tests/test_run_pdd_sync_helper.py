"""
Tests for the _run_pdd_sync helper in tests/test_one_session_eval.py.

Issue #1648: _run_pdd_sync() calls shutil.which("pdd") to locate the executable,
which may resolve to the installed site-packages binary (/opt/anaconda3/bin/pdd,
version 0.0.276) while the checkout is 0.0.278.dev0, causing eval tests to
silently exercise the wrong version.

The fix: use [sys.executable, "-m", "pdd"] so eval tests always use the same
interpreter as the test runner.

Note: This test is in a separate file (not appended to test_one_session_eval.py)
because that file has an autouse fixture that skips all tests unless
PDD_RUN_AGENTIC_TESTS=1 is set, which would prevent the test from running.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

# Ensure the tests/ directory is on sys.path so we can import from sibling modules.
_TESTS_DIR = Path(__file__).parent
if str(_TESTS_DIR) not in sys.path:
    sys.path.insert(0, str(_TESTS_DIR))

# Import the helper under test from the eval module.
# Note: importing from test_one_session_eval does NOT trigger its autouse skip
# fixture in this module's tests.
from test_one_session_eval import _run_pdd_sync


# ---------------------------------------------------------------------------
# Issue #1648: _run_pdd_sync must use sys.executable -m pdd, not PATH pdd
# ---------------------------------------------------------------------------

def test_run_pdd_sync_uses_sys_executable_not_path_binary(tmp_path):
    """Test 5: _run_pdd_sync uses sys.executable -m pdd, not shutil.which("pdd").

    Before fix: _run_pdd_sync calls shutil.which("pdd") to find the executable,
    which may resolve to the installed site-packages binary (e.g., 0.0.276 at
    /opt/anaconda3/bin/pdd) while the checkout is 0.0.278.dev0, causing eval
    tests to silently exercise the wrong version.

    After fix: _run_pdd_sync uses [sys.executable, "-m", "pdd"] so eval tests
    always exercise the same interpreter as the test runner.

    Fails on buggy code: subprocess.run is called with /opt/anaconda3/bin/pdd
    as the first command element instead of sys.executable.
    """
    captured_cmd: list = []

    def _fake_run(cmd, **kwargs):
        captured_cmd.extend(cmd)
        proc = MagicMock()
        proc.returncode = 0
        proc.stdout = "Overall status: Success\n"
        proc.stderr = ""
        return proc

    # Patch subprocess.run on the module object so _run_pdd_sync's call is captured.
    # Patch shutil.which to return a site-packages path so buggy code does NOT
    # reach pytest.skip() (which only fires when shutil.which returns None).
    with patch.object(subprocess, "run", side_effect=_fake_run):
        with patch("shutil.which", return_value="/opt/anaconda3/bin/pdd"):
            _run_pdd_sync(tmp_path, "mymodule", timeout=5)

    assert len(captured_cmd) > 0, (
        "subprocess.run was never called — _run_pdd_sync skipped or raised unexpectedly"
    )
    assert captured_cmd[0] == sys.executable, (
        f"Expected sys.executable ({sys.executable!r}) as first command element, "
        f"got {captured_cmd[0]!r}. "
        "Bug: _run_pdd_sync is using the PATH-resolved binary instead of the current interpreter."
    )
    assert "-m" in captured_cmd, f"Expected '-m' in command, got: {captured_cmd}"
    assert "pdd" in captured_cmd, f"Expected 'pdd' in command, got: {captured_cmd}"
    assert "/opt/anaconda3/bin/pdd" not in captured_cmd, (
        f"PATH binary must not appear in command: {captured_cmd}"
    )
