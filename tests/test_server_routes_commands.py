"""
Tests for pdd/server/routes/commands.py subprocess command building.

Issue #1648: _find_pdd_executable() in server/routes/commands.py prefers
shutil.which("pdd"), which resolves to the installed site-packages binary rather
than the current Python interpreter.  The fix is to always use
[sys.executable, "-m", "pdd"] for interpreter parity.
"""
from __future__ import annotations

import sys
from unittest.mock import patch

import pytest


# ---------------------------------------------------------------------------
# Issue #1648: _build_pdd_command_args must use sys.executable -m pdd
# ---------------------------------------------------------------------------

class TestBuildPddCommandArgsInterpreterParity:
    """Tests that server/routes/commands.py _build_pdd_command_args() uses the current interpreter.

    Issue #1648: _find_pdd_executable() in pdd/server/routes/commands.py uses
    shutil.which("pdd") first, causing subprocess commands to resolve to the
    installed binary instead of the checkout interpreter.
    """

    def test_build_pdd_command_args_ignores_path_pdd(self):
        """Test 3: _build_pdd_command_args uses sys.executable even when PATH has pdd.

        Simulates a developer machine where shutil.which("pdd") returns the
        installed site-packages binary /opt/anaconda3/bin/pdd (version 0.0.276)
        while the checkout is 0.0.278.dev0.

        Fails on buggy code: _find_pdd_executable() returns the PATH binary, so
        _build_pdd_command_args() produces ["/opt/anaconda3/bin/pdd", ...].
        """
        from pdd.server.routes.commands import _build_pdd_command_args

        with patch("shutil.which", return_value="/opt/anaconda3/bin/pdd"):
            cmd = _build_pdd_command_args("sync", {"basename": "mymodule"}, None)

        assert cmd[0] == sys.executable, (
            f"Expected sys.executable ({sys.executable!r}), got {cmd[0]!r}. "
            "Bug: _find_pdd_executable() in server/routes/commands.py returned the PATH binary."
        )
        assert "-m" in cmd, f"Expected '-m' in command, got: {cmd}"
        assert "pdd" in cmd, f"Expected 'pdd' module name in command, got: {cmd}"
        assert "/opt/anaconda3/bin/pdd" not in cmd, (
            f"PATH binary must not appear in command: {cmd}"
        )
        # The old -c fallback must also be gone after the fix
        assert not any("from pdd.cli import cli" in arg for arg in cmd), (
            f"Old -c import fallback must not appear in command after fix: {cmd}"
        )
        # The sync subcommand must still be present
        assert "sync" in cmd, f"Expected 'sync' subcommand in command, got: {cmd}"
        # The sync subcommand must appear after the interpreter prefix
        m_idx = cmd.index("-m")
        pdd_idx = cmd.index("pdd", m_idx + 1)
        sync_idx = cmd.index("sync")
        assert sync_idx > pdd_idx, (
            f"'sync' subcommand must appear after 'pdd' in: {cmd}"
        )
