"""
E2E tests for subprocess interpreter parity in pdd sync runner (Issue #1648).

Unlike the unit tests in tests/test_agentic_sync_runner.py that mock shutil.which,
these tests manipulate the real OS PATH environment variable, reproducing the exact
developer scenario from issue #1648: having a globally-installed pdd binary
(e.g., 0.0.276 from conda) on PATH while a source checkout (0.0.278.dev0) is
the parent process.

The tests exercise the full executable-resolution code path without mocking
shutil.which, confirming that the real PATH lookup does NOT influence the
subprocess command when the fix is in place.

Test behaviour:
  - FAIL on current buggy code (_find_pdd_executable returns the PATH binary)
  - PASS once the bug is fixed (always returns None / uses sys.executable -m pdd)

Issue: https://github.com/promptdriven/pdd/issues/1648
"""

from __future__ import annotations

import json
import os
import shutil
import stat
import subprocess
import sys
from pathlib import Path

import pytest

from pdd.agentic_sync_runner import AsyncSyncRunner, _find_pdd_executable


def get_project_root() -> Path:
    """Return the repo root (parent of the tests/ directory)."""
    current = Path(__file__).parent
    while current != current.parent:
        if (current / "pdd").is_dir() and (current / "pyproject.toml").exists():
            return current
        current = current.parent
    raise RuntimeError("Could not find project root with pdd/ directory")


def _make_fake_pdd_bin(tmp_path: Path) -> tuple[Path, Path]:
    """Create a fake pdd shell script that simulates an older installed binary.

    If this fake binary is ever invoked it writes to *marker_file* and exits
    with code 2, letting tests detect unintended invocations.

    Returns (bin_dir, marker_file).
    """
    bin_dir = tmp_path / "fake_installed_pdd" / "bin"
    bin_dir.mkdir(parents=True)
    marker_file = tmp_path / "fake_pdd_was_invoked"

    fake_pdd = bin_dir / "pdd"
    fake_pdd.write_text(
        "#!/bin/sh\n"
        "# Simulates an older installed pdd binary (e.g., 0.0.276 from conda/pip)\n"
        "# that must NOT be used when a source checkout is the parent process.\n"
        f"touch '{marker_file}'\n"
        "echo 'ERROR: sync runner invoked the installed PATH binary (issue #1648)' >&2\n"
        "exit 2\n"
    )
    fake_pdd.chmod(fake_pdd.stat().st_mode | stat.S_IEXEC | stat.S_IXGRP | stat.S_IXOTH)

    return bin_dir, marker_file


# ---------------------------------------------------------------------------
# E2E: real PATH manipulation — no shutil.which mock
# ---------------------------------------------------------------------------


class TestSyncRunnerInterpreterParityE2E:
    """E2E tests: pdd sync runner uses sys.executable -m pdd, ignoring any PATH binary.

    All tests in this class use real OS PATH manipulation rather than mocking
    shutil.which, reproducing the developer scenario from issue #1648.
    """

    def test_find_pdd_executable_ignores_real_path_binary(
        self, tmp_path: Path, monkeypatch
    ) -> None:
        """_find_pdd_executable() must return None even when PATH has a pdd binary.

        Simulates the issue #1648 scenario: a fake 'pdd' binary (representing an
        older installed version, e.g. 0.0.276) is prepended to PATH so that
        shutil.which("pdd") finds it.  _find_pdd_executable() must still return
        None so that callers build their subprocess command as
        [sys.executable, '-m', 'pdd', ...].

        Fails on buggy code: _find_pdd_executable() returns the fake PATH binary path.
        Passes on fixed code: _find_pdd_executable() returns None.
        """
        bin_dir, marker_file = _make_fake_pdd_bin(tmp_path)

        # Prepend fake bin dir to PATH so shutil.which("pdd") finds it first.
        # This is a real OS-level change, not a shutil.which mock.
        monkeypatch.setenv("PATH", f"{bin_dir}:{os.environ.get('PATH', '')}")

        # Sanity check: shutil.which must find the fake binary (test setup guard).
        resolved = shutil.which("pdd")
        assert resolved is not None and str(bin_dir) in resolved, (
            f"Test setup error: shutil.which('pdd') = {resolved!r}; "
            f"expected fake binary from {bin_dir} to be first on PATH.\n"
            f"Current PATH: {os.environ.get('PATH', '')[:200]}"
        )

        # --- exercise the real function, no mock ---
        result = _find_pdd_executable()

        assert result is None, (
            f"_find_pdd_executable() returned {result!r} but must return None.\n"
            f"Bug (issue #1648): the function resolved the PATH binary "
            f"({resolved!r}) instead of returning None so callers use "
            f"[sys.executable, '-m', 'pdd'] for interpreter parity.\n"
            f"sys.executable = {sys.executable!r}"
        )

        # The fake binary must not have been executed
        assert not marker_file.exists(), (
            "The fake PATH binary was invoked during _find_pdd_executable() — "
            "the function must only locate executables, not invoke them."
        )

    def test_build_command_uses_sys_executable_with_fake_path_pdd(
        self, tmp_path: Path, monkeypatch
    ) -> None:
        """_build_command() must produce [sys.executable, -m, pdd, ...] ignoring PATH.

        Integration-level companion to TestBuildCommandInterpreterParity in
        test_agentic_sync_runner.py.  Uses real PATH manipulation (no shutil.which
        mock) to verify the full command-building path end-to-end.

        Fails on buggy code: cmd[0] is the fake PATH binary.
        Passes on fixed code: cmd[0] is sys.executable.
        """
        bin_dir, marker_file = _make_fake_pdd_bin(tmp_path)

        monkeypatch.setenv("PATH", f"{bin_dir}:{os.environ.get('PATH', '')}")

        # Verify fake binary is first on PATH
        resolved = shutil.which("pdd")
        assert resolved is not None and str(bin_dir) in resolved, (
            f"Test setup error: expected fake binary from {bin_dir} first on PATH, "
            f"got {resolved!r}"
        )

        runner = AsyncSyncRunner(
            basenames=["mymodule"],
            dep_graph={"mymodule": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        cmd = runner._build_command("mymodule")

        assert cmd[0] == sys.executable, (
            f"E2E failure (issue #1648):\n"
            f"  Expected cmd[0] = sys.executable = {sys.executable!r}\n"
            f"  Got cmd[0] = {cmd[0]!r}\n"
            f"  Full command: {cmd}\n"
            f"  shutil.which('pdd') = {resolved!r} (fake PATH binary)\n"
            f"  Bug: _find_pdd_executable() returned the installed PATH binary so\n"
            f"  subprocess sync would execute an older pdd instead of the checkout."
        )
        assert "-m" in cmd, f"Expected '-m' flag in command, got: {cmd}"
        assert "pdd" in cmd, f"Expected 'pdd' module name in command, got: {cmd}"
        assert str(bin_dir) not in " ".join(cmd), (
            f"Fake PATH binary directory must not appear in subprocess command: {cmd}"
        )
        assert "sync" in cmd, (
            f"Regression: 'sync' subcommand must still be present in: {cmd}"
        )

        # Building the command must not execute the fake binary
        assert not marker_file.exists(), (
            "Fake PATH binary was invoked by _build_command() — "
            "_build_command() must construct a command list, not execute it."
        )

    def test_build_command_uses_sys_executable_with_real_env_pdd(self) -> None:
        """_build_command() uses sys.executable -m pdd even with a real pdd on PATH.

        Exercises the real runtime environment with no PATH manipulation.
        In this environment shutil.which("pdd") returns a real binary
        (e.g., /opt/venv/bin/pdd); the sync runner must still produce a command
        starting with sys.executable rather than that binary.

        This is the simplest possible E2E test: no PATH manipulation, no mocks,
        just the real code in the real environment.

        Fails on buggy code: cmd[0] is the resolved PATH binary.
        Passes on fixed code: cmd[0] is sys.executable.
        """
        # Document the real environment for diagnostics
        real_pdd_on_path = shutil.which("pdd")

        runner = AsyncSyncRunner(
            basenames=["mymodule"],
            dep_graph={"mymodule": []},
            sync_options={},
            github_info=None,
            quiet=True,
        )
        cmd = runner._build_command("mymodule")

        assert cmd[0] == sys.executable, (
            f"E2E failure (issue #1648) in real environment:\n"
            f"  Expected cmd[0] = sys.executable = {sys.executable!r}\n"
            f"  Got cmd[0] = {cmd[0]!r}\n"
            f"  Full command: {cmd}\n"
            f"  shutil.which('pdd') = {real_pdd_on_path!r} (real PATH binary)\n"
            f"  Bug: _find_pdd_executable() returned the installed PATH binary so\n"
            f"  subprocess sync would execute a potentially different pdd version."
        )
        assert "-m" in cmd, f"Expected '-m' flag in command, got: {cmd}"
        assert "pdd" in cmd, f"Expected 'pdd' module name in command, got: {cmd}"


# ---------------------------------------------------------------------------
# E2E subprocess: run resolution in a child process (maximum isolation)
# ---------------------------------------------------------------------------


def test_find_pdd_executable_returns_none_in_subprocess(tmp_path: Path) -> None:
    """Subprocess-level E2E: _find_pdd_executable() returns None with a PATH binary.

    Runs _find_pdd_executable() in a completely isolated child Python process
    (using subprocess.run) with a fake pdd binary prepended to PATH.  The child
    process prints the return value as JSON; the parent asserts it is null (None).

    This is the highest-isolation E2E test: the resolution logic runs in a fresh
    interpreter with no shared in-process state.

    Fails on buggy code: child process prints the fake binary path (not null).
    Passes on fixed code: child process prints null.
    """
    bin_dir, marker_file = _make_fake_pdd_bin(tmp_path)

    env = os.environ.copy()
    env["PATH"] = f"{bin_dir}:{env.get('PATH', '')}"
    # Ensure the project root is importable in the child process
    project_root = get_project_root()
    existing_pp = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = f"{project_root}:{existing_pp}" if existing_pp else str(project_root)

    child_script = (
        "from pdd.agentic_sync_runner import _find_pdd_executable; "
        "import json; "
        "print(json.dumps(_find_pdd_executable()))"
    )

    result = subprocess.run(
        [sys.executable, "-c", child_script],
        capture_output=True,
        text=True,
        env=env,
        cwd=str(project_root),
        timeout=30,
    )

    assert result.returncode == 0, (
        f"Child process exited with code {result.returncode}.\n"
        f"stdout: {result.stdout!r}\n"
        f"stderr: {result.stderr!r}"
    )

    value = json.loads(result.stdout.strip())

    assert value is None, (
        f"Subprocess E2E failure (issue #1648):\n"
        f"  _find_pdd_executable() returned {value!r} in child process, expected None.\n"
        f"  Child PATH had fake pdd at: {bin_dir}/pdd\n"
        f"  Bug: the function resolved the PATH binary instead of returning None\n"
        f"  so callers use [sys.executable, '-m', 'pdd'] for interpreter parity."
    )

    # The fake binary script must not have been executed
    assert not marker_file.exists(), (
        "The fake PATH binary was invoked during the subprocess E2E test — "
        "_find_pdd_executable() must not execute binaries, only locate them."
    )
