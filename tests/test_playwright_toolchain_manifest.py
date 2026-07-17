"""Behavioral contracts for the hosted Playwright toolchain manifest producer."""

from __future__ import annotations

import subprocess
from pathlib import Path

import pytest

from pdd.sync_core.playwright_toolchain import native_runtime_paths


def test_native_runtime_paths_canonicalizes_ldd_symlink_targets(tmp_path: Path) -> None:
    """Every manifest member is the canonical final library path."""
    executable = tmp_path / "browser"
    executable.write_bytes(b"browser")
    target = tmp_path / "libreal.dylib"
    target.write_bytes(b"library")
    alias = tmp_path / "libalias.dylib"
    alias.symlink_to(target)

    def ldd(command, **_kwargs):
        return subprocess.CompletedProcess(command, 0, f"lib => {alias}\n", "")

    assert native_runtime_paths((executable,), ldd=ldd) == (target.resolve(),)


def test_native_runtime_paths_fails_closed_on_unresolvable_ldd_path(tmp_path: Path) -> None:
    """A loader path that cannot be canonicalized cannot enter the manifest."""
    executable = tmp_path / "browser"
    executable.write_bytes(b"browser")

    def ldd(command, **_kwargs):
        return subprocess.CompletedProcess(command, 0, "lib => /missing/lib.so\n", "")

    with pytest.raises(FileNotFoundError):
        native_runtime_paths((executable,), ldd=ldd)
