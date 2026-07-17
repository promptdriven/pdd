"""Setuptools hook for the checker-owned, offline-built Node authority addon."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

from setuptools import setup
from setuptools.command.build_py import build_py as _build_py


class PddBuildPy(_build_py):
    """Compile the supported-platform addon before package data is copied."""

    def run(self) -> None:
        root = Path(__file__).resolve().parent
        subprocess.run(
            [sys.executable, str(root / "scripts/build_vitest_fd_cloexec_addon.py")],
            cwd=root,
            check=True,
        )
        super().run()


setup(cmdclass={"build_py": PddBuildPy})
