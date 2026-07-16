"""Synchronize one homogeneous issue-2083 diagnostic wave."""

from __future__ import annotations

import importlib
import os
import time
from pathlib import Path


_WAIT_SECONDS = 30.0


def _wait_for_wave() -> None:
    directory_value = os.environ.get("PDD_2083_BARRIER_DIRECTORY")
    parties_value = os.environ.get("PDD_2083_BARRIER_PARTIES")
    token = os.environ.get("PDD_2083_BARRIER_TOKEN")
    if not directory_value or not parties_value or not token:
        raise RuntimeError("issue-2083 barrier configuration is incomplete")
    directory = Path(directory_value)
    parties = int(parties_value)
    if parties not in {2, 4} or not token.isascii() or not token.isalnum():
        raise RuntimeError("issue-2083 barrier configuration is invalid")
    directory.mkdir(mode=0o700, parents=True, exist_ok=True)
    (directory / f"{token}.ready").write_text("ready\n", encoding="ascii")
    deadline = time.monotonic() + _WAIT_SECONDS
    release = directory / "release"
    while time.monotonic() < deadline:
        if len(tuple(directory.glob("*.ready"))) == parties:
            release.touch(exist_ok=True)
        if release.is_file():
            return
        time.sleep(0.01)
    raise RuntimeError("issue-2083 barrier expired")


def pytest_configure() -> None:
    """Wrap exactly the protected Vitest adapter call with the wave barrier."""
    runner_module = importlib.import_module("pdd.sync_core.runner")
    original = getattr(runner_module, "_run_vitest")
    waited = False

    def synchronized(*args, **kwargs):
        nonlocal waited
        if not waited:
            _wait_for_wave()
            waited = True
        return original(*args, **kwargs)

    setattr(runner_module, "_run_vitest", synchronized)
