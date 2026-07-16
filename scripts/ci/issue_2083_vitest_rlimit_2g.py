"""Closed control plugin for the issue-2083 RLIMIT_AS diagnostic."""
# pylint: disable=protected-access,duplicate-code

from __future__ import annotations

from dataclasses import asdict, replace

from pdd.sync_core import runner
from pdd.sync_core.supervisor import SupervisorLimits


_EXPECTED = SupervisorLimits(
    max_output_bytes=16 * 1024 * 1024,
    max_writable_bytes=512 * 1024 * 1024,
    max_memory_bytes=4 * 1024 * 1024 * 1024,
    max_virtual_memory_bytes=2 * 1024 * 1024 * 1024,
    max_cpu_seconds=300,
    max_processes=128,
)


def pytest_configure() -> None:
    """Assert the complete production policy, then retain its 2 GiB RLIMIT_AS."""
    current = runner._VITEST_SUPERVISOR_LIMITS
    if asdict(current) != asdict(_EXPECTED):
        raise RuntimeError("production Vitest limits changed")
    runner._VITEST_SUPERVISOR_LIMITS = replace(
        current,
        max_virtual_memory_bytes=2 * 1024 * 1024 * 1024,
    )
