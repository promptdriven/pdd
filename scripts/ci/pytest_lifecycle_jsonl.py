"""Durable pytest lifecycle evidence for the temporary issue-1995 workflow.

An unmatched start record identifies only the last observed node and phase.  It
does not, by itself, identify the cause of a stalled or terminated process.
"""

from __future__ import annotations

import json
import os
import time
from pathlib import Path
from typing import Any, Generator

import pytest


def _emit(event: str, **fields: Any) -> None:
    """Append one complete record and durably flush it before returning."""
    destination = os.environ.get("PDD_PYTEST_LIFECYCLE_JSONL")
    if not destination:
        return
    record = {
        "schema_version": 1,
        "event": event,
        "monotonic_ns": time.monotonic_ns(),
        "wall_time_ns": time.time_ns(),
        **fields,
    }
    path = Path(destination)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(record, sort_keys=True, separators=(",", ":")))
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())


def pytest_sessionstart(session: pytest.Session) -> None:
    """Record session entry."""
    _emit("session.start", rootpath=str(session.config.rootpath))


def pytest_sessionfinish(
    session: pytest.Session, exitstatus: int | pytest.ExitCode
) -> None:
    """Record session completion."""
    _emit(
        "session.finish",
        exitstatus=int(exitstatus),
        rootpath=str(session.config.rootpath),
    )


@pytest.hookimpl(hookwrapper=True)
def pytest_collection(session: pytest.Session) -> Generator[None, None, None]:
    """Bracket collection execution."""
    # The hook signature is fixed by pytest; the session is read after yield.
    _emit("collection.start")
    try:
        yield
    finally:
        _emit("collection.finish", item_count=len(session.items))


def pytest_collection_finish(session: pytest.Session) -> None:
    """Record the final collection summary after collection hooks complete."""
    _emit("collection.summary", item_count=len(session.items))


def pytest_runtest_logstart(nodeid: str, location: tuple[str, int | None, str]) -> None:
    """Record node entry."""
    _emit("node.start", nodeid=nodeid, location=location)


def pytest_runtest_logfinish(
    nodeid: str, location: tuple[str, int | None, str]
) -> None:
    """Record node completion."""
    _emit("node.finish", nodeid=nodeid, location=location)


def pytest_runtest_logreport(report: pytest.TestReport) -> None:
    """Record sanitized outcome data needed to attest equivalent skip behavior."""
    _emit(
        "node.report",
        nodeid=report.nodeid,
        phase=report.when,
        outcome=report.outcome,
    )


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_setup(item: pytest.Item) -> Generator[None, None, None]:
    """Bracket setup execution."""
    _emit("phase.start", nodeid=item.nodeid, phase="setup")
    outcome = yield
    _emit_phase_outcome(item.nodeid, "setup", outcome.excinfo)


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_call(item: pytest.Item) -> Generator[None, None, None]:
    """Bracket call execution."""
    _emit("phase.start", nodeid=item.nodeid, phase="call")
    outcome = yield
    _emit_phase_outcome(item.nodeid, "call", outcome.excinfo)


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_teardown(item: pytest.Item) -> Generator[None, None, None]:
    """Bracket teardown execution."""
    _emit("phase.start", nodeid=item.nodeid, phase="teardown")
    outcome = yield
    _emit_phase_outcome(item.nodeid, "teardown", outcome.excinfo)


def _emit_phase_outcome(
    nodeid: str,
    phase: str,
    excinfo: tuple[type[BaseException], BaseException, object] | None,
) -> None:
    """Classify a hook outcome without persisting exception text or arguments."""
    if excinfo is None:
        _emit("phase.finish", nodeid=nodeid, phase=phase)
        return
    exception_type = excinfo[0]
    event = (
        "phase.abort"
        if issubclass(exception_type, (KeyboardInterrupt, SystemExit))
        else "phase.error"
    )
    _emit(
        event,
        nodeid=nodeid,
        phase=phase,
        exception_type=exception_type.__name__,
    )
