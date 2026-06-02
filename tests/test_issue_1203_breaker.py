# tests/test_issue_1203_breaker.py
"""Regression tests for Issue #1203.

The fix-loop circuit breaker must be progress-sensitive: a regeneration that
mismatches N error strings should be able to converge in ~N fix iterations
instead of being killed at 5 consecutive fixes while still making progress.

The breaker reads the failing-test count via ``read_run_report(..., paths=...)``.
Per the PR #1245 review (and Issue #1211), the path hints MUST be forwarded so a
run report living under a *subproject* ``.pdd/meta`` is read correctly when sync
is invoked from the parent directory. A pathless read resolves the wrong meta
dir and reports 0 failures, defeating the progress check.
"""

import json
import os
from pathlib import Path

import pytest

from pdd.sync_orchestration import MAX_CONSECUTIVE_FIXES
from pdd.sync_determine_operation import read_run_report


def _write_run_report(meta_dir: Path, basename: str, language: str, *, tests_failed: int):
    meta_dir.mkdir(parents=True, exist_ok=True)
    report = {
        "timestamp": "2026-05-11T12:42:17",
        "exit_code": 1 if tests_failed else 0,
        "tests_passed": 10,
        "tests_failed": tests_failed,
        "coverage": 92.0,
    }
    (meta_dir / f"{basename}_{language.lower()}_run.json").write_text(json.dumps(report))


def test_run_report_resolves_subproject_meta_from_parent(tmp_path, monkeypatch):
    """read_run_report(paths=...) must read the subproject .pdd/meta even when
    the process CWD is the parent directory (PR #1245 review point #1)."""
    basename, language = "linalg_engine", "python"

    # Parent run CWD with no .pddrc.
    parent = tmp_path
    # Subproject below the run CWD, anchored by its own .pddrc.
    subproj = parent / "subproj"
    (subproj / "src").mkdir(parents=True)
    (subproj / ".pddrc").write_text("# subproject root\n")

    code_file = subproj / "src" / f"{basename}.py"
    code_file.write_text("# generated code\n")

    # Run report lives under the SUBPROJECT meta dir, with 3 failing tests.
    _write_run_report(subproj / ".pdd" / "meta", basename, language, tests_failed=3)

    # Invoke from the parent directory.
    monkeypatch.chdir(parent)
    paths = {"code": code_file}

    rr = read_run_report(basename, language, paths=paths)
    assert rr is not None, "subproject run report should be found via paths hints"
    assert rr.tests_failed == 3

    # Guard against regressing to the pathless call the PR review flagged:
    # from the parent CWD it must NOT find the subproject report.
    rr_pathless = read_run_report(basename, language)
    assert rr_pathless is None or rr_pathless.tests_failed != 3


@pytest.mark.parametrize(
    "failure_series, should_break_on_last",
    [
        # Strictly decreasing each iteration -> still making progress -> stay open.
        ([5, 4, 3, 2, 1], False),
        # Plateau at the breaker threshold -> no progress -> break.
        ([5, 5, 5, 5, 5], True),
        # Decreasing then stalls on the final iteration -> break.
        ([5, 4, 3, 3, 3], True),
    ],
)
def test_progress_sensitive_breaker_condition(failure_series, should_break_on_last):
    """Mirror the inline breaker decision: it fires only when the consecutive-fix
    count has reached the cap AND the latest iteration did not strictly reduce
    the failing-test count."""
    consecutive_fixes = 0
    prev_fix_failures = None
    broke = False

    for current_failures in failure_series:
        consecutive_fixes += 1
        making_progress = (
            current_failures is not None
            and prev_fix_failures is not None
            and current_failures < prev_fix_failures
        )
        prev_fix_failures = current_failures
        if consecutive_fixes >= MAX_CONSECUTIVE_FIXES and not making_progress:
            broke = True
            break

    assert broke is should_break_on_last
