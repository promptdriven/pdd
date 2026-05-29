"""
E2E / integration tests for Issue #1252 — project_root threading across
the full operation_log + sync_determine_operation + update_main chain.

These tests complement the unit-level regression tests in
``tests/test_issue_1252_project_root_threading.py`` (which use mocks to
pin the kwarg-forwarding contract per function). The tests here exercise
the real filesystem — no path mocks — through:

  * ``pdd.operation_log.save_fingerprint`` ↔ ``pdd.sync_determine_operation.read_fingerprint``
    (cross-module roundtrip — the two sides MUST share an anchor)
  * ``pdd.operation_log._resolve_meta_dir`` driven by real ``.pddrc``
    discovery from a parent-CWD invocation
  * ``pdd.update_main._finalize_single_file_fingerprint`` with no
    operation_log mocks (the real `pdd update` post-finalization path)
  * ``pdd.operation_log.log_operation`` decorator end-to-end with a real
    subproject and real meta writes

Each test is set up so the run CWD does NOT contain a ``.pddrc`` and the
subproject DOES, mirroring the original Issue #1211 / #1252 bug report
(``pdd fix`` invoked from a parent dir above the subproject). The
discrimination criterion is the same for every test: no orphan
``.pdd/meta/<module>_python.json`` may land at the parent CWD; the
fingerprint MUST land under ``<subproject>/.pdd/meta/``.

If any Step 6a fix is reverted — `save_fingerprint` drops `project_root`,
`update_main` stops detecting/passing it, the @log_operation decorator
stops forwarding, etc. — at least one of these tests fails.
"""

from __future__ import annotations

import json
import os
from pathlib import Path

import pytest

from pdd import operation_log
from pdd.operation_log import (
    _detect_project_root,
    _detect_project_root_from_paths,
    log_operation,
    save_fingerprint,
    save_run_report,
    clear_run_report,
    append_log_entry,
    load_operation_log,
)
from pdd.sync_determine_operation import read_fingerprint
from pdd.update_main import _finalize_single_file_fingerprint


# ---------------------------------------------------------------------------
# Shared subproject scaffolding
# ---------------------------------------------------------------------------

_PDDRC_BODY = """version: "1.0"
contexts:
  default:
    paths:
      - "**"
    defaults:
      generate_output_path: "src/"
      test_output_path: "tests/"
"""


def _build_parent_and_subproject(tmp_path: Path) -> dict:
    """Build a parent-cwd + nested subproject with a real .pddrc anchor.

    Layout:
        tmp_path/
          parent_cwd/                  <- chdir target (NO .pddrc here)
          extensions/sub/
            .pddrc                     <- the project_root anchor
            prompts/regmod_python.prompt
            src/regmod.py
            tests/test_regmod.py
    """
    parent_cwd = tmp_path / "parent_cwd"
    parent_cwd.mkdir()

    subproject = tmp_path / "extensions" / "sub"
    subproject.mkdir(parents=True)
    (subproject / ".pddrc").write_text(_PDDRC_BODY, encoding="utf-8")

    prompts_dir = subproject / "prompts"
    prompts_dir.mkdir()
    prompt = prompts_dir / "regmod_python.prompt"
    prompt.write_text("% Reg Module\nGenerate something.\n", encoding="utf-8")

    src_dir = subproject / "src"
    src_dir.mkdir()
    code = src_dir / "regmod.py"
    code.write_text("def x():\n    return 1\n", encoding="utf-8")

    tests_dir = subproject / "tests"
    tests_dir.mkdir()
    test = tests_dir / "test_regmod.py"
    test.write_text("def test_x():\n    assert True\n", encoding="utf-8")

    return {
        "parent_cwd": parent_cwd,
        "subproject": subproject,
        "prompt": prompt,
        "code": code,
        "test": test,
    }


def _assert_no_parent_orphan(parent_cwd: Path) -> None:
    """The bug's user-visible symptom — guard it from EVERY E2E test."""
    parent_meta = parent_cwd / ".pdd" / "meta"
    assert not parent_meta.exists(), (
        f"Issue #1211 / #1252 orphan symptom reproduced: a .pdd/meta dir "
        f"was created at the run CWD ({parent_cwd}) instead of the "
        f"subproject root. Contents: "
        f"{[p.name for p in parent_meta.iterdir()] if parent_meta.exists() else '<none>'}"
    )
    # The whole .pdd tree should also be absent — no .pdd/locks, .pdd/state, etc.
    parent_pdd = parent_cwd / ".pdd"
    if parent_pdd.exists():
        # Tolerate empty .pdd directories (some helpers ensure dir before guard),
        # but never tolerate meta files leaking to CWD.
        leaked = list(parent_pdd.rglob("*.json")) + list(parent_pdd.rglob("*.log"))
        assert not leaked, (
            f"Issue #1252: orphan meta files leaked to {parent_pdd}: {leaked}"
        )


# ---------------------------------------------------------------------------
# Group A — operation_log.save_fingerprint ↔ sync_determine_operation.read_fingerprint
#           cross-module roundtrip with explicit project_root.
# ---------------------------------------------------------------------------

def test_save_then_read_fingerprint_roundtrip_with_explicit_project_root(tmp_path, monkeypatch):
    """
    Integration: ``save_fingerprint(project_root=X)`` writes a file that
    ``read_fingerprint(project_root=X)`` can read back, even when CWD is
    a parent dir with no .pddrc of its own.

    This proves the two sides of the writer/reader contract share an
    anchor — the headline Gap 1 risk was that writers fell back to CWD
    while readers honored the caller's `project_root`, producing silent
    state divergence.
    """
    layout = _build_parent_and_subproject(tmp_path)
    monkeypatch.chdir(layout["parent_cwd"])

    paths = {"prompt": layout["prompt"], "code": layout["code"]}

    save_fingerprint(
        "regmod", "python",
        operation="update",
        paths=paths,
        project_root=layout["subproject"],
        cost=0.0,
        model="stub-model",
    )

    # Writer side: lands in the subproject.
    written = layout["subproject"] / ".pdd" / "meta" / "regmod_python.json"
    assert written.exists(), (
        f"save_fingerprint(project_root=subproject) did not write "
        f"{written}; cross-module threading broken."
    )

    # Reader side, same explicit anchor — must round-trip the same record.
    fp = read_fingerprint(
        "regmod", "python",
        paths=paths,
        project_root=layout["subproject"],
    )
    assert fp is not None, (
        "read_fingerprint(project_root=subproject) returned None even "
        "though save_fingerprint just wrote to the same anchor — the two "
        "modules are not sharing a meta-dir resolution."
    )
    assert fp.command == "update"
    assert fp.prompt_hash is not None, (
        "Roundtrip fingerprint is missing prompt_hash; save did not "
        "hash the prompt file at the resolved anchor."
    )

    _assert_no_parent_orphan(layout["parent_cwd"])


def test_save_fingerprint_autodetects_subproject_from_paths_when_cwd_is_parent(
    tmp_path, monkeypatch
):
    """
    Integration: with NO explicit ``project_root`` but with ``paths``
    pointing into the subproject, ``save_fingerprint`` MUST still anchor
    on the subproject (via ``_detect_project_root_from_paths``), not on
    the parent CWD. This exercises the auto-detection fallback path that
    the ~7 untouched callers still depend on.
    """
    layout = _build_parent_and_subproject(tmp_path)
    monkeypatch.chdir(layout["parent_cwd"])

    paths = {"prompt": layout["prompt"], "code": layout["code"]}

    # Deliberately do NOT pass project_root — rely on path-based detection.
    save_fingerprint(
        "regmod", "python",
        operation="generate",
        paths=paths,
    )

    expected = layout["subproject"] / ".pdd" / "meta" / "regmod_python.json"
    assert expected.exists(), (
        f"Auto-detection from paths failed: fingerprint did not land at "
        f"{expected}. _detect_project_root_from_paths likely did not walk "
        f"up to the subproject's .pddrc."
    )

    _assert_no_parent_orphan(layout["parent_cwd"])


def test_save_fingerprint_explicit_root_overrides_misleading_cwd_pddrc(
    tmp_path, monkeypatch
):
    """
    Integration: when the run CWD has its OWN .pddrc (a parent project)
    but the caller passes an explicit ``project_root`` for a subproject,
    the explicit kwarg MUST win. This is the precedence-order contract
    documented in ``_resolve_meta_dir``.
    """
    layout = _build_parent_and_subproject(tmp_path)
    # Plant a competing .pddrc at the parent CWD itself.
    (layout["parent_cwd"] / ".pddrc").write_text(_PDDRC_BODY, encoding="utf-8")
    monkeypatch.chdir(layout["parent_cwd"])

    paths = {"prompt": layout["prompt"], "code": layout["code"]}

    save_fingerprint(
        "regmod", "python",
        operation="update",
        paths=paths,
        project_root=layout["subproject"],
    )

    expected = layout["subproject"] / ".pdd" / "meta" / "regmod_python.json"
    assert expected.exists(), (
        "Explicit project_root did not override the parent-CWD .pddrc; "
        "_resolve_meta_dir precedence is wrong."
    )
    # And critically: nothing under parent's .pdd/meta.
    parent_orphan = layout["parent_cwd"] / ".pdd" / "meta" / "regmod_python.json"
    assert not parent_orphan.exists(), (
        f"Explicit project_root was ignored — fingerprint also landed at "
        f"{parent_orphan} (parent CWD's .pddrc)."
    )


# ---------------------------------------------------------------------------
# Group B — update_main._finalize_single_file_fingerprint end-to-end
#           (no operation_log mocks; real filesystem writes).
# ---------------------------------------------------------------------------

def test_finalize_single_file_fingerprint_e2e_no_mocks(tmp_path, monkeypatch):
    """
    Integration: drive ``_finalize_single_file_fingerprint`` from a
    parent CWD with no mocks on operation_log. This is what `pdd update`
    runs after a successful update. The combined effect MUST be:

      * No `.pdd/meta/` orphan at the parent CWD.
      * Fingerprint exists under `<subproject>/.pdd/meta/regmod_python.json`.
      * The fingerprint is readable by `read_fingerprint(project_root=...)`.

    Reverting Step 6a's `update_main` change (removing the
    `_detect_project_root_from_paths(...)` call or the `project_root=`
    kwarg on the `save_fingerprint` site) reproduces the Issue #1211
    orphan symptom and this test fails.
    """
    layout = _build_parent_and_subproject(tmp_path)
    monkeypatch.chdir(layout["parent_cwd"])

    # No mocks: invoke the real post-update finalization helper.
    _finalize_single_file_fingerprint(
        prompt_path=layout["prompt"],
        code_path=layout["code"],
        sync_metadata=False,
        dry_run=False,
        quiet=True,
        cost=0.123,
        model="integration-test",
    )

    expected = layout["subproject"] / ".pdd" / "meta" / "regmod_python.json"
    assert expected.exists(), (
        f"_finalize_single_file_fingerprint did not produce {expected}. "
        f"Either project_root detection or save_fingerprint threading is "
        f"broken end-to-end."
    )

    # Same anchor must round-trip through the reader.
    fp = read_fingerprint(
        "regmod", "python",
        paths={"prompt": layout["prompt"], "code": layout["code"]},
        project_root=layout["subproject"],
    )
    assert fp is not None and fp.command == "update", (
        "Roundtrip readback failed after _finalize_single_file_fingerprint."
    )

    _assert_no_parent_orphan(layout["parent_cwd"])


def test_finalize_single_file_fingerprint_e2e_respects_sync_metadata_skip(
    tmp_path, monkeypatch
):
    """
    Integration sanity: when ``sync_metadata=True`` the helper must skip
    writing — the orchestrator owns the stage. We assert that the
    finalize call writes NOTHING (no fingerprint, no orphan) even though
    a project_root is detectable.

    This pins the precedence: scope guards beat anchor resolution.
    """
    layout = _build_parent_and_subproject(tmp_path)
    monkeypatch.chdir(layout["parent_cwd"])

    _finalize_single_file_fingerprint(
        prompt_path=layout["prompt"],
        code_path=layout["code"],
        sync_metadata=True,  # <-- skip
        dry_run=False,
        quiet=True,
        cost=0.0,
        model="integration-test",
    )

    sub_fp = layout["subproject"] / ".pdd" / "meta" / "regmod_python.json"
    assert not sub_fp.exists(), (
        "sync_metadata=True must skip the write; helper wrote a "
        "fingerprint anyway."
    )
    _assert_no_parent_orphan(layout["parent_cwd"])


# ---------------------------------------------------------------------------
# Group C — @log_operation decorator end-to-end (real filesystem, no mocks).
# ---------------------------------------------------------------------------

def test_log_operation_decorator_e2e_real_filesystem(tmp_path, monkeypatch):
    """
    Integration: a function decorated with ``@log_operation`` and called
    with a prompt under a subproject MUST write its sync log AND its
    fingerprint to the subproject's `.pdd/meta`, not to the parent CWD.

    This is the full decorator → operation_log → filesystem path that
    `pdd generate`, `pdd test`, `pdd example`, `pdd fix` all rely on.
    """
    layout = _build_parent_and_subproject(tmp_path)
    monkeypatch.chdir(layout["parent_cwd"])

    @log_operation(
        operation="generate",
        clears_run_report=True,
        updates_fingerprint=True,
    )
    def fake_generate(prompt_file):
        # Mirror a successful generate result tuple.
        return "ok", False, 0.0, "stub-model"

    fake_generate(prompt_file=str(layout["prompt"]))

    sub_meta = layout["subproject"] / ".pdd" / "meta"
    assert sub_meta.exists(), (
        "Decorator did not create the subproject .pdd/meta dir; "
        "project_root detection from the prompt path failed."
    )

    sync_log = sub_meta / "regmod_python_sync.log"
    assert sync_log.exists(), (
        f"Decorator did not write sync log at {sync_log}. "
        "append_log_entry threading regression."
    )
    fingerprint = sub_meta / "regmod_python.json"
    assert fingerprint.exists(), (
        f"Decorator did not write fingerprint at {fingerprint}. "
        "save_fingerprint threading regression."
    )

    # The sync log must contain a structured entry for the operation.
    line = sync_log.read_text().strip().splitlines()[-1]
    entry = json.loads(line)
    assert entry.get("operation") == "generate"
    assert entry.get("success") is True

    _assert_no_parent_orphan(layout["parent_cwd"])


def test_log_operation_decorator_e2e_exception_path_still_anchors_correctly(
    tmp_path, monkeypatch
):
    """
    Integration: when the decorated function raises, the decorator still
    logs the attempt — to the SUBPROJECT, not the parent CWD. The
    exception-handling branch in the decorator previously had its own
    code path that could (in principle) skip the project_root the happy
    path computed; this test pins that exceptions and successes share
    the same anchor.
    """
    layout = _build_parent_and_subproject(tmp_path)
    monkeypatch.chdir(layout["parent_cwd"])

    @log_operation(
        operation="generate",
        clears_run_report=False,
        updates_fingerprint=False,
    )
    def fake_generate(prompt_file):
        # Drive the decorator's exception branch.
        raise RuntimeError("simulated LLM failure")

    with pytest.raises(RuntimeError, match="simulated LLM failure"):
        fake_generate(prompt_file=str(layout["prompt"]))

    sub_meta = layout["subproject"] / ".pdd" / "meta"
    sync_log = sub_meta / "regmod_python_sync.log"
    assert sync_log.exists(), (
        f"Decorator exception-path did not write sync log at {sync_log}; "
        "the project_root computed by the decorator must apply to both "
        "success and exception flows."
    )

    line = sync_log.read_text().strip().splitlines()[-1]
    entry = json.loads(line)
    assert entry.get("operation") == "generate"
    # An exception MUST be recorded as a non-success.
    assert entry.get("success") is False, (
        "Decorator recorded a raising function as success=True; the "
        "exception branch is broken."
    )

    _assert_no_parent_orphan(layout["parent_cwd"])


# ---------------------------------------------------------------------------
# Group D — Multi-call integration: save → clear → save with explicit root.
# ---------------------------------------------------------------------------

def test_save_clear_save_sequence_keeps_state_consistent_with_explicit_root(
    tmp_path, monkeypatch
):
    """
    Integration: a realistic command sequence (write run report, clear
    it before a new fingerprint, then write the fingerprint) must keep
    every write anchored on the same explicit project_root and the
    corresponding readers must see the post-sequence state.

    This is the contract `_clear_run_report_before_fingerprint` defends:
    a fresh fingerprint must NEVER coexist with a stale `_run.json`
    (issue #1106). Threading regressions break the invariant silently
    when the clear and the save resolve to different meta dirs.
    """
    layout = _build_parent_and_subproject(tmp_path)
    monkeypatch.chdir(layout["parent_cwd"])

    pr = layout["subproject"]
    paths = {"prompt": layout["prompt"], "code": layout["code"]}

    # 1. seed a stale run report.
    save_run_report(
        "regmod", "python",
        {"success": False, "tests_passed": 0},
        paths=paths,
        project_root=pr,
    )
    run_report = pr / ".pdd" / "meta" / "regmod_python_run.json"
    assert run_report.exists()

    # 2. clear it via the underscore helper (the actual pre-fingerprint guard).
    ok = operation_log._clear_run_report_before_fingerprint(
        "regmod", "python",
        paths=paths,
        project_root=pr,
    )
    assert ok is True
    assert not run_report.exists(), (
        "Issue #1106 + #1252: _clear_run_report_before_fingerprint did "
        "not remove the report at the explicit project_root — clear and "
        "save are anchored differently."
    )

    # 3. write the fingerprint and confirm both readers see the new state
    #    AND the (now-absent) run report.
    save_fingerprint(
        "regmod", "python",
        operation="update",
        paths=paths,
        project_root=pr,
    )
    fp = read_fingerprint("regmod", "python", paths=paths, project_root=pr)
    assert fp is not None and fp.command == "update", (
        "Post-sequence read_fingerprint did not see the freshly-written "
        "fingerprint at the explicit project_root."
    )
    assert not run_report.exists(), (
        "Post-sequence: run report reappeared, violating the "
        "save_fingerprint/clear coexistence invariant (#1106)."
    )

    _assert_no_parent_orphan(layout["parent_cwd"])


# ---------------------------------------------------------------------------
# Group E — Operation log (append + load) cross-call integration.
# ---------------------------------------------------------------------------

def test_append_and_load_operation_log_cross_call_with_explicit_root(
    tmp_path, monkeypatch
):
    """
    Integration: ``append_log_entry`` and ``load_operation_log`` MUST
    share an anchor when both receive the same ``project_root``. This
    catches the regression where the writer threaded the kwarg but the
    reader silently fell back to CWD (or vice-versa), producing logs
    that the loader could never find.
    """
    layout = _build_parent_and_subproject(tmp_path)
    monkeypatch.chdir(layout["parent_cwd"])

    pr = layout["subproject"]
    for op in ("generate", "test", "fix"):
        append_log_entry(
            "regmod", "python",
            {"operation": op, "success": True, "cost": 0.01},
            project_root=pr,
        )

    sync_log = pr / ".pdd" / "meta" / "regmod_python_sync.log"
    assert sync_log.exists()

    entries = load_operation_log("regmod", "python", project_root=pr)
    assert len(entries) == 3, (
        f"Reader/writer anchor mismatch: wrote 3 entries via "
        f"append_log_entry(project_root={pr}) but load_operation_log "
        f"(same project_root) returned {len(entries)}."
    )
    assert [e["operation"] for e in entries] == ["generate", "test", "fix"]

    _assert_no_parent_orphan(layout["parent_cwd"])


# ---------------------------------------------------------------------------
# Group F — Discrimination guard: tests must fail against pre-fix HEAD.
# ---------------------------------------------------------------------------
#
# This isn't a test in the pytest sense — it's a documented invariant the
# test author verified locally and the reviewer can re-verify. Steps to
# discriminate (per Issue #1252 Gap 2):
#
#     git stash                        # remove Step 6a fixes
#     pytest tests/test_issue_1252_project_root_e2e.py -x
#     # -> at least one test in Groups A–E fails because save_fingerprint
#     #    no longer accepts project_root OR update_main doesn't pass it.
#     git stash pop                    # restore Step 6a fixes
#     pytest tests/test_issue_1252_project_root_e2e.py
#     # -> all tests pass.
#
# The discrimination is mechanical: every Group A/B/D/E test passes a
# `project_root=` kwarg to a function whose pre-fix signature does not
# accept that kwarg, so pytest surfaces a TypeError. Group C drives the
# decorator end-to-end and asserts on subproject-anchored output files
# that the pre-fix decorator did not produce (it anchored on CWD).
