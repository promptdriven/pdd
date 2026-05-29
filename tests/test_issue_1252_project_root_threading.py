"""
Regression tests for Issue #1252 (Gap 1): project_root threading through
operation_log writers/readers and update_main's fix-flow entry point.

Each test is designed to FAIL if its corresponding fix from Step 6a is
reverted. Tests fall into three groups:

1.  Signature contract tests — assert that every metadata function that
    must accept a ``project_root`` kwarg actually does. Catches the
    "accepted-but-unused" regression where the kwarg is silently dropped.

2.  Behavioral threading tests — call each function with
    ``project_root=tmp_path`` and assert the output file lands under
    ``tmp_path/.pdd/meta/`` rather than CWD's ``.pdd/meta/``. This is the
    user-visible orphan symptom from Issue #1211 / #1252.

3.  ``update_main`` re-export tests — assert that ``_detect_project_root``
    and ``_detect_project_root_from_paths`` are importable from
    ``pdd.update_main`` (Req. 11 patchable-symbols contract) and that
    ``_finalize_update_fingerprint`` / the repo-mode pair block call
    ``save_fingerprint`` / ``clear_run_report`` / ``get_run_report_path``
    with an explicit ``project_root`` kwarg derived from the prompt path.

See pdd/operation_log.py header docstrings (Issue #1252 Gap 1) for the
threading contract being defended.
"""

from __future__ import annotations

import inspect
import json
from pathlib import Path
from typing import Optional
from unittest.mock import patch, MagicMock

import pytest

from pdd import operation_log
from pdd.update_main import (
    _detect_project_root,
    _detect_project_root_from_paths,
)


# --------------------------------------------------------------------------
# Group 1 — Signature contract tests
# --------------------------------------------------------------------------

# Every (function, kwarg-name) pair that must exist after the #1252 fix.
# Reverting any one of the Step 6a fixes drops one of these kwargs and
# pytest will surface a clear "missing parameter" failure.
_REQUIRED_PROJECT_ROOT_FUNCTIONS = [
    "save_fingerprint",
    "save_run_report",
    "clear_run_report",
    "_clear_run_report_before_fingerprint",
    "append_log_entry",
    "log_event",
    "load_operation_log",
]


@pytest.mark.parametrize("fn_name", _REQUIRED_PROJECT_ROOT_FUNCTIONS)
def test_operation_log_function_accepts_project_root_kwarg_issue_1252(fn_name):
    """
    Each metadata writer/reader must accept ``project_root`` so callers
    can short-circuit CWD-based detection. Issue #1252 Gap 1.
    """
    fn = getattr(operation_log, fn_name, None)
    assert fn is not None, (
        f"Issue #1252: pdd.operation_log.{fn_name} must exist; "
        "the fix in Step 6a added project_root threading to this symbol."
    )

    sig = inspect.signature(fn)
    assert "project_root" in sig.parameters, (
        f"Issue #1252 Gap 1: {fn_name} must accept a `project_root` kwarg. "
        f"Reverting the Step 6a fix drops this kwarg and the function "
        f"silently anchors on CWD."
    )

    param = sig.parameters["project_root"]
    assert param.default is None, (
        f"Issue #1252: {fn_name}.project_root must default to None "
        "(backwards compat for the ~7 callers that don't pass it)."
    )


# --------------------------------------------------------------------------
# Group 2 — Behavioral threading tests
# --------------------------------------------------------------------------
#
# These tests verify that the kwarg is not merely accepted but actually
# forwarded to the path helpers. They use an isolated tmp_path as the
# explicit project_root and assert the file lands at
# ``tmp_path/.pdd/meta/...`` — proving the threading is real.

def _meta_dir(root: Path) -> Path:
    return root / ".pdd" / "meta"


def test_save_fingerprint_threads_project_root_to_disk_issue_1252(tmp_path):
    """
    Calling save_fingerprint with an explicit project_root must write the
    fingerprint under that root's .pdd/meta — not under CWD.

    This is the primary regression test for the headline Gap 1 bug:
    PR #1234 added the kwarg to get_fingerprint_path but save_fingerprint
    never forwarded it, so the fingerprint orphan still landed at CWD.
    """
    # Provide a prompt path so save_fingerprint doesn't try to call
    # get_pdd_file_paths (which would fail in this synthetic environment).
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_file = prompts_dir / "regmod_python.prompt"
    prompt_file.write_text("% Reg Module\n")

    code_file = tmp_path / "regmod.py"
    code_file.write_text("def x(): pass\n")

    explicit_paths = {"prompt": prompt_file, "code": code_file}

    operation_log.save_fingerprint(
        "regmod", "python",
        operation="generate",
        paths=explicit_paths,
        project_root=tmp_path,
    )

    expected = _meta_dir(tmp_path) / "regmod_python.json"
    assert expected.exists(), (
        f"Issue #1252 Gap 1: save_fingerprint did not write under the "
        f"explicit project_root. Expected {expected} to exist."
    )

    # File must be a valid fingerprint JSON (proves we wrote a real
    # fingerprint, not some stub).
    data = json.loads(expected.read_text())
    assert "command" in data and "pdd_version" in data, (
        "Fingerprint file is malformed; save_fingerprint did not produce "
        "the expected Fingerprint dataclass output."
    )


def test_save_run_report_threads_project_root_to_disk_issue_1252(tmp_path):
    """save_run_report must anchor the report file on explicit project_root."""
    operation_log.save_run_report(
        "regmod", "python",
        {"success": True, "tests_passed": 3},
        project_root=tmp_path,
    )
    expected = _meta_dir(tmp_path) / "regmod_python_run.json"
    assert expected.exists(), (
        f"Issue #1252 Gap 1: save_run_report did not write under the "
        f"explicit project_root. Expected {expected} to exist."
    )
    assert json.loads(expected.read_text()) == {"success": True, "tests_passed": 3}


def test_clear_run_report_threads_project_root_to_disk_issue_1252(tmp_path):
    """
    clear_run_report must delete from the explicit project_root's meta
    dir — not from CWD. We seed a report there, then call clear and check
    it was removed.
    """
    operation_log.save_run_report(
        "regmod", "python", {"x": 1}, project_root=tmp_path
    )
    target = _meta_dir(tmp_path) / "regmod_python_run.json"
    assert target.exists()

    operation_log.clear_run_report("regmod", "python", project_root=tmp_path)
    assert not target.exists(), (
        "Issue #1252 Gap 1: clear_run_report did not delete the report "
        "under the explicit project_root — kwarg was not threaded to "
        "get_run_report_path."
    )


def test_clear_run_report_before_fingerprint_threads_project_root_issue_1252(tmp_path):
    """
    _clear_run_report_before_fingerprint must (a) honor project_root for
    both the existence check and the unlink, and (b) return True on the
    happy-path where no stale report exists.
    """
    # Seed a stale report at the explicit project_root.
    operation_log.save_run_report(
        "regmod", "python", {"stale": True}, project_root=tmp_path
    )
    target = _meta_dir(tmp_path) / "regmod_python_run.json"
    assert target.exists()

    ok = operation_log._clear_run_report_before_fingerprint(
        "regmod", "python", project_root=tmp_path
    )
    assert ok is True, (
        "Issue #1252 Gap 1: _clear_run_report_before_fingerprint did not "
        "return True after successfully clearing the stale report under "
        "the explicit project_root."
    )
    assert not target.exists(), (
        "Issue #1252 Gap 1: the report under the explicit project_root "
        "was not removed."
    )


def test_append_log_entry_threads_project_root_to_disk_issue_1252(tmp_path):
    """
    append_log_entry must write the sync log under the explicit
    project_root's .pdd/meta.
    """
    operation_log.append_log_entry(
        "regmod", "python",
        {"operation": "generate", "success": True},
        project_root=tmp_path,
    )
    expected = _meta_dir(tmp_path) / "regmod_python_sync.log"
    assert expected.exists(), (
        f"Issue #1252 Gap 1: append_log_entry did not write under the "
        f"explicit project_root. Expected {expected} to exist."
    )
    line = expected.read_text().strip().splitlines()[0]
    assert json.loads(line)["operation"] == "generate"


def test_log_event_threads_project_root_to_disk_issue_1252(tmp_path):
    """log_event is a thin wrapper around append_log_entry — must thread project_root."""
    operation_log.log_event(
        "regmod", "python",
        event_type="info", details={"msg": "hello"},
        project_root=tmp_path,
    )
    expected = _meta_dir(tmp_path) / "regmod_python_sync.log"
    assert expected.exists(), (
        f"Issue #1252 Gap 1: log_event did not write under the explicit "
        f"project_root. Expected {expected} to exist."
    )


def test_load_operation_log_threads_project_root_to_disk_issue_1252(tmp_path):
    """
    load_operation_log must read from the explicit project_root, not CWD.
    We seed a log via append_log_entry(project_root=...) then read it back
    via load_operation_log(project_root=...).
    """
    operation_log.append_log_entry(
        "regmod", "python",
        {"operation": "generate", "success": True},
        project_root=tmp_path,
    )

    entries = operation_log.load_operation_log(
        "regmod", "python", project_root=tmp_path
    )
    assert len(entries) == 1, (
        "Issue #1252 Gap 1: load_operation_log did not read from the "
        "explicit project_root — kwarg was not threaded to get_log_path."
    )
    assert entries[0]["operation"] == "generate"


# --------------------------------------------------------------------------
# Group 3 — @log_operation decorator threads project_root
# --------------------------------------------------------------------------

def test_log_operation_decorator_passes_project_root_to_writes_issue_1252(tmp_path):
    """
    When the @log_operation decorator infers a prompt_file, it must derive
    a project_root from the prompt path and pass it explicitly through to
    every metadata write (append_log_entry, _clear_run_report_before_fingerprint,
    save_fingerprint, save_run_report).

    Reverting Step 6a's decorator change drops `project_root=` from those
    calls; this test pins the contract by inspecting the kwargs each
    inner function actually received.
    """
    # Build a fake subproject layout with a .pddrc anchor so the
    # decorator's _detect_project_root_from_paths call resolves to
    # `tmp_path` (not CWD).
    (tmp_path / ".pddrc").write_text("[]")
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_file = prompts_dir / "decmod_python.prompt"
    prompt_file.write_text("% Dec Module\n")

    captured = {}

    def _capture(name):
        def _spy(*args, **kwargs):
            captured.setdefault(name, []).append(kwargs)
            # Return a sane default so the decorator's control flow continues.
            if name == "_clear_run_report_before_fingerprint":
                return True
            return None
        return _spy

    @operation_log.log_operation(
        operation="generate",
        clears_run_report=True,
        updates_fingerprint=True,
    )
    def fake_command(prompt_file):
        # Mirror the shape of a successful generate result.
        return "ok", False, 0.0, "model"

    with patch.object(operation_log, "append_log_entry", side_effect=_capture("append_log_entry")), \
         patch.object(operation_log, "_clear_run_report_before_fingerprint",
                       side_effect=_capture("_clear_run_report_before_fingerprint")), \
         patch.object(operation_log, "save_fingerprint", side_effect=_capture("save_fingerprint")):
        fake_command(prompt_file=str(prompt_file))

    for inner in ("append_log_entry", "_clear_run_report_before_fingerprint", "save_fingerprint"):
        assert inner in captured, f"Decorator never called {inner}"
        call_kwargs = captured[inner][0]
        assert "project_root" in call_kwargs, (
            f"Issue #1252 Gap 1: @log_operation did not pass project_root "
            f"to {inner}. Reverting Step 6a's decorator change reproduces "
            f"the orphan bug from Issue #1211."
        )
        # The decorator should resolve project_root to the subproject root
        # (where .pddrc lives), which is tmp_path here.
        pr = call_kwargs["project_root"]
        assert pr is not None, (
            f"@log_operation passed project_root=None to {inner}; the "
            f".pddrc-based detection from the prompt path should have "
            f"resolved {tmp_path}, not None."
        )
        assert Path(pr).resolve() == tmp_path.resolve(), (
            f"@log_operation resolved project_root={pr!r} for {inner}; "
            f"expected the .pddrc anchor at {tmp_path}."
        )


# --------------------------------------------------------------------------
# Group 4 — update_main re-exports (Req. 11)
# --------------------------------------------------------------------------

def test_update_main_reexports_detect_project_root_issue_1252():
    """
    prompts/update_main_python.prompt Req. 11 requires
    ``_detect_project_root`` and ``_detect_project_root_from_paths`` to
    be importable from ``pdd.update_main`` so tests can monkeypatch them
    at that module level. Step 6a added the re-export.
    """
    # Direct import (top of file) already validates this at import time;
    # the assertions below give a clear failure message if the re-exports
    # are removed and the import is moved/wrapped.
    assert callable(_detect_project_root), (
        "Issue #1252 Req. 11: pdd.update_main._detect_project_root must "
        "be importable as a patchable module-level symbol."
    )
    assert callable(_detect_project_root_from_paths), (
        "Issue #1252 Req. 11: pdd.update_main._detect_project_root_from_paths "
        "must be importable as a patchable module-level symbol."
    )

    # Also verify both are the same function objects as the originals
    # in pdd.operation_log (i.e. a true re-export, not a re-definition).
    assert _detect_project_root is operation_log._detect_project_root
    assert _detect_project_root_from_paths is operation_log._detect_project_root_from_paths


# --------------------------------------------------------------------------
# Group 5 — update_main fix-flow threads project_root to save_fingerprint
# --------------------------------------------------------------------------

def _get_update_main_module():
    """Return the pdd.update_main *module* — bypass the function-shadowing in pdd/__init__.py."""
    import sys
    import pdd.update_main  # noqa: F401  (ensure the submodule is imported)
    return sys.modules["pdd.update_main"]


def test_finalize_single_file_fingerprint_passes_project_root_issue_1252(tmp_path):
    """
    ``_finalize_single_file_fingerprint`` (the post-update path used by
    the `pdd fix` flow) must compute project_root once from the prompt
    path and forward it to both ``_clear_run_report_before_fingerprint``
    and ``save_fingerprint``. Reverting Step 6a's update_main change
    drops the kwarg and the `.pdd/meta/<module>_python.json` orphan from
    Issue #1211 reproduces.
    """
    um = _get_update_main_module()

    # Subproject layout with .pddrc anchor so detection resolves to tmp_path.
    (tmp_path / ".pddrc").write_text("[]")
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()
    prompt_path = prompts_dir / "finalmod_python.prompt"
    prompt_path.write_text("% Final Module\n")
    code_path = tmp_path / "finalmod.py"
    code_path.write_text("def x(): pass\n")

    captured = {}

    def _spy_clear(*args, **kwargs):
        captured["clear"] = kwargs
        return True

    def _spy_save(*args, **kwargs):
        captured["save"] = kwargs

    # The helpers are imported lazily inside the function via
    # ``from .operation_log import ...``, so patch them at the
    # pdd.operation_log module level. infer_module_identity is left intact
    # because the function imports it from the same lazy block.
    with patch.object(operation_log, "_clear_run_report_before_fingerprint", side_effect=_spy_clear), \
         patch.object(operation_log, "save_fingerprint", side_effect=_spy_save):
        um._finalize_single_file_fingerprint(
            prompt_path=prompt_path,
            code_path=code_path,
            sync_metadata=False,
            dry_run=False,
            quiet=True,
            cost=0.0,
            model="gpt-4",
        )

    for k in ("clear", "save"):
        assert k in captured, (
            f"_finalize_single_file_fingerprint never called the {k} helper"
        )
        assert "project_root" in captured[k], (
            f"Issue #1252 Gap 1: _finalize_single_file_fingerprint did not "
            f"pass project_root to {k}. Reverting Step 6a's update_main "
            f"change reproduces the orphan bug."
        )
        pr = captured[k]["project_root"]
        assert pr is not None, (
            f"_finalize_single_file_fingerprint passed project_root=None to "
            f"{k}; the .pddrc-based detection should have resolved {tmp_path}."
        )
        assert Path(pr).resolve() == tmp_path.resolve(), (
            f"_finalize_single_file_fingerprint resolved project_root={pr!r} "
            f"for {k}; expected the .pddrc anchor at {tmp_path}."
        )


def test_finalize_single_file_fingerprint_symbol_exists_issue_1252():
    """
    Sanity guard: ``_finalize_single_file_fingerprint`` is the symbol used
    by the `pdd update` / `pdd fix` post-update flow to thread project_root.
    If it gets renamed or inlined, the test above silently stops covering
    the fix.
    """
    um = _get_update_main_module()
    assert hasattr(um, "_finalize_single_file_fingerprint"), (
        "Issue #1252 Gap 1: pdd.update_main._finalize_single_file_fingerprint "
        "must exist — this is the symbol that threads project_root through "
        "the `pdd update` / `pdd fix` post-update flow."
    )
