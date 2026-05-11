"""Tests for pdd.metadata_finalize.

Test plan (mirrors the spec in prompts/metadata_finalize_python.prompt):

1. MetadataReport dataclass: every spec field exists with the correct default.
2. finalize_metadata return type is MetadataReport.
3. Target resolution:
   3a. Bare basename ("foo") -> basename="foo".
   3b. Prompt-path target ("prompts/foo_python.prompt") -> basename="foo", language="python".
   3c. Code-path target ("foo.py") -> basename="foo", language inferred from extension.
4. Language inference:
   4a. language=None + prompt suffix -> inferred.
   4b. explicit language arg overrides inference.
   4c. unresolvable language path falls back to default ("python").
5. get_pdd_file_paths called with (basename, language, prompts_dir, context_override=...).
6. fingerprint_state:
   6a. "missing" when read_fingerprint returns None.
   6b. "current" when fingerprint exists and no stale components.
   6c. "stale" when any stored hash != current hash for a present file.
7. run_report_state:
   7a. "missing" when no run report.
   7b. "skipped" when fingerprint.command startswith "skip:" — supersedes "missing".
   7c. "stale" when run-report test hash != current OR prompt/code/example stale.
   7d. "current" when run report matches and sources are not stale.
8. stale_components:
   8a. Empty when fingerprint absent.
   8b. Lists each component whose hash differs from stored.
   8c. Missing file does NOT count as stale.
   8d. test_files dict mismatch produces "test" in stale_components.
9. files_present:
   9a. Path keys map to Path.exists().
   9b. test_files key requires non-empty list AND every entry exists.
10. dry_run=True:
    10a. No call to operation_log.save_fingerprint or clear_run_report.
    10b. No SyncLock acquisition (does not write a lock file).
    10c. wrote_fingerprint=False, cleared_run_report=False.
    10d. report.dry_run=True.
    10e. Repeated dry-run calls return identical report content (determinism).
11. dry_run=False:
    11a. SyncLock(basename, language) acquired.
    11b. operation_log.save_fingerprint called with operation="metadata-finalize", paths=...
    11c. wrote_fingerprint=True on success.
    11d. clear_run_report called only when run_report_state == "stale".
    11e. Skip fingerprint write when prompt file is missing; warning recorded.
12. Error handling:
    12a. Empty target -> ValueError.
    12b. get_pdd_file_paths failure -> ValueError (wrapped).
    12c. Lock acquisition errors propagate (re-raised).
    12d. Unreadable run report is recorded as a warning, not aborted.
13. include_deps forwarded to calculate_current_hashes from stored fingerprint.
14. Regression: skip: command takes precedence over missing run report (bug fixed in verify).
15. Regression: dry_run does not write the lock file (bug fixed in verify).
"""
from __future__ import annotations

import os
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional
from unittest.mock import MagicMock, patch

import pytest

# Ensure repo root on path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from pdd.metadata_finalize import MetadataReport, finalize_metadata


# ---------------------------------------------------------------------------
# Fake dataclasses that mimic the shape of the real Fingerprint / RunReport.
# Using simple stand-ins avoids importing the heavy sync_determine_operation
# module just for type construction in tests.
# ---------------------------------------------------------------------------
@dataclass
class _FakeFingerprint:
    pdd_version: str = "1.0.0"
    timestamp: str = "2026-01-01T00:00:00+00:00"
    command: str = "generate"
    prompt_hash: Optional[str] = None
    code_hash: Optional[str] = None
    example_hash: Optional[str] = None
    test_hash: Optional[str] = None
    test_files: Optional[Dict[str, str]] = None
    include_deps: Optional[Dict[str, str]] = None


@dataclass
class _FakeRunReport:
    timestamp: str = "2026-01-01T00:00:00+00:00"
    exit_code: int = 0
    tests_passed: int = 1
    tests_failed: int = 0
    coverage: float = 0.9
    test_hash: Optional[str] = None
    test_files: Optional[Dict[str, str]] = None


class _FakeLock:
    """Minimal context manager mimicking SyncLock without disk writes."""

    instances: List["_FakeLock"] = []

    def __init__(self, basename: str, language: str) -> None:
        self.basename = basename
        self.language = language
        self.entered = False
        self.exited = False
        _FakeLock.instances.append(self)

    def __enter__(self) -> "_FakeLock":
        self.entered = True
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        self.exited = True


@pytest.fixture(autouse=True)
def _reset_fake_lock_instances():
    _FakeLock.instances = []
    yield
    _FakeLock.instances = []


@pytest.fixture
def patched_deps(tmp_path, monkeypatch):
    """Patch all lazy imports finalize_metadata pulls in.

    Returns a dict of MagicMock handles so tests can configure return values
    and assert on call args.
    """
    paths = {
        "prompt": tmp_path / "prompts" / "demo_python.prompt",
        "code": tmp_path / "demo.py",
        "example": tmp_path / "examples" / "demo_example.py",
        "test": tmp_path / "tests" / "test_demo.py",
        "test_files": [tmp_path / "tests" / "test_demo.py"],
    }
    # Default: files exist
    paths["prompt"].parent.mkdir(parents=True, exist_ok=True)
    paths["example"].parent.mkdir(parents=True, exist_ok=True)
    paths["test"].parent.mkdir(parents=True, exist_ok=True)
    for key in ("prompt", "code", "example", "test"):
        paths[key].write_text("x")

    handles = {
        "get_pdd_file_paths": MagicMock(return_value=paths),
        "read_fingerprint": MagicMock(return_value=None),
        "read_run_report": MagicMock(return_value=None),
        "calculate_current_hashes": MagicMock(
            return_value={
                "prompt_hash": "PH",
                "code_hash": "CH",
                "example_hash": "EH",
                "test_hash": "TH",
                "test_files": {"test_demo.py": "TH"},
                "include_deps": {},
            }
        ),
        "SyncLock": _FakeLock,
        "save_fingerprint": MagicMock(),
        "clear_run_report": MagicMock(),
        "paths": paths,
    }

    import pdd.sync_determine_operation as sdo
    import pdd.operation_log as op_log

    monkeypatch.setattr(sdo, "get_pdd_file_paths", handles["get_pdd_file_paths"])
    monkeypatch.setattr(sdo, "read_fingerprint", handles["read_fingerprint"])
    monkeypatch.setattr(sdo, "read_run_report", handles["read_run_report"])
    monkeypatch.setattr(sdo, "calculate_current_hashes", handles["calculate_current_hashes"])
    monkeypatch.setattr(sdo, "SyncLock", handles["SyncLock"])
    monkeypatch.setattr(op_log, "save_fingerprint", handles["save_fingerprint"])
    monkeypatch.setattr(op_log, "clear_run_report", handles["clear_run_report"])

    return handles


# ---------------------------------------------------------------------------
# 1. MetadataReport dataclass
# ---------------------------------------------------------------------------
def test_metadata_report_has_all_spec_fields():
    """The dataclass must expose every field listed in the spec."""
    rpt = MetadataReport(
        basename="b",
        language="python",
        paths={"prompt": "p"},
        files_present={"prompt": True},
        fingerprint_state="current",
        run_report_state="missing",
    )
    assert rpt.basename == "b"
    assert rpt.language == "python"
    assert rpt.paths == {"prompt": "p"}
    assert rpt.files_present == {"prompt": True}
    assert rpt.fingerprint_state == "current"
    assert rpt.run_report_state == "missing"
    assert rpt.stale_components == []
    assert rpt.wrote_fingerprint is False
    assert rpt.cleared_run_report is False
    assert rpt.warnings == []
    assert rpt.dry_run is False


# ---------------------------------------------------------------------------
# 2. return type
# ---------------------------------------------------------------------------
def test_finalize_metadata_returns_metadata_report(patched_deps):
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert isinstance(rpt, MetadataReport)


# ---------------------------------------------------------------------------
# 3. Target resolution
# ---------------------------------------------------------------------------
def test_bare_basename_resolves(patched_deps):
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert rpt.basename == "demo"
    assert rpt.language == "python"


def test_prompt_path_target_resolves_basename_and_language(patched_deps):
    rpt = finalize_metadata("prompts/foo_python.prompt", dry_run=True)
    assert rpt.basename == "foo"
    assert rpt.language == "python"


def test_code_path_target_resolves_basename(patched_deps):
    rpt = finalize_metadata("demo.py", dry_run=True)
    assert rpt.basename == "demo"
    assert rpt.language == "python"


def test_test_prefix_stripped_from_code_path(patched_deps):
    rpt = finalize_metadata("tests/test_demo.py", dry_run=True)
    assert rpt.basename == "demo"


def test_example_prefix_stripped_from_code_path(patched_deps):
    rpt = finalize_metadata("examples/example_demo.py", dry_run=True)
    assert rpt.basename == "demo"


# ---------------------------------------------------------------------------
# 4. Language inference: explicit arg overrides
# ---------------------------------------------------------------------------
def test_explicit_language_overrides_prompt_suffix(patched_deps):
    rpt = finalize_metadata(
        "prompts/foo_python.prompt", language="javascript", dry_run=True
    )
    assert rpt.language == "javascript"


# ---------------------------------------------------------------------------
# 5. get_pdd_file_paths called with right args
# ---------------------------------------------------------------------------
def test_get_pdd_file_paths_called_with_kwargs(patched_deps):
    finalize_metadata(
        "demo",
        language="python",
        prompts_dir="my_prompts",
        context_override="ctx",
        dry_run=True,
    )
    handle = patched_deps["get_pdd_file_paths"]
    handle.assert_called_once()
    args, kwargs = handle.call_args
    assert args[0] == "demo"
    assert args[1] == "python"
    assert args[2] == "my_prompts"
    assert kwargs.get("context_override") == "ctx"


# ---------------------------------------------------------------------------
# 6. fingerprint_state
# ---------------------------------------------------------------------------
def test_fingerprint_state_missing_when_no_fingerprint(patched_deps):
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert rpt.fingerprint_state == "missing"


def test_fingerprint_state_current_when_hashes_match(patched_deps):
    patched_deps["read_fingerprint"].return_value = _FakeFingerprint(
        prompt_hash="PH",
        code_hash="CH",
        example_hash="EH",
        test_hash="TH",
        test_files={"test_demo.py": "TH"},
    )
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert rpt.fingerprint_state == "current"
    assert rpt.stale_components == []


def test_fingerprint_state_stale_when_code_hash_diverges(patched_deps):
    patched_deps["read_fingerprint"].return_value = _FakeFingerprint(
        prompt_hash="PH",
        code_hash="OLD",  # divergent
        example_hash="EH",
        test_hash="TH",
        test_files={"test_demo.py": "TH"},
    )
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert rpt.fingerprint_state == "stale"
    assert "code" in rpt.stale_components


# ---------------------------------------------------------------------------
# 7. run_report_state
# ---------------------------------------------------------------------------
def test_run_report_state_missing_when_absent(patched_deps):
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert rpt.run_report_state == "missing"


def test_run_report_state_skipped_when_fingerprint_command_skip(patched_deps):
    """Bug #23 regression: skip: command supersedes missing run report."""
    patched_deps["read_fingerprint"].return_value = _FakeFingerprint(
        command="skip:test",
        prompt_hash="PH",
        code_hash="CH",
        example_hash="EH",
        test_hash="TH",
        test_files={"test_demo.py": "TH"},
    )
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert rpt.run_report_state == "skipped"


def test_run_report_state_stale_when_test_hash_differs(patched_deps):
    patched_deps["read_fingerprint"].return_value = _FakeFingerprint(
        prompt_hash="PH",
        code_hash="CH",
        example_hash="EH",
        test_hash="TH",
        test_files={"test_demo.py": "TH"},
    )
    patched_deps["read_run_report"].return_value = _FakeRunReport(
        test_hash="OLD", test_files={"test_demo.py": "OLD"}
    )
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert rpt.run_report_state == "stale"


def test_run_report_state_stale_when_code_is_stale(patched_deps):
    patched_deps["read_fingerprint"].return_value = _FakeFingerprint(
        prompt_hash="PH",
        code_hash="OLD",  # code stale
        example_hash="EH",
        test_hash="TH",
        test_files={"test_demo.py": "TH"},
    )
    patched_deps["read_run_report"].return_value = _FakeRunReport(
        test_hash="TH", test_files={"test_demo.py": "TH"}
    )
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert rpt.run_report_state == "stale"


def test_run_report_state_current_when_all_match(patched_deps):
    patched_deps["read_fingerprint"].return_value = _FakeFingerprint(
        prompt_hash="PH",
        code_hash="CH",
        example_hash="EH",
        test_hash="TH",
        test_files={"test_demo.py": "TH"},
    )
    patched_deps["read_run_report"].return_value = _FakeRunReport(
        test_hash="TH", test_files={"test_demo.py": "TH"}
    )
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert rpt.run_report_state == "current"


# ---------------------------------------------------------------------------
# 8. stale_components
# ---------------------------------------------------------------------------
def test_stale_components_empty_when_fingerprint_absent(patched_deps):
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert rpt.stale_components == []


def test_stale_components_lists_all_diverged(patched_deps):
    patched_deps["read_fingerprint"].return_value = _FakeFingerprint(
        prompt_hash="OLDP",
        code_hash="OLDC",
        example_hash="EH",
        test_hash="TH",
        test_files={"test_demo.py": "TH"},
    )
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert set(rpt.stale_components) >= {"prompt", "code"}


def test_missing_file_not_marked_stale(patched_deps):
    # Remove code file -> not present -> should NOT appear in stale_components.
    patched_deps["paths"]["code"].unlink()
    patched_deps["calculate_current_hashes"].return_value = {
        "prompt_hash": "PH",
        # code_hash absent because file gone
        "example_hash": "EH",
        "test_hash": "TH",
        "test_files": {"test_demo.py": "TH"},
        "include_deps": {},
    }
    patched_deps["read_fingerprint"].return_value = _FakeFingerprint(
        prompt_hash="PH",
        code_hash="OLDC",
        example_hash="EH",
        test_hash="TH",
        test_files={"test_demo.py": "TH"},
    )
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert "code" not in rpt.stale_components


def test_test_files_dict_mismatch_yields_test_stale(patched_deps):
    patched_deps["read_fingerprint"].return_value = _FakeFingerprint(
        prompt_hash="PH",
        code_hash="CH",
        example_hash="EH",
        test_hash="TH",
        test_files={"test_demo.py": "OLDHASH"},
    )
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert "test" in rpt.stale_components


# ---------------------------------------------------------------------------
# 9. files_present
# ---------------------------------------------------------------------------
def test_files_present_reflects_exists(patched_deps):
    patched_deps["paths"]["example"].unlink()
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert rpt.files_present["prompt"] is True
    assert rpt.files_present["code"] is True
    assert rpt.files_present["example"] is False
    assert rpt.files_present["test"] is True


def test_files_present_test_files_empty_list_is_false(patched_deps):
    patched_deps["paths"]["test_files"] = []
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert rpt.files_present["test_files"] is False


def test_files_present_test_files_requires_all_exist(patched_deps):
    # Add a non-existent extra entry.
    patched_deps["paths"]["test_files"] = [
        patched_deps["paths"]["test"],
        Path("/nonexistent/test_other.py"),
    ]
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert rpt.files_present["test_files"] is False


# ---------------------------------------------------------------------------
# 10. dry_run=True semantics
# ---------------------------------------------------------------------------
def test_dry_run_does_not_call_save_fingerprint(patched_deps):
    finalize_metadata("demo", language="python", dry_run=True)
    patched_deps["save_fingerprint"].assert_not_called()
    patched_deps["clear_run_report"].assert_not_called()


def test_dry_run_does_not_acquire_lock(patched_deps):
    finalize_metadata("demo", language="python", dry_run=True)
    assert _FakeLock.instances == []  # never constructed


def test_dry_run_sets_flags_false(patched_deps):
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert rpt.wrote_fingerprint is False
    assert rpt.cleared_run_report is False
    assert rpt.dry_run is True


def test_dry_run_is_deterministic(patched_deps):
    r1 = finalize_metadata("demo", language="python", dry_run=True)
    r2 = finalize_metadata("demo", language="python", dry_run=True)
    assert r1.basename == r2.basename
    assert r1.language == r2.language
    assert r1.files_present == r2.files_present
    assert r1.fingerprint_state == r2.fingerprint_state
    assert r1.run_report_state == r2.run_report_state
    assert r1.stale_components == r2.stale_components


# ---------------------------------------------------------------------------
# 11. dry_run=False semantics
# ---------------------------------------------------------------------------
def test_non_dry_run_acquires_lock(patched_deps):
    finalize_metadata("demo", language="python", dry_run=False)
    assert len(_FakeLock.instances) == 1
    lock = _FakeLock.instances[0]
    assert lock.basename == "demo"
    assert lock.language == "python"
    assert lock.entered is True
    assert lock.exited is True


def test_non_dry_run_writes_fingerprint(patched_deps):
    rpt = finalize_metadata("demo", language="python", dry_run=False)
    patched_deps["save_fingerprint"].assert_called_once()
    _args, kwargs = patched_deps["save_fingerprint"].call_args
    assert kwargs["basename"] == "demo"
    assert kwargs["language"] == "python"
    assert kwargs["operation"] == "metadata-finalize"
    assert kwargs["paths"] == patched_deps["paths"]
    assert rpt.wrote_fingerprint is True


def test_non_dry_run_clears_run_report_when_stale(patched_deps):
    patched_deps["read_fingerprint"].return_value = _FakeFingerprint(
        prompt_hash="OLD",  # stale prompt
        code_hash="CH",
        example_hash="EH",
        test_hash="TH",
        test_files={"test_demo.py": "TH"},
    )
    patched_deps["read_run_report"].return_value = _FakeRunReport(
        test_hash="TH", test_files={"test_demo.py": "TH"}
    )
    rpt = finalize_metadata("demo", language="python", dry_run=False)
    patched_deps["clear_run_report"].assert_called_once_with("demo", "python")
    assert rpt.cleared_run_report is True


def test_non_dry_run_does_not_clear_when_not_stale(patched_deps):
    patched_deps["read_fingerprint"].return_value = _FakeFingerprint(
        prompt_hash="PH",
        code_hash="CH",
        example_hash="EH",
        test_hash="TH",
        test_files={"test_demo.py": "TH"},
    )
    patched_deps["read_run_report"].return_value = _FakeRunReport(
        test_hash="TH", test_files={"test_demo.py": "TH"}
    )
    rpt = finalize_metadata("demo", language="python", dry_run=False)
    patched_deps["clear_run_report"].assert_not_called()
    assert rpt.cleared_run_report is False


def test_non_dry_run_skips_write_when_prompt_missing(patched_deps):
    patched_deps["paths"]["prompt"].unlink()
    rpt = finalize_metadata("demo", language="python", dry_run=False)
    patched_deps["save_fingerprint"].assert_not_called()
    assert rpt.wrote_fingerprint is False
    assert any(
        "prompt" in w.lower() and "skip" in w.lower() for w in rpt.warnings
    )


# ---------------------------------------------------------------------------
# 12. Error handling
# ---------------------------------------------------------------------------
def test_empty_target_raises_value_error(patched_deps):
    with pytest.raises(ValueError):
        finalize_metadata("", dry_run=True)


def test_get_pdd_file_paths_failure_raises_value_error(patched_deps):
    patched_deps["get_pdd_file_paths"].side_effect = RuntimeError("boom")
    with pytest.raises(ValueError):
        finalize_metadata("demo", language="python", dry_run=True)


def test_lock_acquisition_error_propagates(patched_deps, monkeypatch):
    class _BoomLock:
        def __init__(self, basename, language):
            pass

        def __enter__(self):
            raise TimeoutError("locked by another process")

        def __exit__(self, exc_type, exc_val, exc_tb):
            pass

    import pdd.sync_determine_operation as sdo
    monkeypatch.setattr(sdo, "SyncLock", _BoomLock)
    with pytest.raises(TimeoutError):
        finalize_metadata("demo", language="python", dry_run=False)


def test_unreadable_run_report_recorded_as_warning(patched_deps):
    patched_deps["read_run_report"].side_effect = ValueError("bad json")
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert any("run report" in w.lower() for w in rpt.warnings)


def test_per_file_hash_error_does_not_abort(patched_deps):
    patched_deps["calculate_current_hashes"].side_effect = RuntimeError("hash fail")
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert any("hash" in w.lower() for w in rpt.warnings)


# ---------------------------------------------------------------------------
# 13. include_deps forwarded
# ---------------------------------------------------------------------------
def test_include_deps_forwarded_to_calculate_current_hashes(patched_deps):
    patched_deps["read_fingerprint"].return_value = _FakeFingerprint(
        include_deps={"some/file.prompt": "DEPHASH"},
    )
    finalize_metadata("demo", language="python", dry_run=True)
    handle = patched_deps["calculate_current_hashes"]
    _args, kwargs = handle.call_args
    assert kwargs.get("stored_include_deps") == {"some/file.prompt": "DEPHASH"}


# ---------------------------------------------------------------------------
# 14. Regression: skip: supersedes missing
# ---------------------------------------------------------------------------
def test_regression_skip_supersedes_missing_run_report(patched_deps):
    """If we ever revert the order, this test fails."""
    patched_deps["read_fingerprint"].return_value = _FakeFingerprint(
        command="skip:verify",
        prompt_hash="PH",
        code_hash="CH",
        example_hash="EH",
        test_hash="TH",
        test_files={"test_demo.py": "TH"},
    )
    patched_deps["read_run_report"].return_value = None  # missing
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    assert rpt.run_report_state == "skipped"


# ---------------------------------------------------------------------------
# 15. Regression: dry_run never touches the lock file
# ---------------------------------------------------------------------------
def test_regression_dry_run_does_not_construct_synclock(patched_deps):
    """SyncLock should not be invoked at all when dry_run=True."""
    finalize_metadata("demo", language="python", dry_run=True)
    assert _FakeLock.instances == []


# ---------------------------------------------------------------------------
# 16. paths field stringified for JSON-friendliness
# ---------------------------------------------------------------------------
def test_paths_in_report_are_strings_for_path_values(patched_deps):
    rpt = finalize_metadata("demo", language="python", dry_run=True)
    # Path objects from get_pdd_file_paths are coerced to str so the report
    # can be serialized.
    assert isinstance(rpt.paths["code"], str)
    assert rpt.paths["code"].endswith("demo.py")
