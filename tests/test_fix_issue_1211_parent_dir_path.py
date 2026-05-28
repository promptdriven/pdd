# tests/test_fix_issue_1211_parent_dir_path.py
"""
Regression tests for issue #1211:
  pdd fix from a parent dir writes orphan files to run cwd instead of the subproject.

Root cause: _extract_basename in pdd/construct_paths.py (line 845) calls
_strip_language_suffix(prompt_path) instead of _strip_language_suffix_with_subdir(prompt_path)
for the 'fix' command.  The plain variant strips only the filename stem, discarding every
intermediate directory component under prompts/.

Example (from pdd_cloud PR #1707):
  Prompt:  extensions/github_pdd_app/prompts/src/routers/webhook_handlers_Python.prompt
  Buggy:   basename = "webhook_handlers"  → output = .../webhook_handlers.py  (orphan)
  Fixed:   basename = "src/routers/webhook_handlers" → output = .../src/routers/webhook_handlers.py

Secondary expansion items (Step 6):
  • operation_log.ensure_meta_dir / get_fingerprint_path must accept project_root so that
    .pdd/meta/ entries are written under the subproject root, not the run CWD.
  • sync_determine_operation.get_meta_dir must accept project_root for the same reason.
"""

import pytest
from pathlib import Path
from unittest.mock import patch

from pdd.construct_paths import construct_paths


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_fix_input_files(tmp_path: Path, prompt_rel: str, *, with_test: bool = True):
    """Create a minimal set of files for a 'fix' command invocation.

    Returns a dict suitable for passing to construct_paths as input_file_paths.
    prompt_rel is relative to tmp_path, e.g. 'prompts/src/routers/webhook_handlers_Python.prompt'.
    """
    prompt_path = tmp_path / prompt_rel
    prompt_path.parent.mkdir(parents=True, exist_ok=True)
    prompt_path.write_text("prompt content")

    code_file = tmp_path / "webhook_handlers.py"
    code_file.write_text("def handler(): pass")

    files = {
        "prompt_file": str(prompt_path),
        "code_file": str(code_file),
    }

    if with_test:
        test_file = tmp_path / "test_webhook_handlers.py"
        test_file.write_text("def test_handler(): pass")
        files["unit_test_file"] = str(test_file)

    return files


def _call_construct_paths_fix(input_file_paths, tmp_path):
    """Call construct_paths for command='fix' with mocked dependencies.

    Returns the mock object for generate_output_paths so callers can inspect
    how it was invoked.
    """
    mock_output = {
        "output_code": str(tmp_path / "out.py"),
        "output_test": str(tmp_path / "out_test.py"),
        "output_results": str(tmp_path / "out.log"),
    }

    with patch("pdd.construct_paths.generate_output_paths", return_value=mock_output) as mock_gop, \
         patch("pdd.construct_paths._find_pddrc_file", return_value=None), \
         patch("pdd.construct_paths.get_extension", return_value=".py"), \
         patch("pdd.construct_paths.get_language", return_value="python"):
        construct_paths(
            input_file_paths,
            force=True,
            quiet=True,
            command="fix",
            command_options={},
        )
        return mock_gop


# ---------------------------------------------------------------------------
# Test 1 (primary bug): fix + nested prompt → subdir components in basename
# ---------------------------------------------------------------------------

def test_fix_nested_prompt_preserves_subdir_in_basename(tmp_path):
    """fix command with a nested prompt path must preserve subdirectory components.

    For prompts/src/routers/webhook_handlers_Python.prompt the basename passed to
    generate_output_paths must include 'src/routers/webhook_handlers', NOT the bare
    'webhook_handlers' that the buggy _strip_language_suffix variant produces.

    Fails on buggy code: _extract_basename calls _strip_language_suffix(prompt_path)
    which returns only the stem, so the basename becomes 'webhook_handlers_test_webhook_handlers'.
    Passes after fix: _strip_language_suffix_with_subdir preserves the subdir path,
    producing 'src/routers/webhook_handlers_test_webhook_handlers'.
    """
    input_file_paths = _make_fix_input_files(
        tmp_path,
        "prompts/src/routers/webhook_handlers_Python.prompt",
        with_test=True,
    )

    mock_gop = _call_construct_paths_fix(input_file_paths, tmp_path)

    mock_gop.assert_called()
    actual_basename = mock_gop.call_args.kwargs["basename"]

    assert "src/routers/webhook_handlers" in actual_basename, (
        f"Expected basename to contain 'src/routers/webhook_handlers' (subdir-preserved) "
        f"but got {actual_basename!r}. "
        "Bug: _extract_basename uses _strip_language_suffix instead of "
        "_strip_language_suffix_with_subdir for the fix command."
    )


# ---------------------------------------------------------------------------
# Test 2 (regression): fix + flat prompt still works correctly
# ---------------------------------------------------------------------------

def test_fix_flat_prompt_basename_unaffected(tmp_path):
    """fix command with a prompt directly under prompts/ still produces correct basename.

    This is a regression guard: after switching to _strip_language_suffix_with_subdir,
    flat prompts (no subdirectory under prompts/) must continue to work identically to
    the pre-fix baseline.
    """
    input_file_paths = _make_fix_input_files(
        tmp_path,
        "prompts/webhook_handlers_Python.prompt",
        with_test=True,
    )

    mock_gop = _call_construct_paths_fix(input_file_paths, tmp_path)

    mock_gop.assert_called()
    actual_basename = mock_gop.call_args.kwargs["basename"]

    # For a flat prompt there are no subdirs to preserve; the stem should appear unchanged.
    assert "webhook_handlers" in actual_basename, (
        f"Expected basename to contain 'webhook_handlers' for a flat prompt, "
        f"but got {actual_basename!r}."
    )
    # Also verify we did NOT accidentally add spurious path components.
    assert "/" not in actual_basename.split("_test_")[0], (
        f"Flat prompt should produce a basename without slashes, got {actual_basename!r}."
    )


# ---------------------------------------------------------------------------
# Test 3: Multi-level nesting preserves all directory levels
# ---------------------------------------------------------------------------

def test_fix_multi_level_nested_prompt_preserves_all_subdirs(tmp_path):
    """fix command with deeply nested prompt preserves every subdirectory level.

    Uses the real-world path from pdd_cloud PR #1707:
      prompts/src/services/solving_orchestrator/budget_Python.prompt
    The basename must include 'src/services/solving_orchestrator/budget'.

    Fails on buggy code because _strip_language_suffix returns only 'budget'.
    """
    code_file = tmp_path / "budget.py"
    code_file.write_text("x = 1")
    test_file = tmp_path / "test_budget.py"
    test_file.write_text("def test_budget(): pass")

    prompt_dir = tmp_path / "prompts" / "src" / "services" / "solving_orchestrator"
    prompt_dir.mkdir(parents=True)
    prompt_file = prompt_dir / "budget_Python.prompt"
    prompt_file.write_text("prompt content")

    input_file_paths = {
        "prompt_file": str(prompt_file),
        "code_file": str(code_file),
        "unit_test_file": str(test_file),
    }

    mock_output = {
        "output_code": str(tmp_path / "out.py"),
        "output_test": str(tmp_path / "out_test.py"),
        "output_results": str(tmp_path / "out.log"),
    }

    with patch("pdd.construct_paths.generate_output_paths", return_value=mock_output) as mock_gop, \
         patch("pdd.construct_paths._find_pddrc_file", return_value=None), \
         patch("pdd.construct_paths.get_extension", return_value=".py"), \
         patch("pdd.construct_paths.get_language", return_value="python"):
        construct_paths(
            input_file_paths,
            force=True,
            quiet=True,
            command="fix",
            command_options={},
        )

    mock_gop.assert_called()
    actual_basename = mock_gop.call_args.kwargs["basename"]

    assert "src/services/solving_orchestrator/budget" in actual_basename, (
        f"Expected basename to contain 'src/services/solving_orchestrator/budget' "
        f"but got {actual_basename!r}. "
        "All subdirectory levels must be preserved for multi-level nesting."
    )


# ---------------------------------------------------------------------------
# Test 4: Fallback branch (no unit_test_file) also uses subdir-aware variant
# ---------------------------------------------------------------------------

def test_fix_nested_prompt_no_unit_test_file_preserves_subdir(tmp_path):
    """fix command fallback branch (no unit_test_file) still uses subdir-aware basename.

    When no unit_test_file is provided, _extract_basename for 'fix' falls back to
    returning prompt_basename directly (line 851).  This path also uses _strip_language_suffix
    on buggy code, so it must be fixed too.

    Fails on buggy code: returns only 'webhook_handlers' (no subdir).
    Passes after fix: returns 'src/routers/webhook_handlers' (subdir preserved).
    """
    input_file_paths = _make_fix_input_files(
        tmp_path,
        "prompts/src/routers/webhook_handlers_Python.prompt",
        with_test=False,  # Triggers the fallback branch in _extract_basename
    )
    # Remove unit_test_file key to be explicit
    input_file_paths.pop("unit_test_file", None)

    mock_gop = _call_construct_paths_fix(input_file_paths, tmp_path)

    mock_gop.assert_called()
    actual_basename = mock_gop.call_args.kwargs["basename"]

    assert "src/routers/webhook_handlers" in actual_basename, (
        f"Expected basename to contain 'src/routers/webhook_handlers' even without "
        f"unit_test_file, but got {actual_basename!r}. "
        "The fallback branch of _extract_basename for 'fix' has the same bug."
    )


# ---------------------------------------------------------------------------
# Test 5 (expansion item): ensure_meta_dir must accept project_root
# Scope addition: covers expansion item "Meta path anchored to run CWD in
# operation_log.py (META_DIR/ensure_meta_dir at lines 20-25)" identified by
# Step 6 but absent from Step 8's plan.
# ---------------------------------------------------------------------------

def test_ensure_meta_dir_accepts_project_root_and_creates_under_it(tmp_path, monkeypatch):
    """ensure_meta_dir must create .pdd/meta under the specified project_root, not the CWD.

    The expansion item from Step 6 notes that ensure_meta_dir always creates
    .pdd/meta/ relative to the run CWD.  After the fix, calling
    ensure_meta_dir(project_root=subproject) must create
    <subproject>/.pdd/meta/, NOT <cwd>/.pdd/meta/.

    Fails on buggy code: ensure_meta_dir() accepts no arguments → TypeError.
    Passes after fix: directory created under the supplied project_root.
    """
    subproject = tmp_path / "extensions" / "github_pdd_app"
    subproject.mkdir(parents=True)

    cwd_dir = tmp_path / "parent_cwd"
    cwd_dir.mkdir()
    monkeypatch.chdir(cwd_dir)

    from pdd.operation_log import ensure_meta_dir

    # On buggy code this raises TypeError: unexpected keyword argument 'project_root'
    ensure_meta_dir(project_root=subproject)

    expected_meta_dir = subproject / ".pdd" / "meta"
    assert expected_meta_dir.exists(), (
        f"Expected .pdd/meta to be created under subproject at {expected_meta_dir}, "
        "but it was not found. "
        "Bug: ensure_meta_dir does not accept project_root; it always creates "
        ".pdd/meta relative to the run CWD."
    )


# ---------------------------------------------------------------------------
# Test 6 (expansion item): get_fingerprint_path must accept project_root
# ---------------------------------------------------------------------------

def test_get_fingerprint_path_returns_path_under_project_root(tmp_path, monkeypatch):
    """get_fingerprint_path must return a path under the specified project_root.

    For a subproject at extensions/github_pdd_app, calling
    get_fingerprint_path('src/routers/webhook_handlers', 'python', project_root=subproject)
    must return a path whose parent chain includes <subproject>/.pdd/meta/.

    Fails on buggy code: get_fingerprint_path() does not accept project_root → TypeError.
    Passes after fix: returned path is rooted at <project_root>/.pdd/meta/.
    """
    subproject = tmp_path / "extensions" / "github_pdd_app"
    subproject.mkdir(parents=True)

    cwd_dir = tmp_path / "parent_cwd"
    cwd_dir.mkdir()
    monkeypatch.chdir(cwd_dir)

    from pdd.operation_log import get_fingerprint_path

    # On buggy code this raises TypeError: unexpected keyword argument 'project_root'
    result = get_fingerprint_path(
        "src/routers/webhook_handlers", "python", project_root=subproject
    )

    expected_meta_dir = subproject / ".pdd" / "meta"
    assert str(result).startswith(str(expected_meta_dir)), (
        f"Expected fingerprint path to start with {expected_meta_dir}, "
        f"but got {result}. "
        "Bug: get_fingerprint_path does not accept project_root; it always "
        "returns a path relative to the run CWD."
    )


# ---------------------------------------------------------------------------
# Test 7 (expansion item): sync_determine_operation.get_meta_dir must accept
# project_root so that sync's meta-path logic is rooted at the subproject.
# ---------------------------------------------------------------------------

def test_sync_get_meta_dir_accepts_project_root(tmp_path, monkeypatch):
    """sync_determine_operation.get_meta_dir must return a path under project_root.

    The expansion item from Step 6 notes that get_meta_dir (lines 57-59 in
    sync_determine_operation.py) returns Path.cwd() / '.pdd' / 'meta', which
    anchors meta files to the run CWD even when the prompt lives in a subproject.

    Fails on buggy code: get_meta_dir() accepts no arguments → TypeError.
    Passes after fix: returns <project_root>/.pdd/meta.
    """
    subproject = tmp_path / "extensions" / "github_pdd_app"
    subproject.mkdir(parents=True)

    cwd_dir = tmp_path / "parent_cwd"
    cwd_dir.mkdir()
    monkeypatch.chdir(cwd_dir)

    from pdd.sync_determine_operation import get_meta_dir

    # On buggy code this raises TypeError: unexpected keyword argument 'project_root'
    result = get_meta_dir(project_root=subproject)

    expected = subproject / ".pdd" / "meta"
    assert result == expected, (
        f"Expected get_meta_dir(project_root=subproject) to return {expected}, "
        f"but got {result}. "
        "Bug: get_meta_dir ignores project_root and always returns CWD/.pdd/meta."
    )
