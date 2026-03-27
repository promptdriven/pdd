"""
E2E tests for Issue #437: Fingerprint metadata files have null hash fields
after successful generate/example commands.

Bug: The @log_operation decorator at pdd/operation_log.py:374 calls
save_fingerprint() without the required 'paths' parameter, causing
calculate_current_hashes() to return an empty dict and all hash fields
(prompt_hash, code_hash, example_hash, test_hash) to be null.

The sync command is unaffected because it uses a separate code path
(_save_fingerprint_atomic) that correctly passes the paths dictionary.

Issue: https://github.com/promptdriven/pdd/issues/437
"""

import json
import os
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock

from pdd import operation_log


# ---- Fixtures ----

@pytest.fixture
def temp_pdd_env(tmp_path):
    """
    Sets up a temporary PDD_DIR and META_DIR for file operations.
    Patches the module-level constants to use this temp path.
    """
    pdd_dir = tmp_path / ".pdd"
    meta_dir = pdd_dir / "meta"

    with patch("pdd.operation_log.PDD_DIR", str(pdd_dir)), \
         patch("pdd.operation_log.META_DIR", str(meta_dir)):
        yield meta_dir


@pytest.fixture
def project_with_files(tmp_path):
    """
    Creates a realistic project directory with prompt, code, example, and test files.
    Returns (tmp_path, paths_dict, basename, language).
    """
    prompts_dir = tmp_path / "prompts"
    src_dir = tmp_path / "src"
    examples_dir = tmp_path / "examples"
    tests_dir = tmp_path / "tests"

    for d in [prompts_dir, src_dir, examples_dir, tests_dir]:
        d.mkdir(parents=True)

    basename = "widget"
    language = "python"

    prompt_file = prompts_dir / f"{basename}_{language}.prompt"
    prompt_file.write_text("% Widget Module\nCreate a widget class.\n")

    code_file = src_dir / f"{basename}.py"
    code_file.write_text("class Widget:\n    def render(self): pass\n")

    example_file = examples_dir / f"{basename}_example.py"
    example_file.write_text("from src.widget import Widget\nWidget().render()\n")

    test_file = tests_dir / f"test_{basename}.py"
    test_file.write_text("def test_widget(): assert True\n")

    paths = {
        "prompt": prompt_file,
        "code": code_file,
        "example": example_file,
        "test": test_file,
    }

    return tmp_path, paths, basename, language


# ---- Tests ----


def test_decorator_calls_save_fingerprint_with_paths(temp_pdd_env):
    """
    Issue #437: The @log_operation decorator calls save_fingerprint() without
    the 'paths' parameter, resulting in null hash fields.

    This test mocks save_fingerprint and verifies that when the decorator
    invokes it, 'paths' is present and non-None in the call arguments.
    On buggy code, 'paths' is missing entirely from the kwargs.
    """
    @operation_log.log_operation(
        operation="generate",
        updates_fingerprint=True
    )
    def mock_generate(prompt_file: str):
        return ("Generated successfully", 0.10, "gpt-4")

    with patch("pdd.operation_log.save_fingerprint") as mock_save_fp:
        mock_generate(prompt_file="prompts/widget_python.prompt")

        # Verify save_fingerprint was called
        assert mock_save_fp.called, (
            "save_fingerprint should be called when updates_fingerprint=True"
        )

        # THE BUG: The decorator does NOT pass 'paths' to save_fingerprint.
        # Current call: save_fingerprint(basename, language, operation=..., cost=..., model=...)
        # After fix: save_fingerprint(basename, language, operation=..., paths=<dict>, cost=..., model=...)
        call_kwargs = mock_save_fp.call_args.kwargs

        assert "paths" in call_kwargs, (
            "Bug #437: save_fingerprint called without 'paths' keyword argument. "
            "The decorator must pass the paths dict so content hashes can be calculated. "
            f"Actual kwargs: {call_kwargs}"
        )
        assert call_kwargs["paths"] is not None, (
            "Bug #437: save_fingerprint called with paths=None. "
            "The decorator must pass a valid paths dict."
        )


def test_decorator_produces_non_null_hashes_in_fingerprint(temp_pdd_env, project_with_files):
    """
    Issue #437: After a successful generate command via the decorator, the
    fingerprint metadata file must contain actual SHA-256 hashes, not null.

    This test creates real files, runs a decorated function, and inspects
    the resulting fingerprint JSON to verify prompt_hash and code_hash are populated.
    On buggy code, all hashes are null because paths is never passed to save_fingerprint.
    """
    tmp_path, paths, basename, language = project_with_files

    @operation_log.log_operation(
        operation="generate",
        updates_fingerprint=True
    )
    def mock_generate(prompt_file: str):
        return ("Generated successfully", 0.10, "gpt-4")

    prompt_path = f"prompts/{basename}_{language}.prompt"

    # Patch get_pdd_file_paths at the source module so the fix can find it.
    # On buggy code, the decorator never calls get_pdd_file_paths, so this mock
    # is irrelevant and hashes stay null. After the fix, the decorator calls it,
    # gets our real paths, and calculate_current_hashes computes actual hashes.
    with patch(
        "pdd.sync_determine_operation.get_pdd_file_paths", return_value=paths
    ):
        mock_generate(prompt_file=prompt_path)

    # Read the fingerprint file
    fp_path = operation_log.get_fingerprint_path(basename, language)
    assert fp_path.exists(), f"Fingerprint file should exist at {fp_path}"

    with open(fp_path) as f:
        fp_data = json.load(f)

    # THE BUG: All hash fields are null because paths was not passed.
    # After the fix, at least prompt_hash and code_hash should be valid SHA-256.
    assert fp_data["prompt_hash"] is not None, (
        f"Bug #437: prompt_hash is null in fingerprint. "
        f"Full data: {json.dumps(fp_data, indent=2)}"
    )
    assert fp_data["code_hash"] is not None, (
        f"Bug #437: code_hash is null in fingerprint. "
        f"Full data: {json.dumps(fp_data, indent=2)}"
    )

    # Validate hash format: SHA-256 = 64 hex characters
    for field in ["prompt_hash", "code_hash"]:
        val = fp_data[field]
        assert isinstance(val, str) and len(val) == 64, (
            f"{field} should be a 64-char hex SHA-256 hash, got: {val}"
        )
        assert all(c in "0123456789abcdef" for c in val), (
            f"{field} should be hexadecimal, got: {val}"
        )


def test_decorator_passes_paths_to_save_fingerprint(temp_pdd_env):
    """
    Issue #437: Verify the decorator constructs a paths dict and passes it
    to save_fingerprint().

    The decorator has basename and language (inferred from prompt_file).
    The fix should use get_pdd_file_paths(basename, language) to build paths,
    then pass them to save_fingerprint(). On buggy code, paths is absent.
    """
    sentinel_paths = {"prompt": Path("/fake/prompt.prompt"), "code": Path("/fake/code.py")}

    @operation_log.log_operation(
        operation="generate",
        updates_fingerprint=True
    )
    def mock_generate(prompt_file: str):
        return ("Generated", 0.05, "gpt-4")

    with patch("pdd.operation_log.save_fingerprint") as mock_save_fp, \
         patch(
             "pdd.sync_determine_operation.get_pdd_file_paths",
             return_value=sentinel_paths,
         ) as mock_get_paths:
        mock_generate(prompt_file="prompts/mymod_python.prompt")

        # Verify save_fingerprint was called
        assert mock_save_fp.called, "save_fingerprint should be called"

        # Verify save_fingerprint received the paths
        call_kwargs = mock_save_fp.call_args.kwargs
        paths_value = call_kwargs.get("paths")
        assert paths_value is not None, (
            "Bug #437: save_fingerprint was not passed a 'paths' argument. "
            f"Actual kwargs: {call_kwargs}"
        )

        # Verify the paths dict has the expected structure (dict with Path values)
        assert isinstance(paths_value, dict), (
            f"paths should be a dict, got {type(paths_value)}"
        )


def test_decorator_fingerprint_all_four_hash_fields(temp_pdd_env, project_with_files):
    """
    Issue #437: Verify that ALL four hash fields (prompt_hash, code_hash,
    example_hash, test_hash) are populated when corresponding files exist.

    The issue reports all four fields as null. This test confirms the
    complete set is populated after the fix.
    """
    tmp_path, paths, basename, language = project_with_files

    @operation_log.log_operation(
        operation="generate",
        updates_fingerprint=True
    )
    def mock_generate(prompt_file: str):
        return ("Generated", 0.10, "gpt-4")

    prompt_path = f"prompts/{basename}_{language}.prompt"

    with patch(
        "pdd.sync_determine_operation.get_pdd_file_paths", return_value=paths
    ):
        mock_generate(prompt_file=prompt_path)

    fp_path = operation_log.get_fingerprint_path(basename, language)
    with open(fp_path) as f:
        fp_data = json.load(f)

    # All four hash fields should be non-null since all files exist
    null_fields = [
        field for field in ["prompt_hash", "code_hash", "example_hash", "test_hash"]
        if fp_data.get(field) is None
    ]

    assert not null_fields, (
        f"Bug #437: The following hash fields are null: {null_fields}. "
        f"All should contain SHA-256 hashes when files exist. "
        f"Full fingerprint: {json.dumps(fp_data, indent=2)}"
    )

    # Verify metadata fields are also correct
    assert fp_data["command"] == "generate"
    assert "pdd_version" in fp_data
    assert "timestamp" in fp_data


def test_decorator_no_fingerprint_when_identity_unknown(temp_pdd_env):
    """
    Edge case: When the decorator cannot infer basename/language (no prompt_file
    argument), it should not attempt to save a fingerprint at all. This test
    ensures the fix doesn't break commands that don't provide identity info.
    """
    @operation_log.log_operation(
        operation="some_cmd",
        updates_fingerprint=True
    )
    def cmd_without_prompt(other_arg: str):
        return ("Done", 0.0, "model")

    with patch("pdd.operation_log.save_fingerprint") as mock_save_fp:
        cmd_without_prompt(other_arg="something")

        # When identity can't be inferred, save_fingerprint should NOT be called
        mock_save_fp.assert_not_called()

    # No meta directory should have been created
    assert not os.path.exists(temp_pdd_env)
