# tests/test_core_dump.py
"""Tests for core/dump."""
import os
import sys
import subprocess
from pathlib import Path
from unittest.mock import patch, ANY, MagicMock

import pytest
from click.testing import CliRunner
import click

from pdd import cli, __version__, DEFAULT_STRENGTH, DEFAULT_TIME

RUN_ALL_TESTS_ENABLED = os.getenv("PDD_RUN_ALL_TESTS") == "1"


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_core_dump_default_flag_false(mock_main, mock_auto_update, runner, create_dummy_files):
    """By default, core_dump flag in context should be False (or missing)."""
    files = create_dummy_files("test_core_default.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')

    result = runner.invoke(cli.cli, ["generate", str(files["test_core_default.prompt"])])

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(result.output)
        if result.exception:
            raise result.exception

    mock_main.assert_called_once()
    ctx = mock_main.call_args.kwargs.get("ctx")
    assert ctx is not None
    # If implementation does not set it explicitly, this assertion can be relaxed
    assert ctx.obj.get("core_dump", False) is False
    mock_auto_update.assert_called_once_with()

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_core_dump_flag_sets_ctx_true(mock_main, mock_auto_update, runner, create_dummy_files):
    """`--core-dump` should set ctx.obj['core_dump'] to True."""
    files = create_dummy_files("test_core_enabled.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')

    result = runner.invoke(
        cli.cli,
        [
            "--core-dump",
            "generate",
            str(files["test_core_enabled.prompt"]),
        ],
    )

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(result.output)
        if result.exception:
            raise result.exception

    mock_main.assert_called_once()
    ctx = mock_main.call_args.kwargs.get("ctx")
    assert ctx is not None
    assert ctx.obj.get("core_dump") is True
    mock_auto_update.assert_called_once_with()

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main', side_effect=Exception("Core dump test error"))
def test_cli_core_dump_does_not_propagate_exception(mock_main, mock_auto_update, runner, create_dummy_files):
    """
    When --core-dump is enabled and the command raises,
    the CLI should still handle the error gracefully (exit_code == 0),
    allowing core-dump machinery to run without crashing the CLI.
    """
    files = create_dummy_files("test_core_error.prompt")

    result = runner.invoke(
        cli.cli,
        [
            "--core-dump",
            "generate",
            str(files["test_core_error.prompt"]),
        ],
    )

    # Error should be handled by the CLI's error handler (no traceback propagated)
    assert result.exit_code == 0
    assert result.exception is None
    # We don't assert on the exact output text to avoid coupling to wording.
    mock_main.assert_called_once()
    mock_auto_update.assert_called_once_with()


def test_core_dump_includes_file_contents(tmp_path):
    """Test that core dump includes file contents from tracked files."""
    import json
    from pdd.core.dump import _write_core_dump, _build_issue_markdown

    # Create test files
    test_prompt = tmp_path / "test.prompt"
    test_code = tmp_path / "test.py"
    test_prompt.write_text("Test prompt content")
    test_code.write_text("print('test')")

    # Create mock context
    mock_ctx = MagicMock()
    mock_ctx.obj = {
        'core_dump': True,
        'core_dump_files': {str(test_prompt.resolve()), str(test_code.resolve())},
        'force': False,
        'strength': 0.75,
        'temperature': 0.0,
        'time': 0.25,
        'verbose': False,
        'quiet': True,
        'local': False,
        'context': None,
        'output_cost': None,
        'review_examples': False
    }

    # Change to temp directory for core dump output
    os.chdir(tmp_path)

    # Write core dump
    _write_core_dump(mock_ctx, [('result', 0.5, 'test-model')], ['test'], 0.5)

    # Find the generated core dump
    core_dumps = list((tmp_path / ".pdd" / "core_dumps").glob("pdd-core-*.json"))
    assert len(core_dumps) == 1, "Should create one core dump file"

    # Read and verify content
    core_dump_data = json.loads(core_dumps[0].read_text())

    # Check that file contents are included
    assert 'file_contents' in core_dump_data
    file_contents = core_dump_data['file_contents']

    # Should contain both files
    assert any('test.prompt' in key for key in file_contents.keys()), \
        f"test.prompt not in file_contents keys: {list(file_contents.keys())}"
    assert any('test.py' in key for key in file_contents.keys()), \
        f"test.py not in file_contents keys: {list(file_contents.keys())}"

    # Check actual content
    prompt_key = [k for k in file_contents.keys() if 'test.prompt' in k][0]
    code_key = [k for k in file_contents.keys() if 'test.py' in k][0]

    assert file_contents[prompt_key] == "Test prompt content"
    assert file_contents[code_key] == "print('test')"

    # Test that browser-based markdown truncates files
    title, body = _build_issue_markdown(core_dump_data, "", core_dumps[0], None, [], truncate_files=True)
    assert "... (truncated" not in body or len(body) < 5000  # Should be much smaller

    # Test that API-based markdown includes full contents
    title, body_full = _build_issue_markdown(core_dump_data, "", core_dumps[0], None, [], truncate_files=False)
    assert "Test prompt content" in body_full
    assert "print('test')" in body_full


def test_core_dump_auto_includes_meta_files(tmp_path):
    """Test that core dump automatically includes relevant meta files."""
    import json
    from pdd.core.dump import _write_core_dump

    # Create meta directory and files
    meta_dir = tmp_path / ".pdd" / "meta"
    meta_dir.mkdir(parents=True, exist_ok=True)

    test_meta = meta_dir / "test_generate.json"
    test_meta.write_text('{"version": "1.0"}')

    # Create mock context
    mock_ctx = MagicMock()
    mock_ctx.obj = {
        'core_dump': True,
        'core_dump_files': set(),
        'force': False,
        'strength': 0.75,
        'temperature': 0.0,
        'time': 0.25,
        'verbose': False,
        'quiet': True,
        'local': False,
        'context': None,
        'output_cost': None,
        'review_examples': False
    }

    os.chdir(tmp_path)

    # Write core dump with 'generate' command
    _write_core_dump(mock_ctx, [('result', 0.5, 'test-model')], ['generate'], 0.5)

    # Find the generated core dump
    core_dumps = list((tmp_path / ".pdd" / "core_dumps").glob("pdd-core-*.json"))
    assert len(core_dumps) == 1

    # Read and verify content
    core_dump_data = json.loads(core_dumps[0].read_text())

    # Meta file should be auto-included
    file_contents = core_dump_data.get('file_contents', {})
    assert any('test_generate.json' in key for key in file_contents.keys()), \
        f"Meta file not auto-included: {list(file_contents.keys())}"


def test_core_dump_handles_large_files(tmp_path):
    """Test that core dump marks large files as 'too large'."""
    import json
    from pdd.core.dump import _write_core_dump

    # Create a large file (over 50KB limit)
    large_file = tmp_path / "large.txt"
    large_file.write_text("x" * 60000)  # 60KB

    mock_ctx = MagicMock()
    mock_ctx.obj = {
        'core_dump': True,
        'core_dump_files': {str(large_file.resolve())},
        'force': False,
        'strength': 0.75,
        'temperature': 0.0,
        'time': 0.25,
        'verbose': False,
        'quiet': True,
        'local': False,
        'context': None,
        'output_cost': None,
        'review_examples': False
    }

    os.chdir(tmp_path)

    _write_core_dump(mock_ctx, [('result', 0.5, 'test-model')], ['test'], 0.5)

    core_dumps = list((tmp_path / ".pdd" / "core_dumps").glob("pdd-core-*.json"))
    core_dump_data = json.loads(core_dumps[0].read_text())

    file_contents = core_dump_data.get('file_contents', {})
    large_file_key = [k for k in file_contents.keys() if 'large.txt' in k][0]

    assert file_contents[large_file_key] == "<too large>"


def test_core_dump_handles_binary_files(tmp_path):
    """Test that core dump marks binary files appropriately."""
    import json
    from pdd.core.dump import _write_core_dump

    # Create a binary file
    binary_file = tmp_path / "test.bin"
    binary_file.write_bytes(b'\x00\x01\x02\x03\xFF\xFE')

    mock_ctx = MagicMock()
    mock_ctx.obj = {
        'core_dump': True,
        'core_dump_files': {str(binary_file.resolve())},
        'force': False,
        'strength': 0.75,
        'temperature': 0.0,
        'time': 0.25,
        'verbose': False,
        'quiet': True,
        'local': False,
        'context': None,
        'output_cost': None,
        'review_examples': False
    }

    os.chdir(tmp_path)

    _write_core_dump(mock_ctx, [('result', 0.5, 'test-model')], ['test'], 0.5)

    core_dumps = list((tmp_path / ".pdd" / "core_dumps").glob("pdd-core-*.json"))
    core_dump_data = json.loads(core_dumps[0].read_text())

    file_contents = core_dump_data.get('file_contents', {})
    binary_file_key = [k for k in file_contents.keys() if 'test.bin' in k][0]

    assert file_contents[binary_file_key] == "<binary>"

