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
from pdd.core.cli import cli as cli_command, process_commands

RUN_ALL_TESTS_ENABLED = os.getenv("PDD_RUN_ALL_TESTS") == "1"


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


def test_core_dump_includes_file_contents(tmp_path, monkeypatch):
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

    # Change to temp directory for core dump output (auto-restored by monkeypatch)
    monkeypatch.chdir(tmp_path)

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
    # For browser-based submission, verify files are truncated
    # The body should be reasonably sized (not include full raw JSON, etc.)
    assert len(body) < 5000, f"Browser-based body should be truncated, but was {len(body)} chars"

    # Test that API-based markdown includes full contents
    title, body_full = _build_issue_markdown(core_dump_data, "", core_dumps[0], None, [], truncate_files=False)
    assert "Test prompt content" in body_full
    assert "print('test')" in body_full


def test_core_dump_auto_includes_meta_files(tmp_path, monkeypatch):
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

    monkeypatch.chdir(tmp_path)

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


def test_core_dump_handles_large_files(tmp_path, monkeypatch):
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

    monkeypatch.chdir(tmp_path)

    _write_core_dump(mock_ctx, [('result', 0.5, 'test-model')], ['test'], 0.5)

    core_dumps = list((tmp_path / ".pdd" / "core_dumps").glob("pdd-core-*.json"))
    core_dump_data = json.loads(core_dumps[0].read_text())

    file_contents = core_dump_data.get('file_contents', {})
    large_file_key = [k for k in file_contents.keys() if 'large.txt' in k][0]

    assert file_contents[large_file_key] == "<too large>"


def test_core_dump_handles_binary_files(tmp_path, monkeypatch):
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

    monkeypatch.chdir(tmp_path)

    _write_core_dump(mock_ctx, [('result', 0.5, 'test-model')], ['test'], 0.5)

    core_dumps = list((tmp_path / ".pdd" / "core_dumps").glob("pdd-core-*.json"))
    core_dump_data = json.loads(core_dumps[0].read_text())

    file_contents = core_dump_data.get('file_contents', {})
    binary_file_key = [k for k in file_contents.keys() if 'test.bin' in k][0]

    assert file_contents[binary_file_key] == "<binary>"


def test_terminal_output_captured_in_core_dump(tmp_path, monkeypatch):
    """Test that terminal output (stdout/stderr) is captured and included in core dump."""
    import json
    from pdd.core.dump import _write_core_dump
    from pdd.core.cli import OutputCapture
    import sys

    # Create mock context with output capture
    mock_ctx = MagicMock()

    # Set up output capture similar to how the CLI does it
    original_stdout = sys.stdout
    original_stderr = sys.stderr

    stdout_capture = OutputCapture(original_stdout)
    stderr_capture = OutputCapture(original_stderr)

    # Write some test output to the captures
    stdout_capture.write("Test stdout output\n")
    stdout_capture.write("More stdout\n")
    stderr_capture.write("Test stderr output\n")

    # Prepare terminal output string like the CLI does
    captured_parts = []
    stdout_text = stdout_capture.get_captured_output()
    if stdout_text:
        captured_parts.append(f"=== STDOUT ===\n{stdout_text}")
    stderr_text = stderr_capture.get_captured_output()
    if stderr_text:
        captured_parts.append(f"=== STDERR ===\n{stderr_text}")
    terminal_output = "\n\n".join(captured_parts)

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

    monkeypatch.chdir(tmp_path)

    # Write core dump with terminal output
    _write_core_dump(mock_ctx, [('result', 0.5, 'test-model')], ['test'], 0.5, terminal_output)

    # Find the generated core dump
    core_dumps = list((tmp_path / ".pdd" / "core_dumps").glob("pdd-core-*.json"))
    assert len(core_dumps) == 1

    # Read and verify content
    core_dump_data = json.loads(core_dumps[0].read_text())

    # Check that terminal output is included
    assert 'terminal_output' in core_dump_data
    captured_output = core_dump_data['terminal_output']

    assert "=== STDOUT ===" in captured_output
    assert "Test stdout output" in captured_output
    assert "More stdout" in captured_output
    assert "=== STDERR ===" in captured_output
    assert "Test stderr output" in captured_output


def test_terminal_output_included_in_gist(tmp_path):
    """Test that terminal output is added as a separate file in GitHub gist."""
    import json
    from pdd.core.dump import _create_gist_with_files
    from unittest.mock import patch, MagicMock

    # Create a payload with terminal output
    payload = {
        "schema_version": 1,
        "pdd_version": "1.0.0",
        "timestamp_utc": "20231201T120000Z",
        "terminal_output": "Test terminal output\nLine 2\nLine 3",
        "file_contents": {
            "test.py": "print('hello')"
        }
    }

    core_path = tmp_path / "test-core.json"
    core_path.write_text(json.dumps(payload))

    # Mock the requests.post call
    with patch('pdd.core.dump.requests.post') as mock_post:
        mock_response = MagicMock()
        mock_response.status_code = 201
        mock_response.json.return_value = {"html_url": "https://gist.github.com/test123"}
        mock_post.return_value = mock_response

        # Call the function
        gist_url = _create_gist_with_files("test_token", payload, core_path)

        # Verify gist was created
        assert gist_url == "https://gist.github.com/test123"

        # Verify the POST request
        mock_post.assert_called_once()
        call_kwargs = mock_post.call_args.kwargs
        gist_data = call_kwargs['json']

        # Check that terminal_output.txt is in the gist files
        assert 'terminal_output.txt' in gist_data['files']
        assert gist_data['files']['terminal_output.txt']['content'] == "Test terminal output\nLine 2\nLine 3"

        # Check other expected files
        assert 'core-dump.json' in gist_data['files']


def test_terminal_output_in_issue_markdown(tmp_path):
    """Test that terminal output is included in the issue markdown."""
    from pdd.core.dump import _build_issue_markdown

    payload = {
        "schema_version": 1,
        "pdd_version": "1.0.0",
        "timestamp_utc": "20231201T120000Z",
        "argv": ["generate", "test.prompt"],
        "cwd": str(tmp_path),
        "platform": {"system": "Linux", "release": "5.10", "python": "3.9.0"},
        "invoked_subcommands": ["generate"],
        "total_cost": 0.5,
        "steps": [],
        "errors": [],
        "environment": {},
        "file_contents": {},
        "terminal_output": "=== STDOUT ===\nGenerating code...\nDone!\n\n=== STDERR ===\nWarning: something happened"
    }

    core_path = tmp_path / "test-core.json"

    # Test without gist (full output)
    title, body = _build_issue_markdown(payload, "Test description", core_path, None, [], truncate_files=False)

    assert "## Terminal Output" in body
    assert "=== STDOUT ===" in body
    assert "Generating code..." in body
    assert "=== STDERR ===" in body
    assert "Warning: something happened" in body

    # Test with gist (link to gist)
    title, body_gist = _build_issue_markdown(
        payload, "Test description", core_path, None, [],
        truncate_files=False, gist_url="https://gist.github.com/test123"
    )

    assert "## Terminal Output" in body_gist
    assert "https://gist.github.com/test123" in body_gist
    assert "terminal_output.txt" in body_gist

    # Test with truncation (for browser mode)
    title, body_truncated = _build_issue_markdown(payload, "Test description", core_path, None, [], truncate_files=True)

    assert "## Terminal Output" in body_truncated
    # Should show truncated output
    assert "=== STDOUT ===" in body_truncated


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main', side_effect=KeyboardInterrupt())
def test_keyboard_interrupt_writes_core_dump(mock_main, mock_auto_update, tmp_path, runner, monkeypatch):
    """Test that core dump is written when KeyboardInterrupt (Ctrl+C) occurs."""
    import json

    # Create a test prompt file
    test_prompt = tmp_path / "test.prompt"
    test_prompt.write_text("Test prompt for keyboard interrupt")

    # Change to temp directory (auto-restored by monkeypatch)
    monkeypatch.chdir(tmp_path)

    # Run with --core-dump and simulate keyboard interrupt
    result = runner.invoke(
        cli.cli,
        [
            "--core-dump",
            "generate",
            str(test_prompt),
        ],
    )

    # Command should exit with error code due to interrupt
    assert result.exit_code != 0

    # But core dump should still be written
    core_dumps = list((tmp_path / ".pdd" / "core_dumps").glob("pdd-core-*.json"))
    assert len(core_dumps) >= 1, "Core dump should be created even on KeyboardInterrupt"

    # Verify core dump contains the error
    core_dump_data = json.loads(core_dumps[0].read_text())
    errors = core_dump_data.get('errors', [])

    # Should have recorded the KeyboardInterrupt
    assert len(errors) > 0, "KeyboardInterrupt should be recorded in core dump errors"
    assert any('KeyboardInterrupt' in str(err.get('type', '')) for err in errors), \
        "Error type should include KeyboardInterrupt"


def test_cli_results_none_guard_issue_253():
    """
    Regression test for Issue #253 Bug 2.

    Verifies that cli.py has the guard `results is not None` before iterating
    over results, preventing 'NoneType' object is not iterable error.
    """
    # Read cli.py and verify the guard is present
    cli_path = Path(__file__).parent.parent / "pdd" / "core" / "cli.py"
    cli_content = cli_path.read_text()

    # Check for the specific guard pattern
    expected_pattern = "results is not None and not all(res is None for res in results)"

    assert expected_pattern in cli_content, (
        f"Bug #253 (Secondary): cli.py is missing the 'results is not None' guard.\n"
        f"Expected pattern: '{expected_pattern}'\n"
        f"This causes 'NoneType' object is not iterable when results is None."
    )


@patch('pdd.core.cli.console.print')
@patch('pdd.core.cli._write_core_dump')
def test_process_commands_handles_none_results_issue_253(mock_write_dump, mock_print):
    """
    Regression test for Issue #253 Bug 2.

    Verifies that process_commands handles None results gracefully
    without raising TypeError: 'NoneType' object is not iterable.
    """
    ctx = click.Context(cli_command)
    ctx.obj = {"quiet": False, "core_dump": False}
    ctx.invoked_subcommands = ["generate", "fix"]  # 2 commands expected

    with ctx:
        # This should NOT raise TypeError
        process_commands(results=None)

    # If we reach here without exception, the test passes


# =============================================================================
# Issue #231: --core-dump on by default, garbage collection, --no-core-dump
# =============================================================================

@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_core_dump_on_by_default_issue_231(mock_main, mock_auto_update, runner, create_dummy_files):
    """
    Issue #231: By default, core_dump flag in context should be True.

    This is a feature change from the original behavior where core_dump
    was off by default. Now we gather all info by default.
    """
    files = create_dummy_files("test_core_default_on.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')

    result = runner.invoke(cli.cli, ["generate", str(files["test_core_default_on.prompt"])])

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(result.output)
        if result.exception:
            raise result.exception

    mock_main.assert_called_once()
    ctx = mock_main.call_args.kwargs.get("ctx")
    assert ctx is not None
    # Issue #231: core_dump should be True by default
    assert ctx.obj.get("core_dump") is True, \
        "Issue #231: --core-dump should be on by default"
    mock_auto_update.assert_called_once_with()


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_no_core_dump_flag_issue_231(mock_main, mock_auto_update, runner, create_dummy_files):
    """
    Issue #231: --no-core-dump should disable core dump collection.

    For certain automation cases, users need to disable core dumps.
    """
    files = create_dummy_files("test_no_core_dump.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')

    result = runner.invoke(
        cli.cli,
        [
            "--no-core-dump",
            "generate",
            str(files["test_no_core_dump.prompt"]),
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
    # Issue #231: --no-core-dump should set core_dump to False
    assert ctx.obj.get("core_dump") is False, \
        "Issue #231: --no-core-dump should disable core dump"
    mock_auto_update.assert_called_once_with()


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_no_core_dump_does_not_create_file_issue_231(
    mock_main, mock_auto_update, tmp_path, runner, monkeypatch
):
    """
    Issue #231: --no-core-dump should actually prevent dump file creation.

    This is a regression test to ensure the flag doesn't just set context
    but actually prevents file I/O.
    """
    # Create a test prompt file
    test_prompt = tmp_path / "test.prompt"
    test_prompt.write_text("Test prompt for no-core-dump verification")

    mock_main.return_value = ('code', False, 0.0, 'model')

    # Change to temp directory
    monkeypatch.chdir(tmp_path)

    # Ensure no core dumps exist before
    core_dump_dir = tmp_path / ".pdd" / "core_dumps"
    assert not core_dump_dir.exists() or len(list(core_dump_dir.glob("pdd-core-*.json"))) == 0

    result = runner.invoke(
        cli.cli,
        [
            "--no-core-dump",
            "generate",
            str(test_prompt),
        ],
    )

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(result.output)
        if result.exception:
            raise result.exception

    # Issue #231: No core dump file should be created
    if core_dump_dir.exists():
        dumps = list(core_dump_dir.glob("pdd-core-*.json"))
        assert len(dumps) == 0, \
            f"Issue #231: --no-core-dump should not create any dump files, found: {dumps}"


@patch('pdd.core.cli.auto_update')
@patch('pdd.commands.generate.code_generator_main')
def test_cli_keep_core_dumps_option_issue_231(mock_main, mock_auto_update, runner, create_dummy_files):
    """
    Issue #231: --keep-core-dumps N should be available to override default of 10.

    This option controls how many core dumps to keep during garbage collection.
    """
    files = create_dummy_files("test_keep_core_dumps.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')

    result = runner.invoke(
        cli.cli,
        [
            "--keep-core-dumps", "5",
            "generate",
            str(files["test_keep_core_dumps.prompt"]),
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
    # Issue #231: --keep-core-dumps should set the keep count
    assert ctx.obj.get("keep_core_dumps") == 5, \
        "Issue #231: --keep-core-dumps should set keep_core_dumps in context"
    mock_auto_update.assert_called_once_with()


def test_garbage_collect_core_dumps_function_exists_issue_231():
    """
    Issue #231: garbage_collect_core_dumps function should exist in core/dump.py.

    This function is needed to clean up old core dumps on CLI invocation.
    """
    from pdd.core import dump

    assert hasattr(dump, 'garbage_collect_core_dumps'), \
        "Issue #231: garbage_collect_core_dumps function should exist in core/dump.py"

    # Should be callable
    assert callable(dump.garbage_collect_core_dumps), \
        "Issue #231: garbage_collect_core_dumps should be callable"


def test_garbage_collect_core_dumps_keeps_last_n_issue_231(tmp_path, monkeypatch):
    """
    Issue #231: garbage_collect_core_dumps should delete old core dumps,
    keeping only the last N files sorted by mtime.
    """
    import time
    from pdd.core.dump import garbage_collect_core_dumps

    monkeypatch.chdir(tmp_path)

    # Create core dump directory
    core_dump_dir = tmp_path / ".pdd" / "core_dumps"
    core_dump_dir.mkdir(parents=True, exist_ok=True)

    # Create 15 test core dump files with different mtimes
    for i in range(15):
        dump_file = core_dump_dir / f"pdd-core-2024010{i:02d}T120000Z.json"
        dump_file.write_text(f'{{"index": {i}}}')
        # Set mtime to ensure ordering (older files have earlier mtime)
        mtime = time.time() - (15 - i) * 100  # Earlier index = older file
        os.utime(dump_file, (mtime, mtime))

    # Verify we have 15 files
    assert len(list(core_dump_dir.glob("pdd-core-*.json"))) == 15

    # Run garbage collection with keep=10 (default)
    deleted = garbage_collect_core_dumps(keep=10)

    # Should have deleted 5 files
    assert deleted == 5, f"Expected 5 files deleted, got {deleted}"

    # Should have 10 files remaining
    remaining = list(core_dump_dir.glob("pdd-core-*.json"))
    assert len(remaining) == 10, f"Expected 10 files remaining, got {len(remaining)}"

    # The remaining files should be the 10 newest (highest index)
    remaining_indices = []
    for f in remaining:
        import json
        data = json.loads(f.read_text())
        remaining_indices.append(data["index"])

    remaining_indices.sort()
    assert remaining_indices == list(range(5, 15)), \
        f"Expected indices 5-14 to remain (newest), got {remaining_indices}"


def test_garbage_collect_with_custom_keep_count_issue_231(tmp_path, monkeypatch):
    """
    Issue #231: garbage_collect_core_dumps should respect custom keep count.
    """
    import time
    from pdd.core.dump import garbage_collect_core_dumps

    monkeypatch.chdir(tmp_path)

    # Create core dump directory
    core_dump_dir = tmp_path / ".pdd" / "core_dumps"
    core_dump_dir.mkdir(parents=True, exist_ok=True)

    # Create 10 test core dump files
    for i in range(10):
        dump_file = core_dump_dir / f"pdd-core-2024010{i:01d}T120000Z.json"
        dump_file.write_text(f'{{"index": {i}}}')
        mtime = time.time() - (10 - i) * 100
        os.utime(dump_file, (mtime, mtime))

    # Run garbage collection with keep=3
    deleted = garbage_collect_core_dumps(keep=3)

    # Should have deleted 7 files
    assert deleted == 7, f"Expected 7 files deleted, got {deleted}"

    # Should have 3 files remaining
    remaining = list(core_dump_dir.glob("pdd-core-*.json"))
    assert len(remaining) == 3, f"Expected 3 files remaining, got {len(remaining)}"


def test_garbage_collect_no_directory_issue_231(tmp_path, monkeypatch):
    """
    Issue #231: garbage_collect_core_dumps should handle missing directory gracefully.
    """
    from pdd.core.dump import garbage_collect_core_dumps

    monkeypatch.chdir(tmp_path)

    # Core dump directory does not exist
    core_dump_dir = tmp_path / ".pdd" / "core_dumps"
    assert not core_dump_dir.exists()

    # Should not raise, should return 0
    deleted = garbage_collect_core_dumps(keep=10)
    assert deleted == 0


@patch('pdd.core.cli.auto_update')
@patch('pdd.core.dump.garbage_collect_core_dumps')
@patch('pdd.commands.generate.code_generator_main')
def test_garbage_collection_called_on_invocation_issue_231(
    mock_main, mock_gc, mock_auto_update, runner, create_dummy_files
):
    """
    Issue #231: Garbage collection should be called on every CLI invocation.

    GC runs at CLI startup AND after dump write to ensure:
    1. Cleanup happens on every invocation (including --no-core-dump)
    2. At most N dumps are kept after writing (not N+1)
    """
    files = create_dummy_files("test_gc_on_invocation.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')
    mock_gc.return_value = 0

    result = runner.invoke(cli.cli, ["generate", str(files["test_gc_on_invocation.prompt"])])

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(result.output)
        if result.exception:
            raise result.exception

    # Issue #231: GC should be called at least twice (startup + after dump write)
    assert mock_gc.call_count >= 2, \
        f"Issue #231: GC should be called at startup and after dump write, got {mock_gc.call_count} calls"

    # All calls should use keep=10 by default
    for call in mock_gc.call_args_list:
        assert call.kwargs.get('keep') == 10 or call.args == (10,), \
            "Issue #231: GC should be called with keep=10 by default"


@patch('pdd.core.cli.auto_update')
@patch('pdd.core.dump.garbage_collect_core_dumps')
@patch('pdd.commands.generate.code_generator_main')
def test_garbage_collection_respects_keep_option_issue_231(
    mock_main, mock_gc, mock_auto_update, runner, create_dummy_files
):
    """
    Issue #231: Garbage collection should respect --keep-core-dumps option.
    """
    files = create_dummy_files("test_gc_with_keep.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')
    mock_gc.return_value = 0

    result = runner.invoke(
        cli.cli,
        ["--keep-core-dumps", "20", "generate", str(files["test_gc_with_keep.prompt"])]
    )

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(result.output)
        if result.exception:
            raise result.exception

    # Issue #231: GC should be called at least twice with custom keep value
    assert mock_gc.call_count >= 2, \
        f"Issue #231: GC should be called at startup and after dump write, got {mock_gc.call_count} calls"

    # All calls should use the custom keep value
    for call in mock_gc.call_args_list:
        assert call.kwargs.get('keep') == 20 or call.args == (20,), \
            "Issue #231: GC should be called with keep=20 when --keep-core-dumps=20"


def test_keep_core_dumps_rejects_negative_values_issue_231(runner):
    """
    Issue #231: --keep-core-dumps should reject negative values.

    Negative values would cause incorrect slice behavior (e.g., -1 would
    delete the newest file instead of keeping the last one).
    """
    result = runner.invoke(
        cli.cli,
        ["--keep-core-dumps", "-1"],
    )

    # Click's IntRange should reject negative values
    assert result.exit_code != 0, \
        "Issue #231: --keep-core-dumps should reject negative values"
    assert "Invalid value" in result.output or "not in the range" in result.output, \
        f"Expected error message for negative value, got: {result.output}"


def test_garbage_collect_with_keep_zero_clears_all_issue_231(tmp_path, monkeypatch):
    """
    Issue #231: garbage_collect_core_dumps(keep=0) should clear all dumps.

    A keep value of 0 means "don't keep any old dumps".
    """
    import time
    from pdd.core.dump import garbage_collect_core_dumps

    monkeypatch.chdir(tmp_path)

    # Create core dump directory
    core_dump_dir = tmp_path / ".pdd" / "core_dumps"
    core_dump_dir.mkdir(parents=True, exist_ok=True)

    # Create 5 test core dump files
    for i in range(5):
        dump_file = core_dump_dir / f"pdd-core-2024010{i}T120000Z.json"
        dump_file.write_text(f'{{"index": {i}}}')
        mtime = time.time() - (5 - i) * 100
        os.utime(dump_file, (mtime, mtime))

    # Verify we have 5 files
    assert len(list(core_dump_dir.glob("pdd-core-*.json"))) == 5

    # Run garbage collection with keep=0
    deleted = garbage_collect_core_dumps(keep=0)

    # Should have deleted all 5 files
    assert deleted == 5, f"Expected 5 files deleted, got {deleted}"

    # Should have 0 files remaining
    remaining = list(core_dump_dir.glob("pdd-core-*.json"))
    assert len(remaining) == 0, f"Expected 0 files remaining, got {len(remaining)}"


@patch('pdd.core.cli.auto_update')
@patch('pdd.core.dump.garbage_collect_core_dumps')
@patch('pdd.commands.generate.code_generator_main')
def test_keep_core_dumps_zero_is_valid_issue_231(
    mock_main, mock_gc, mock_auto_update, runner, create_dummy_files
):
    """
    Issue #231: --keep-core-dumps 0 should be valid and clear all old dumps.
    """
    files = create_dummy_files("test_gc_keep_zero.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')
    mock_gc.return_value = 0

    result = runner.invoke(
        cli.cli,
        ["--keep-core-dumps", "0", "generate", str(files["test_gc_keep_zero.prompt"])]
    )

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(result.output)
        if result.exception:
            raise result.exception

    # Issue #231: GC should be called at least twice with keep=0
    assert mock_gc.call_count >= 2, \
        f"Issue #231: GC should be called at startup and after dump write, got {mock_gc.call_count} calls"

    # All calls should use keep=0
    for call in mock_gc.call_args_list:
        assert call.kwargs.get('keep') == 0 or call.args == (0,), \
            "Issue #231: GC should be called with keep=0 when --keep-core-dumps=0"


@patch('pdd.core.cli.auto_update')
@patch('pdd.core.dump.garbage_collect_core_dumps')
@patch('pdd.commands.generate.code_generator_main')
def test_gc_runs_even_with_no_core_dump_issue_231(
    mock_main, mock_gc, mock_auto_update, runner, create_dummy_files
):
    """
    Issue #231: GC should run on every invocation, even with --no-core-dump.

    This ensures old dumps are cleaned up regardless of whether new dumps are written.
    """
    files = create_dummy_files("test_gc_with_no_dump.prompt")
    mock_main.return_value = ('code', False, 0.0, 'model')
    mock_gc.return_value = 0

    result = runner.invoke(
        cli.cli,
        ["--no-core-dump", "generate", str(files["test_gc_with_no_dump.prompt"])]
    )

    if result.exit_code != 0:
        print(f"Unexpected exit code: {result.exit_code}")
        print(result.output)
        if result.exception:
            raise result.exception

    # Issue #231: GC should still be called at CLI startup even with --no-core-dump
    assert mock_gc.call_count >= 1, \
        "Issue #231: GC should run on every invocation, including --no-core-dump"

    # Should be called with keep=10 by default
    call_args = mock_gc.call_args_list[0]
    assert call_args.kwargs.get('keep') == 10 or call_args.args == (10,), \
        "Issue #231: GC should be called with keep=10 by default"
