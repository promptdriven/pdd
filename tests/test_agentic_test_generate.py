"""
Tests for the agentic_test_generate module.

This module tests the agentic test generation flow for non-Python languages.
"""
import json
import os
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock

from pdd.agentic_test_generate import (
    run_agentic_test_generate,
    _get_file_mtimes,
    _extract_json_from_text,
    _read_generated_test_file,
    _detect_changed_files,
)


# -----------------------------------------------------------------------------
# Helper Function Tests
# -----------------------------------------------------------------------------


class TestGetFileMtimes:
    """Tests for _get_file_mtimes helper function."""

    def test_basic_file_scan(self, tmp_path):
        """Test that files are scanned and mtimes recorded."""
        # Create test files
        (tmp_path / "file1.txt").write_text("content1")
        (tmp_path / "file2.py").write_text("content2")

        mtimes = _get_file_mtimes(tmp_path)

        assert len(mtimes) == 2
        assert any("file1.txt" in str(p) for p in mtimes.keys())
        assert any("file2.py" in str(p) for p in mtimes.keys())

    def test_ignores_hidden_dirs(self, tmp_path):
        """Test that .git, __pycache__, etc. are ignored."""
        # Create files in ignored directories
        git_dir = tmp_path / ".git"
        git_dir.mkdir()
        (git_dir / "config").write_text("git config")

        pycache_dir = tmp_path / "__pycache__"
        pycache_dir.mkdir()
        (pycache_dir / "module.pyc").write_text("bytecode")

        # Create a normal file
        (tmp_path / "normal.py").write_text("code")

        mtimes = _get_file_mtimes(tmp_path)

        # Only the normal file should be recorded
        assert len(mtimes) == 1
        assert any("normal.py" in str(p) for p in mtimes.keys())

    def test_handles_empty_directory(self, tmp_path):
        """Test that empty directories return empty dict."""
        mtimes = _get_file_mtimes(tmp_path)
        assert mtimes == {}

    def test_handles_nested_dirs(self, tmp_path):
        """Test that nested directories are scanned."""
        nested = tmp_path / "src" / "lib"
        nested.mkdir(parents=True)
        (nested / "util.js").write_text("export default {}")

        mtimes = _get_file_mtimes(tmp_path)

        assert len(mtimes) == 1
        assert any("util.js" in str(p) for p in mtimes.keys())


class TestExtractJsonFromText:
    """Tests for _extract_json_from_text helper function."""

    def test_extracts_raw_json(self):
        """Test extraction of raw JSON object."""
        text = '{"success": true, "message": "done"}'
        result = _extract_json_from_text(text)

        assert result == {"success": True, "message": "done"}

    def test_extracts_json_from_markdown(self):
        """Test extraction of JSON from markdown code blocks."""
        text = '''
        Here is the result:
        ```json
        {"success": true, "test_file": "test.spec.ts"}
        ```
        '''
        result = _extract_json_from_text(text)

        assert result == {"success": True, "test_file": "test.spec.ts"}

    def test_extracts_json_from_code_block_no_language(self):
        """Test extraction of JSON from code blocks without language hint."""
        text = '''
        ```
        {"success": false, "message": "failed"}
        ```
        '''
        result = _extract_json_from_text(text)

        assert result == {"success": False, "message": "failed"}

    def test_extracts_json_embedded_in_text(self):
        """Test extraction of JSON embedded in surrounding text."""
        text = 'Some preamble {"key": "value"} and epilogue'
        result = _extract_json_from_text(text)

        assert result == {"key": "value"}

    def test_returns_none_for_invalid_json(self):
        """Test that invalid JSON returns None."""
        text = '{"key": invalid}'
        result = _extract_json_from_text(text)

        assert result is None

    def test_returns_none_for_no_json(self):
        """Test that text without JSON returns None."""
        text = 'Just some plain text without any JSON'
        result = _extract_json_from_text(text)

        assert result is None

    def test_returns_none_for_empty_string(self):
        """Test that empty string returns None."""
        assert _extract_json_from_text("") is None
        assert _extract_json_from_text("   ") is None


class TestReadGeneratedTestFile:
    """Tests for _read_generated_test_file helper function."""

    def test_reads_existing_file(self, tmp_path):
        """Test reading an existing test file."""
        test_file = tmp_path / "test.spec.ts"
        test_file.write_text("describe('test', () => {})")

        content = _read_generated_test_file(test_file)

        assert content == "describe('test', () => {})"

    def test_returns_empty_for_nonexistent(self, tmp_path):
        """Test that non-existent file returns empty string."""
        test_file = tmp_path / "nonexistent.test.js"

        content = _read_generated_test_file(test_file)

        assert content == ""

    def test_returns_empty_for_directory(self, tmp_path):
        """Test that a directory path returns empty string."""
        dir_path = tmp_path / "tests"
        dir_path.mkdir()

        content = _read_generated_test_file(dir_path)

        assert content == ""


class TestDetectChangedFiles:
    """Tests for _detect_changed_files helper function."""

    def test_detects_new_files(self, tmp_path):
        """Test detection of newly created files."""
        before = {}
        file1 = tmp_path / "new_file.ts"
        after = {file1: 123456.0}

        changed = _detect_changed_files(before, after, tmp_path)

        assert "new_file.ts" in changed

    def test_detects_modified_files(self, tmp_path):
        """Test detection of modified files."""
        file1 = tmp_path / "existing.js"
        before = {file1: 100.0}
        after = {file1: 200.0}  # Different mtime

        changed = _detect_changed_files(before, after, tmp_path)

        assert "existing.js" in changed

    def test_detects_deleted_files(self, tmp_path):
        """Test detection of deleted files."""
        file1 = tmp_path / "deleted.py"
        before = {file1: 100.0}
        after = {}

        changed = _detect_changed_files(before, after, tmp_path)

        assert "deleted.py" in changed

    def test_ignores_unchanged_files(self, tmp_path):
        """Test that unchanged files are not reported."""
        file1 = tmp_path / "unchanged.go"
        before = {file1: 100.0}
        after = {file1: 100.0}  # Same mtime

        changed = _detect_changed_files(before, after, tmp_path)

        assert changed == []


# -----------------------------------------------------------------------------
# Main Function Tests
# -----------------------------------------------------------------------------


@pytest.fixture
def mock_env(tmp_path):
    """Sets up a temporary environment with dummy files."""
    # Create dummy input files
    prompt_file = tmp_path / "feature.prompt"
    prompt_file.write_text("Create a function that adds two numbers")

    code_file = tmp_path / "add.ts"
    code_file.write_text("export function add(a: number, b: number): number { return a + b; }")

    test_file = tmp_path / "add.test.ts"

    # Save original CWD
    old_cwd = os.getcwd()
    os.chdir(tmp_path)

    yield {
        "prompt": prompt_file,
        "code": code_file,
        "test": test_file,
        "root": tmp_path,
    }

    # Restore CWD
    os.chdir(old_cwd)


@patch("pdd.agentic_test_generate.load_prompt_template")
def test_missing_template(mock_load, mock_env):
    """Test that the function returns failure if the prompt template cannot be loaded."""
    mock_load.return_value = None

    content, cost, model, success = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    assert content == ""
    assert cost == 0.0
    assert model == "unknown"
    assert success is False


@patch("pdd.agentic_test_generate.get_available_agents")
def test_no_agents_available(mock_agents, mock_env):
    """Test that the function returns failure if no agents are available."""
    mock_agents.return_value = []

    content, cost, model, success = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    assert content == ""
    assert cost == 0.0
    assert model == "unknown"
    assert success is False


@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_successful_generation(mock_agents, mock_load, mock_run, mock_env):
    """Test a successful test generation run."""
    mock_agents.return_value = ["anthropic"]
    mock_load.return_value = "Template {prompt_path} {code_path} {test_path} {project_root} {prompt_content} {code_content}"

    # Define side effect to create test file
    def side_effect(*args, **kwargs):
        test_content = "describe('add', () => { it('adds numbers', () => {}); });"
        mock_env["test"].write_text(test_content)
        return (True, '{"success": true, "message": "Generated tests"}', 0.15, "anthropic")

    mock_run.side_effect = side_effect

    content, cost, model, success = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    assert content == "describe('add', () => { it('adds numbers', () => {}); });"
    assert cost == 0.15
    assert model == "agentic-anthropic"
    assert success is True


@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_agent_returns_invalid_json(mock_agents, mock_load, mock_run, mock_env):
    """Test handling of agent output that is not valid JSON."""
    mock_agents.return_value = ["anthropic"]
    mock_load.return_value = "Template"
    mock_run.return_value = (True, "I generated the tests", 0.1, "anthropic")

    content, cost, model, success = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    # Should still work but content will be empty (no test file created)
    assert content == ""
    assert cost == 0.1
    assert success is False  # No valid JSON with success field


@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_detects_test_file_at_different_path(mock_agents, mock_load, mock_run, mock_env):
    """Test detection of test file created at a different path than expected."""
    mock_agents.return_value = ["anthropic"]
    mock_load.return_value = "Template"

    # Agent creates test file with different name
    def side_effect(*args, **kwargs):
        alt_test = mock_env["root"] / "add.spec.ts"
        alt_test.write_text("test('works', () => {});")
        return (True, '{"success": true}', 0.1, "anthropic")

    mock_run.side_effect = side_effect

    content, cost, model, success = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"],
        quiet=True, verbose=True
    )

    # Should find the test file at the alternative path
    assert content == "test('works', () => {});"
    assert success is True


@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_json_in_markdown_block(mock_agents, mock_load, mock_run, mock_env):
    """Test parsing of JSON wrapped in markdown code blocks."""
    mock_agents.return_value = ["anthropic"]
    mock_load.return_value = "Template"

    agent_output = '''
    Here is the result:
    ```json
    {"success": true, "message": "Tests generated", "test_file": "add.test.ts"}
    ```
    '''
    mock_run.return_value = (True, agent_output, 0.2, "anthropic")

    content, cost, model, success = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    # JSON parsing should succeed
    assert cost == 0.2
    assert success is True


@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_handles_missing_input_files(mock_agents, mock_load, mock_run, mock_env):
    """Test handling of missing input files."""
    mock_agents.return_value = ["anthropic"]
    mock_load.return_value = "Template"
    mock_run.return_value = (True, '{"success": true}', 0.1, "anthropic")

    # Remove input files
    mock_env["prompt"].unlink()
    mock_env["code"].unlink()

    # Should not crash, just proceed with empty content
    content, cost, model, success = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"],
        quiet=True, verbose=True
    )

    # Function should still complete
    assert cost == 0.1
    assert success is True


@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_model_name_formatting(mock_agents, mock_load, mock_run, mock_env):
    """Test that model name is properly formatted with provider prefix."""
    mock_agents.return_value = ["google"]
    mock_load.return_value = "Template"
    mock_run.return_value = (True, '{"success": true}', 0.1, "google")

    content, cost, model, success = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    assert model == "agentic-google"
    assert success is True


@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_model_name_fallback(mock_agents, mock_load, mock_run, mock_env):
    """Test model name fallback when provider is empty."""
    mock_agents.return_value = ["anthropic"]
    mock_load.return_value = "Template"
    mock_run.return_value = (True, '{"success": true}', 0.1, "")

    content, cost, model, success = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    assert model == "agentic-cli"
    assert success is True
