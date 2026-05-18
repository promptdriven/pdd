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

    content, cost, model, success, error_msg = run_agentic_test_generate(
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

    content, cost, model, success, error_msg = run_agentic_test_generate(
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

    content, cost, model, success, error_msg = run_agentic_test_generate(
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

    content, cost, model, success, error_msg = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    # Should still work but content will be empty (no test file created)
    assert content == ""
    assert cost == 0.1
    assert success is False  # No valid JSON with success field


@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_success_inferred_when_json_missing_but_test_file_exists(
    mock_agents, mock_load, mock_run, mock_env
):
    """Test fallback: agent succeeded and created test file, but JSON not in final output.

    Reproduces the bug where Claude CLI's --output-format json puts only the
    last assistant text in 'result'. If the agent outputs JSON in a non-final
    turn (e.g., before a TodoWrite call), PDD receives the summary table
    instead, which contains no JSON. The agent DID succeed and the test file
    exists, so we should infer success.
    """
    mock_agents.return_value = ["anthropic"]
    mock_load.return_value = "Template"

    # Agent creates test file but returns non-JSON summary text (last turn)
    def side_effect(*args, **kwargs):
        test_content = "describe('add', () => { it('works', () => {}); });"
        mock_env["test"].write_text(test_content)
        return (True, "## Summary\n| Tests | Status |\n|-------|--------|\n| 49 | Passed |", 0.15, "anthropic")

    mock_run.side_effect = side_effect

    content, cost, model, success, error_msg = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    assert content == "describe('add', () => { it('works', () => {}); });"
    assert cost == 0.15
    assert success is True


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

    content, cost, model, success, error_msg = run_agentic_test_generate(
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

    content, cost, model, success, error_msg = run_agentic_test_generate(
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
    content, cost, model, success, error_msg = run_agentic_test_generate(
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

    content, cost, model, success, error_msg = run_agentic_test_generate(
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

    content, cost, model, success, error_msg = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    assert model == "agentic-cli"
    assert success is True


# -----------------------------------------------------------------------------
# Prompt Template Content Tests
# -----------------------------------------------------------------------------


class TestAgenticTestPromptContent:
    """Tests that the agentic test generation prompt contains language-specific guidance."""

    def test_prompt_contains_python_import_rules(self):
        """Bug fix: The agentic test prompt must contain Python-specific import guidance.

        Without this, the agentic generator produces tests like:
            from src.hello import hello
        instead of:
            from hello import hello
        which causes pytest-cov (--cov=hello) to report 0% coverage.
        """
        prompt_path = Path(__file__).parent.parent / "pdd" / "prompts" / "agentic_test_generate_LLM.prompt"
        prompt_content = prompt_path.read_text()

        # Must contain Python-specific import rule
        assert "from hello import hello" in prompt_content or "by its filename stem" in prompt_content, (
            "Agentic test prompt must contain Python-specific import guidance "
            "to prevent 'from src.hello import hello' style imports"
        )

        # Must mention sys.path setup for Python
        assert "sys.path" in prompt_content, (
            "Agentic test prompt must contain sys.path setup instructions for Python"
        )


# --- Issue #1072 Tests: Error message dropped from return value ---


@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_error_message_returned_when_all_providers_fail(mock_agents, mock_load, mock_run, mock_env):
    """Issue #1072: run_agentic_test_generate must return the error message as a 5th tuple element.

    When all agent providers fail, run_agentic_task returns
    (False, "All agent providers failed: ...", 0.0, ""). The error string is stored
    in local variable `message` at line 266 but NEVER returned — the function returns
    a 4-tuple (content, cost, model_name, final_success) at line 310, silently
    dropping the error.

    This test verifies the fix: a 5-tuple is returned where result[4] contains
    the provider failure error message.
    """
    mock_agents.return_value = ["anthropic"]
    mock_load.return_value = (
        "Template {prompt_path} {code_path} {test_path} "
        "{project_root} {prompt_content} {code_content}"
    )
    error_msg = "All agent providers failed: anthropic: Exit code 1; google: TerminalQuotaError"
    mock_run.return_value = (False, error_msg, 0.0, "")

    result = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    assert len(result) == 5, (
        f"Expected 5-tuple but got {len(result)}-tuple — "
        f"error message is silently dropped at agentic_test_generate.py:310"
    )
    content, cost, model, success, returned_error = result
    assert success is False
    assert content == ""
    assert "All agent providers failed" in returned_error, (
        f"Expected error message containing provider failure, got: {returned_error!r}"
    )


@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_error_message_from_json_failure_report(mock_agents, mock_load, mock_run, mock_env):
    """Issue #1072: When agent returns JSON with success=false, the parsed message must
    be included as the 5th tuple element.

    run_agentic_task returns (True, '{"success": false, "message": "Tests failed: ..."}', ...).
    The code parses this JSON and stores the message in the local `message` variable
    (line 269/272) but never returns it in the tuple (line 310).
    """
    mock_agents.return_value = ["anthropic"]
    mock_load.return_value = (
        "Template {prompt_path} {code_path} {test_path} "
        "{project_root} {prompt_content} {code_content}"
    )
    json_output = json.dumps({
        "success": False,
        "message": "Tests failed: 3 of 10 failed"
    })
    mock_run.return_value = (True, json_output, 0.15, "anthropic")

    result = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    assert len(result) == 5, (
        f"Expected 5-tuple but got {len(result)}-tuple — "
        f"error message is silently dropped at agentic_test_generate.py:310"
    )
    content, cost, model, success, returned_error = result
    assert success is False
    assert "Tests failed: 3 of 10 failed" in returned_error, (
        f"Expected JSON-parsed failure message in 5th element, got: {returned_error!r}"
    )


@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_empty_error_on_successful_generation(mock_agents, mock_load, mock_run, mock_env):
    """Issue #1072: On success, the 5th tuple element must be an empty string (no error).

    Regression guard: ensures the 5-tuple fix doesn't accidentally return
    success messages as error messages.
    """
    mock_agents.return_value = ["anthropic"]
    mock_load.return_value = (
        "Template {prompt_path} {code_path} {test_path} "
        "{project_root} {prompt_content} {code_content}"
    )

    def side_effect(*args, **kwargs):
        test_content = "describe('add', () => { it('adds numbers', () => {}); });"
        mock_env["test"].write_text(test_content)
        return (True, '{"success": true, "message": "Generated tests"}', 0.15, "anthropic")

    mock_run.side_effect = side_effect

    result = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    assert len(result) == 5, (
        f"Expected 5-tuple but got {len(result)}-tuple"
    )
    content, cost, model, success, returned_error = result
    assert success is True
    assert returned_error == "", (
        f"Expected empty error on success, got: {returned_error!r}"
    )


# Scope addition: covers expansion item "early returns at agentic_test_generate.py:190 201 235
# must also return 5-tuples with error messages" identified by Step 6 but absent from Step 8's plan
@patch("pdd.agentic_test_generate.get_available_agents")
def test_early_return_no_agents_returns_5_tuple_with_error(mock_agents, mock_env):
    """Issue #1072 (Step 6 expansion): Early return at line 190 (no agents available)
    must also return a 5-tuple with an error message, not a 4-tuple.
    """
    mock_agents.return_value = []

    result = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    assert len(result) == 5, (
        f"Early return (no agents) at line 190 returns {len(result)}-tuple, "
        f"expected 5-tuple with error message"
    )
    content, cost, model, success, returned_error = result
    assert success is False
    assert returned_error != "", (
        "Early return (no agents) should include a non-empty error message"
    )


# Scope addition: covers expansion item "early returns at agentic_test_generate.py:190 201 235"
@patch("pdd.agentic_test_generate.load_prompt_template")
def test_early_return_missing_template_returns_5_tuple_with_error(mock_load, mock_env):
    """Issue #1072 (Step 6 expansion): Early return at line 201 (missing template)
    must also return a 5-tuple with an error message.
    """
    mock_load.return_value = None

    result = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    assert len(result) == 5, (
        f"Early return (missing template) at line 201 returns {len(result)}-tuple, "
        f"expected 5-tuple with error message"
    )
    content, cost, model, success, returned_error = result
    assert success is False
    assert returned_error != "", (
        "Early return (missing template) should include a non-empty error message"
    )


# ---------------------------------------------------------------------------
# Codex review (#1015) F-A / F-H (iter-10): the repair directive must
# reach the agentic test-generation instruction via the explicit
# `repair_directive` kwarg. run_agentic_test_generate MUST NOT read
# `PDD_REPAIR_DIRECTIVE` from the environment — a stale outer value
# would otherwise contaminate direct invocations that have no active
# retry context.
# ---------------------------------------------------------------------------
@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_pdd_repair_directive_reaches_agentic_instruction(
    mock_agents, mock_load, mock_run, mock_env, monkeypatch
):
    """When `repair_directive` is passed, run_agentic_test_generate
    must append a `<test_repair_directive>` block to prompt_content
    before formatting the agent instruction. The on-disk prompt file
    is NOT mutated; only the in-process prompt content sent to the
    agent is augmented."""
    # Ensure no ambient env contamination — kwarg is the only channel.
    monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

    mock_agents.return_value = ["anthropic"]
    mock_load.return_value = (
        "Template prompt_content={prompt_content} code={code_content} "
        "prompt_path={prompt_path} code_path={code_path} test_path={test_path} "
        "project_root={project_root}"
    )

    def side_effect(*args, **kwargs):
        mock_env["test"].write_text("test content")
        return (True, '{"success": true}', 0.1, "anthropic")

    mock_run.side_effect = side_effect

    run_agentic_test_generate(
        mock_env["prompt"],
        mock_env["code"],
        mock_env["test"],
        quiet=True,
        repair_directive="repair text for test retry",
    )

    # The injected directive must be present in the agent's instruction.
    assert mock_run.call_count == 1
    instruction = mock_run.call_args.kwargs["instruction"]
    assert "<test_repair_directive>" in instruction
    assert "repair text for test retry" in instruction
    assert "</test_repair_directive>" in instruction
    # Original prompt content is preserved.
    assert "Create a function that adds two numbers" in instruction
    # On-disk prompt file is not mutated.
    assert mock_env["prompt"].read_text(encoding="utf-8") == (
        "Create a function that adds two numbers"
    )


@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_pdd_repair_directive_absent_when_kwarg_unset(
    mock_agents, mock_load, mock_run, mock_env, monkeypatch
):
    """When `repair_directive` is None (default), no directive block
    is injected."""
    monkeypatch.delenv("PDD_REPAIR_DIRECTIVE", raising=False)

    mock_agents.return_value = ["anthropic"]
    mock_load.return_value = (
        "Template prompt_content={prompt_content} code={code_content} "
        "prompt_path={prompt_path} code_path={code_path} test_path={test_path} "
        "project_root={project_root}"
    )

    def side_effect(*args, **kwargs):
        mock_env["test"].write_text("test content")
        return (True, '{"success": true}', 0.1, "anthropic")

    mock_run.side_effect = side_effect

    run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    instruction = mock_run.call_args.kwargs["instruction"]
    assert "<test_repair_directive>" not in instruction


@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_agentic_test_generate_ignores_stale_env_directive_without_kwarg(
    mock_agents, mock_load, mock_run, mock_env, monkeypatch
):
    """Codex F-H: run_agentic_test_generate MUST NOT read
    `PDD_REPAIR_DIRECTIVE` from the environment. Direct invocations
    with a stale outer env value but no `repair_directive` kwarg must
    NOT inject a `<test_repair_directive>` block."""
    monkeypatch.setenv("PDD_REPAIR_DIRECTIVE", "STALE-OUTER-DIRECTIVE")

    mock_agents.return_value = ["anthropic"]
    mock_load.return_value = (
        "Template prompt_content={prompt_content} code={code_content} "
        "prompt_path={prompt_path} code_path={code_path} test_path={test_path} "
        "project_root={project_root}"
    )

    def side_effect(*args, **kwargs):
        mock_env["test"].write_text("test content")
        return (True, '{"success": true}', 0.1, "anthropic")

    mock_run.side_effect = side_effect

    run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    instruction = mock_run.call_args.kwargs["instruction"]
    assert "<test_repair_directive>" not in instruction
    assert "STALE-OUTER-DIRECTIVE" not in instruction


# -----------------------------------------------------------------------------
# Alternate-path churn recovery (PR #1015 external review iter-11 follow-up).
# The agent may write tests to a path other than `output_test_file` (e.g.
# `__tests__/foo.test.ts`). When that alt path existed before the run with
# real coverage, the outer `cmd_test_main` churn check compares the alt
# content against the CANONICAL path's pre-existing content (empty) and
# misses the regression. `run_agentic_test_generate` now snapshots
# pre-existing test-like file contents from the working tree BEFORE the
# agent runs (covering tracked-clean, tracked-dirty, AND untracked alt
# tests uniformly) and re-runs the churn check against that snapshot,
# restoring the pre-run content on failure.
# -----------------------------------------------------------------------------


@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_alt_path_rewrite_with_untracked_prior_raises_churn_error(
    mock_agents, mock_load, mock_run, mock_env
):
    """Agent rewrites a pre-existing UNTRACKED alt-path test file
    (20 tests → 1) when the canonical path is absent. Because the
    baseline now comes from a working-tree snapshot (not `git show
    HEAD`), the untracked prior content drives the churn check and
    the gate fires. The alt path is restored to the snapshotted
    pre-run content so the repair loop sees the actual pre-sync
    state."""
    mock_agents.return_value = ["anthropic"]
    mock_load.return_value = "Template"

    alt_path = mock_env["root"] / "__tests__" / "foo.test.ts"
    alt_path.parent.mkdir(parents=True, exist_ok=True)
    pre_existing = (
        "\n".join(f"it('case {i}', () => {{}});" for i in range(20)) + "\n"
    )
    # Write the alt-path file on disk BEFORE the agent runs. No git
    # commit — the file is untracked. The snapshot taken inside
    # run_agentic_test_generate must still pick it up so the churn
    # gate has the right baseline.
    alt_path.write_text(pre_existing, encoding="utf-8")

    rewritten = "it('case 0', () => {});\n"

    def side_effect(*args, **kwargs):
        alt_path.write_text(rewritten, encoding="utf-8")
        return (True, '{"success": true, "message": "Generated tests"}', 0.2, "anthropic")

    mock_run.side_effect = side_effect

    from pdd.code_generator_main import TestChurnError

    with pytest.raises(TestChurnError) as excinfo:
        run_agentic_test_generate(
            mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
        )

    # Repair-loop hand-off: alt path restored to the snapshotted
    # pre-run content (untracked, never in git), cost/model attached.
    assert alt_path.read_text(encoding="utf-8") == pre_existing
    assert excinfo.value.total_cost == 0.2
    assert excinfo.value.model_name == "agentic-anthropic"
    # Canonical path stayed untouched (this branch only fires when
    # canonical was never written).
    assert not mock_env["test"].exists()


@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_alt_path_restore_preserves_dirty_working_tree_edits(
    mock_agents, mock_load, mock_run, mock_env
):
    """Tracked-but-dirty alt-path: the snapshot captures the
    working-tree (dirty) content, NOT git HEAD. On `TestChurnError`
    the restore writes the dirty content back, preserving local
    edits that an HEAD-based restore would have silently discarded.
    """
    mock_agents.return_value = ["anthropic"]
    mock_load.return_value = "Template"

    alt_path = mock_env["root"] / "__tests__" / "foo.test.ts"
    alt_path.parent.mkdir(parents=True, exist_ok=True)
    # The "dirty" working-tree content the user had on disk before
    # `pdd sync` ran. In a real git repo HEAD would still hold the
    # pristine 20-test version; we don't have a repo here, but the
    # snapshot approach doesn't consult git at all, so the test
    # exercises the same code path either way.
    dirty_working_tree = (
        "\n".join(f"it('dirty case {i}', () => {{}});" for i in range(25))
        + "\n// uncommitted local edits\n"
    )
    alt_path.write_text(dirty_working_tree, encoding="utf-8")

    rewritten = "it('case 0', () => {});\n"

    def side_effect(*args, **kwargs):
        alt_path.write_text(rewritten, encoding="utf-8")
        return (True, '{"success": true, "message": "Generated tests"}', 0.15, "anthropic")

    mock_run.side_effect = side_effect

    from pdd.code_generator_main import TestChurnError

    with pytest.raises(TestChurnError):
        run_agentic_test_generate(
            mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
        )

    # Restore must produce the dirty working-tree content, not HEAD.
    assert alt_path.read_text(encoding="utf-8") == dirty_working_tree


@patch("pdd.agentic_test_generate.run_agentic_task")
@patch("pdd.agentic_test_generate.load_prompt_template")
@patch("pdd.agentic_test_generate.get_available_agents")
def test_alt_path_first_time_generation_does_not_raise(
    mock_agents, mock_load, mock_run, mock_env
):
    """When the alt-path file did NOT exist before the agent ran,
    the snapshot has no entry for it; the alt-path branch falls
    through (first-time generation is exempt) and the function
    returns the alt-path content normally."""
    mock_agents.return_value = ["anthropic"]
    mock_load.return_value = "Template"

    alt_path = mock_env["root"] / "__tests__" / "foo.test.ts"
    alt_path.parent.mkdir(parents=True, exist_ok=True)
    rewritten = "it('case 0', () => {});\n"

    def side_effect(*args, **kwargs):
        # Brand-new alt path; no pre-existing content to snapshot.
        alt_path.write_text(rewritten, encoding="utf-8")
        return (True, '{"success": true, "message": "Generated tests"}', 0.1, "anthropic")

    mock_run.side_effect = side_effect

    content, cost, model, success, error_msg = run_agentic_test_generate(
        mock_env["prompt"], mock_env["code"], mock_env["test"], quiet=True
    )

    assert content == rewritten
    assert cost == 0.1
    assert success is True
    assert alt_path.read_text(encoding="utf-8") == rewritten
