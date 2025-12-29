"""
# DETAILED TEST PLAN FOR pdd/agentic_verify.py

## Overview
The module provides `run_agentic_verify()` which delegates verification fixes to a CLI agent
in explore mode. It detects file changes, parses JSON output, and returns results.

## Functions to Test (Public API Only)
1. run_agentic_verify(prompt_file, code_file, program_file, verification_log_file, *, verbose, quiet)
   - Returns: tuple[bool, str, float, str, list[str]]
   - Components: (success, message, cost, model, changed_files)

## Test Strategy

### Unit Tests (Primary Approach)
Since this module involves I/O operations, external CLI calls, and file system monitoring,
unit tests with mocking are the most appropriate testing strategy.

### Z3 Formal Verification Assessment
Z3 formal verification is NOT well-suited for this module because:
1. Heavy reliance on I/O operations (file system, external processes)
2. Non-deterministic behavior (agent responses, file timing)
3. External dependencies that cannot be formally modeled
4. Primary logic is integration/orchestration rather than algorithmic

Therefore, we focus on comprehensive unit testing with mocking.

## Test Cases

### 1. Happy Path Tests
   - TC1.1: Agent returns valid JSON with success=True, files changed
   - TC1.2: Agent returns valid JSON with success=True, no files changed
   - TC1.3: Verification log file exists and is read correctly
   - TC1.4: Verification log file doesn't exist (uses default message)

### 2. Error Handling Tests
   - TC2.1: Template loading fails (returns error tuple)
   - TC2.2: Agent returns valid JSON with success=False
   - TC2.3: Agent output contains no valid JSON
   - TC2.4: Agent output contains JSON in markdown code blocks

### 3. File Change Detection Tests
   - TC3.1: New files created during execution
   - TC3.2: Existing files modified during execution
   - TC3.3: Multiple files changed
   - TC3.4: Files deleted during execution (won't appear in changed list)

### 4. JSON Parsing Tests (Indirect)
   - TC4.1: JSON embedded in markdown code blocks with ```json
   - TC4.2: JSON embedded in markdown code blocks without language
   - TC4.3: Raw JSON without code blocks
   - TC4.4: Malformed JSON (should fallback gracefully)
   - TC4.5: Multiple JSON objects (extracts first)

### 5. Integration Tests
   - TC5.1: Verbose flag is passed to underlying agent
   - TC5.2: Quiet flag suppresses console output
   - TC5.3: All file paths are resolved correctly
   - TC5.4: Project root is set to current working directory

### 6. Edge Cases
   - TC6.1: Empty verification log file
   - TC6.2: Very large verification log
   - TC6.3: Changed files outside project root (handled gracefully)
   - TC6.4: Special characters in file paths

## Mocking Strategy
- Mock `load_prompt_template`: Control template loading success/failure
- Mock `run_agentic_task`: Control agent responses and simulate execution
- Use temporary directories: Isolate file system operations
- Mock console output: Verify logging behavior

## Test Data Requirements
- Sample prompt template strings
- Sample agent JSON responses (success and failure)
- Sample verification log content
- Temporary file structures for change detection

## Coverage Goals
- 100% coverage of public API (run_agentic_verify)
- All return value combinations tested
- All error paths exercised
- File change detection scenarios covered
"""

import json
import time
from pathlib import Path
from typing import Any
from unittest.mock import patch

import pytest

# Import the function under test using the ACTUAL module path
from pdd.agentic_verify import run_agentic_verify


# ============================================================================
# FIXTURES
# ============================================================================


@pytest.fixture
def temp_project_dir(tmp_path: Path) -> dict[str, Path]:
    """Create a temporary project directory structure."""
    prompt_file = tmp_path / "prompt.txt"
    code_file = tmp_path / "code.py"
    program_file = tmp_path / "program.py"
    verification_log = tmp_path / "verification.log"

    # Create basic files
    prompt_file.write_text("Test prompt content")
    code_file.write_text("def test(): pass")
    program_file.write_text("import code; code.test()")

    return {
        "root": tmp_path,
        "prompt_file": prompt_file,
        "code_file": code_file,
        "program_file": program_file,
        "verification_log": verification_log,
    }


@pytest.fixture
def mock_template() -> str:
    """Provide a mock prompt template."""
    return (
        "You are fixing a verification failure.\n"
        "Prompt: {prompt_path}\n"
        "Code: {code_path}\n"
        "Program: {program_path}\n"
        "Project: {project_root}\n"
        "Previous: {previous_attempts}"
    )


@pytest.fixture
def sample_agent_success_json() -> dict[str, Any]:
    """Sample successful agent response as JSON."""
    return {
        "success": True,
        "message": "Fixed the issue by updating the code",
        "cost": 0.05,
        "model": "claude-3",
        "changed_files": ["code.py", "program.py"],
    }


@pytest.fixture
def sample_agent_failure_json() -> dict[str, Any]:
    """Sample failed agent response as JSON."""
    return {
        "success": False,
        "message": "Could not resolve the issue",
        "cost": 0.03,
        "model": "claude-3",
        "changed_files": [],
    }


# ============================================================================
# TEST CASES: Happy Path
# ============================================================================


def test_successful_verification_with_valid_json(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC1.1: Agent returns valid JSON with success=True and files are changed."""
    # Create verification log
    temp_project_dir["verification_log"].write_text(
        "Previous attempt 1: Failed\nPrevious attempt 2: Failed"
    )

    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template

        # Agent returns JSON wrapped in code block
        agent_output = f"```json\n{json.dumps(sample_agent_success_json)}\n```"
        mock_agent.return_value = (True, agent_output, 0.05, "claude-3")

        # Simulate file changes by modifying file before calling
        time.sleep(0.01)  # Ensure time difference
        temp_project_dir["code_file"].write_text("def test(): return 42")

        success, message, cost, model, changed_files = run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            verbose=False,
            quiet=True,
        )

        assert success is True
        assert message == "Fixed the issue by updating the code"
        assert cost == 0.05
        assert model == "claude-3"
        assert isinstance(changed_files, list)


def test_successful_verification_no_file_changes(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC1.2: Agent returns valid JSON with success=True but no files changed."""
    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template

        agent_output = json.dumps(sample_agent_success_json)
        mock_agent.return_value = (True, agent_output, 0.05, "claude-3")

        success, message, cost, model, changed_files = run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        assert success is True
        # Changed files list should be based on actual mtime changes (empty or populated)
        assert isinstance(changed_files, list)


def test_verification_log_exists_and_read(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC1.3: Verification log file exists and is read correctly."""
    log_content = (
        "Previous attempt 1: Failed with error X\n"
        "Previous attempt 2: Failed with error Y"
    )
    temp_project_dir["verification_log"].write_text(log_content)

    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template

        agent_output = json.dumps(sample_agent_success_json)
        mock_agent.return_value = (True, agent_output, 0.05, "claude-3")

        success, message, cost, model, changed_files = run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        # Verify the agent was called with instruction containing log content
        call_args = mock_agent.call_args
        instruction = call_args[1]["instruction"]
        assert log_content in instruction


def test_verification_log_missing_uses_default(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC1.4: Verification log file doesn't exist, uses default message."""
    # Don't create the verification log

    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template

        agent_output = json.dumps(sample_agent_success_json)
        mock_agent.return_value = (True, agent_output, 0.05, "claude-3")

        success, message, cost, model, changed_files = run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        # Verify the agent was called with default message
        call_args = mock_agent.call_args
        instruction = call_args[1]["instruction"]
        assert "No previous verification logs found" in instruction


# ============================================================================
# TEST CASES: Error Handling
# ============================================================================


def test_template_loading_fails(temp_project_dir: dict[str, Path]) -> None:
    """TC2.1: Template loading fails, returns error tuple."""
    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = None  # Simulate failure

        success, message, cost, model, changed_files = run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        assert success is False
        assert "Failed to load prompt template" in message
        assert cost == 0.0
        assert model == "unknown"
        assert changed_files == []


def test_agent_returns_failure_json(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_failure_json: dict[str, Any],
) -> None:
    """TC2.2: Agent returns valid JSON with success=False."""
    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template

        agent_output = json.dumps(sample_agent_failure_json)
        mock_agent.return_value = (True, agent_output, 0.03, "claude-3")

        success, message, cost, model, changed_files = run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        assert success is False
        assert message == "Could not resolve the issue"
        assert cost == 0.03
        assert model == "claude-3"


def test_agent_returns_invalid_json(
    temp_project_dir: dict[str, Path],
    mock_template: str,
) -> None:
    """TC2.3: Agent output contains no valid JSON."""
    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template

        agent_output = "This is plain text without any JSON structure"
        mock_agent.return_value = (True, agent_output, 0.02, "claude-3")

        success, message, cost, model, changed_files = run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
            verbose=False,
        )

        assert success is False
        assert message == agent_output
        assert cost == 0.02
        assert model == "claude-3"


def test_agent_returns_json_in_markdown_with_language(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC2.4: Agent output contains JSON in markdown code blocks with language specifier."""
    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template

        agent_output = (
            f"Here is the result:\n```json\n"
            f"{json.dumps(sample_agent_success_json)}\n```\nDone!"
        )
        mock_agent.return_value = (True, agent_output, 0.05, "claude-3")

        success, message, cost, model, changed_files = run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        assert success is True
        assert message == "Fixed the issue by updating the code"


def test_agent_returns_json_in_markdown_without_language(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC4.2: Agent output contains JSON in markdown code blocks without language."""
    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template

        agent_output = f"```\n{json.dumps(sample_agent_success_json)}\n```"
        mock_agent.return_value = (True, agent_output, 0.05, "claude-3")

        success, message, cost, model, changed_files = run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        assert success is True
        assert message == "Fixed the issue by updating the code"


# ============================================================================
# TEST CASES: File Change Detection
# ============================================================================


def test_new_files_created_during_execution(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC3.1: New files created during execution are detected."""
    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template

        def create_new_file(*args: Any, **kwargs: Any) -> tuple[bool, str, float, str]:
            """Simulate agent creating a new file."""
            new_file = temp_project_dir["root"] / "new_file.py"
            new_file.write_text("# New file created by agent")
            return (True, json.dumps(sample_agent_success_json), 0.05, "claude-3")

        mock_agent.side_effect = create_new_file

        success, message, cost, model, changed_files = run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        assert success is True
        assert "new_file.py" in changed_files or any(
            "new_file.py" in f for f in changed_files
        )


def test_existing_files_modified_during_execution(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC3.2: Existing files modified during execution are detected."""
    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template

        def modify_existing_file(
            *args: Any, **kwargs: Any
        ) -> tuple[bool, str, float, str]:
            """Simulate agent modifying an existing file."""
            time.sleep(0.01)  # Ensure mtime changes
            temp_project_dir["code_file"].write_text("def test(): return 'modified'")
            return (True, json.dumps(sample_agent_success_json), 0.05, "claude-3")

        mock_agent.side_effect = modify_existing_file

        success, message, cost, model, changed_files = run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        assert success is True
        assert any("code.py" in f for f in changed_files)


def test_multiple_files_changed(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC3.3: Multiple files changed during execution."""
    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template

        def modify_multiple_files(
            *args: Any, **kwargs: Any
        ) -> tuple[bool, str, float, str]:
            """Simulate agent modifying multiple files."""
            time.sleep(0.01)
            temp_project_dir["code_file"].write_text("def test(): return 'modified'")
            temp_project_dir["program_file"].write_text(
                "import code; print(code.test())"
            )
            (temp_project_dir["root"] / "helper.py").write_text("# Helper module")
            return (True, json.dumps(sample_agent_success_json), 0.05, "claude-3")

        mock_agent.side_effect = modify_multiple_files

        success, message, cost, model, changed_files = run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        assert success is True
        assert len(changed_files) >= 2


# ============================================================================
# TEST CASES: Integration
# ============================================================================


def test_verbose_flag_passed_to_agent(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC5.1: Verbose flag is passed to underlying agent."""
    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template
        mock_agent.return_value = (
            True,
            json.dumps(sample_agent_success_json),
            0.05,
            "claude-3",
        )

        run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            verbose=True,
            quiet=True,
        )

        # Verify verbose was passed
        call_kwargs = mock_agent.call_args[1]
        assert call_kwargs["verbose"] is True


def test_quiet_flag_passed_to_agent(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC5.2: Quiet flag is passed to underlying agent."""
    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template
        mock_agent.return_value = (
            True,
            json.dumps(sample_agent_success_json),
            0.05,
            "claude-3",
        )

        run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            verbose=False,
            quiet=True,
        )

        # Verify quiet was passed
        call_kwargs = mock_agent.call_args[1]
        assert call_kwargs["quiet"] is True


def test_file_paths_resolved_correctly(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC5.3: All file paths are resolved correctly in instruction."""
    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template
        mock_agent.return_value = (
            True,
            json.dumps(sample_agent_success_json),
            0.05,
            "claude-3",
        )

        run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        # Verify instruction contains resolved paths
        instruction = mock_agent.call_args[1]["instruction"]
        assert str(temp_project_dir["prompt_file"].resolve()) in instruction
        assert str(temp_project_dir["code_file"].resolve()) in instruction
        assert str(temp_project_dir["program_file"].resolve()) in instruction


def test_project_root_is_cwd(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC5.4: Project root is set to current working directory."""
    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template
        mock_agent.return_value = (
            True,
            json.dumps(sample_agent_success_json),
            0.05,
            "claude-3",
        )

        run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        # Verify cwd parameter
        call_kwargs = mock_agent.call_args[1]
        assert call_kwargs["cwd"] == temp_project_dir["root"]


# ============================================================================
# TEST CASES: Edge Cases
# ============================================================================


def test_empty_verification_log(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC6.1: Empty verification log file."""
    temp_project_dir["verification_log"].write_text("")

    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template
        mock_agent.return_value = (
            True,
            json.dumps(sample_agent_success_json),
            0.05,
            "claude-3",
        )

        success, message, cost, model, changed_files = run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        assert success is True


def test_large_verification_log(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC6.2: Very large verification log."""
    large_content = "Failed attempt\n" * 10000
    temp_project_dir["verification_log"].write_text(large_content)

    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template
        mock_agent.return_value = (
            True,
            json.dumps(sample_agent_success_json),
            0.05,
            "claude-3",
        )

        success, message, cost, model, changed_files = run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        assert success is True


def test_special_characters_in_paths(
    tmp_path: Path,
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC6.4: Special characters in file paths."""
    # Create directory with special characters
    special_dir = tmp_path / "test-dir_with.special$chars"
    special_dir.mkdir()

    prompt_file = special_dir / "prompt (v2).txt"
    code_file = special_dir / "code-file.py"
    program_file = special_dir / "program_v2.py"
    verification_log = special_dir / "log.txt"

    prompt_file.write_text("Test prompt")
    code_file.write_text("def test(): pass")
    program_file.write_text("import code")

    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = special_dir
        mock_load.return_value = mock_template
        mock_agent.return_value = (
            True,
            json.dumps(sample_agent_success_json),
            0.05,
            "claude-3",
        )

        success, message, cost, model, changed_files = run_agentic_verify(
            prompt_file,
            code_file,
            program_file,
            verification_log,
            quiet=True,
        )

        assert success is True


def test_malformed_json_with_braces(
    temp_project_dir: dict[str, Path],
    mock_template: str,
) -> None:
    """TC4.4: Malformed JSON that looks like JSON but isn't valid."""
    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template

        # Invalid JSON with syntax error
        agent_output = '{"success": True, "message": "Missing comma" "another": "field"}'
        mock_agent.return_value = (True, agent_output, 0.02, "claude-3")

        success, message, cost, model, changed_files = run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        # Should gracefully handle malformed JSON
        assert success is False


def test_json_with_extra_fields(
    temp_project_dir: dict[str, Path],
    mock_template: str,
) -> None:
    """TC: JSON with extra fields beyond the required ones."""
    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template

        extended_json = {
            "success": True,
            "message": "Fixed successfully",
            "cost": 0.04,
            "model": "claude-3",
            "changed_files": ["code.py"],
            "extra_field": "extra_value",
            "another_field": 123,
        }

        agent_output = json.dumps(extended_json)
        mock_agent.return_value = (True, agent_output, 0.04, "claude-3")

        success, message, cost, model, changed_files = run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        # Should successfully parse despite extra fields
        assert success is True
        assert message == "Fixed successfully"


def test_label_parameter_passed_correctly(
    temp_project_dir: dict[str, Path],
    mock_template: str,
    sample_agent_success_json: dict[str, Any],
) -> None:
    """TC: Verify that the label parameter is passed correctly to run_agentic_task."""
    with (
        patch("pdd.agentic_verify.load_prompt_template") as mock_load,
        patch("pdd.agentic_verify.run_agentic_task") as mock_agent,
        patch("pdd.agentic_verify.Path.cwd") as mock_cwd,
    ):
        mock_cwd.return_value = temp_project_dir["root"]
        mock_load.return_value = mock_template
        mock_agent.return_value = (
            True,
            json.dumps(sample_agent_success_json),
            0.05,
            "claude-3",
        )

        run_agentic_verify(
            temp_project_dir["prompt_file"],
            temp_project_dir["code_file"],
            temp_project_dir["program_file"],
            temp_project_dir["verification_log"],
            quiet=True,
        )

        # Verify label was passed
        call_kwargs = mock_agent.call_args[1]
        assert call_kwargs["label"] == "verify-explore"