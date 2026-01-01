"""
Test Suite for pdd/agentic_verify.py

DETAILED TEST PLAN:
===================

## Functions Under Test:
1. run_agentic_verify() - Main entry point for agentic verification fallback

## Test Categories:

### A. Template Loading Tests
   - Test when template loads successfully
   - Test when template loading fails (should return early with error)

### B. Verification Log Handling Tests
   - Test when verification_log_file exists and has content
   - Test when verification_log_file doesn't exist (should use default message)

### C. Agent Execution Success Tests
   - Test successful agent execution with valid JSON response
   - Test successful agent execution with JSON in markdown code blocks
   - Test successful agent execution with raw JSON
   - Test agent execution with invalid/malformed JSON
   - Test agent execution with no JSON in output

### D. Agent Execution Failure Tests
   - Test when agent task fails completely
   - Test when agent returns success=False in JSON

### E. File Change Detection Tests
   - Test detection of modified files (mtime changes)
   - Test detection of newly created files
   - Test when no files are changed
   - Test relative path conversion for changed files
   - Test handling of files in ignored directories (.git, __pycache__, etc.)

### F. Return Value Tests
   - Verify correct 5-tuple structure: (success, message, cost, model, changed_files)
   - Verify cost and model are passed through from agent
   - Verify changed_files list is correctly populated from mtime detection

### G. Flag Behavior Tests
   - Test verbose flag behavior
   - Test quiet flag behavior

### H. Edge Cases
   - Test with non-existent prompt/code/program files (paths exist but files may be missing)
   - Test JSON parsing with nested objects
   - Test JSON parsing with extra text before/after JSON
   - Test changed_files calculation with files outside project root

## Testing Approach:
- Unit tests with mocking of external dependencies (load_prompt_template, run_agentic_task)
- Use temporary directories for file system operations
- Mock time-dependent operations for reproducibility
- Test isolation through fixtures and proper teardown

## Why Unit Tests (not Z3):
The code involves:
- I/O operations (file reading/writing, mtime checking)
- External CLI tool invocation
- String parsing and JSON extraction
- Orchestration logic

These are not mathematical properties that Z3 can verify. Unit tests with
mocking are the appropriate testing strategy for this integration-focused code.
"""

import json
import time
from pathlib import Path
from unittest.mock import MagicMock, Mock, patch

import pytest

# Import the function under test using the actual module path
from pdd.agentic_verify import run_agentic_verify


# ============================================================================
# FIXTURES
# ============================================================================

@pytest.fixture
def temp_project_dir(tmp_path):
    """Create a temporary project directory with required files."""
    project_dir = tmp_path / "project"
    project_dir.mkdir()
    
    # Create required files
    prompt_file = project_dir / "prompt.txt"
    prompt_file.write_text("Test prompt content")
    
    code_file = project_dir / "code.py"
    code_file.write_text("# Test code")
    
    program_file = project_dir / "program.py"
    program_file.write_text("# Test program")
    
    verification_log_file = project_dir / "verification.log"
    verification_log_file.write_text("Previous verification attempts...")
    
    return project_dir


@pytest.fixture
def mock_template():
    """Return a mock template string."""
    return """You are fixing verification failure.
Prompt: {prompt_path}
Code: {code_path}
Program: {program_path}
Root: {project_root}
Previous: {previous_attempts}"""


@pytest.fixture
def valid_json_response():
    """Return a valid JSON response from agent."""
    return {
        "success": True,
        "message": "Fixed the issue successfully",
        "cost": 0.025,
        "model": "claude-3",
        "changed_files": ["code.py", "program.py"]
    }


# ============================================================================
# A. TEMPLATE LOADING TESTS
# ============================================================================

def test_run_agentic_verify_template_load_failure(temp_project_dir):
    """Test that function fails gracefully when template cannot be loaded."""
    with patch('pdd.agentic_verify.load_prompt_template', return_value=None):
        with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
            result = run_agentic_verify(
                prompt_file=temp_project_dir / "prompt.txt",
                code_file=temp_project_dir / "code.py",
                program_file=temp_project_dir / "program.py",
                verification_log_file=temp_project_dir / "verification.log",
                quiet=True
            )
    
    success, message, cost, model, changed_files = result
    assert success is False
    assert "Failed to load prompt template" in message
    assert cost == 0.0
    assert model == "unknown"
    assert changed_files == []


def test_run_agentic_verify_template_loads_successfully(temp_project_dir, mock_template):
    """Test that template is loaded and used correctly."""
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template) as mock_load:
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, '{"success": true, "message": "ok"}', 0.01, "test-model")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    # Verify template was loaded with correct name
    mock_load.assert_called_once_with("agentic_verify_explore_LLM")
    
    success, message, cost, model, changed_files = result
    # Should succeed since JSON was valid
    assert success is True


# ============================================================================
# B. VERIFICATION LOG HANDLING TESTS
# ============================================================================

def test_run_agentic_verify_with_existing_log(temp_project_dir, mock_template):
    """Test that existing verification log is read and included in instruction."""
    log_content = "Attempt 1: Failed\nAttempt 2: Failed"
    (temp_project_dir / "verification.log").write_text(log_content)
    
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, '{"success": true, "message": "ok"}', 0.01, "test")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
            
            # Verify the instruction includes the log content
            call_args = mock_agent.call_args
            instruction = call_args[1]['instruction']
            assert log_content in instruction


def test_run_agentic_verify_with_missing_log(temp_project_dir, mock_template):
    """Test that missing verification log uses default message."""
    non_existent_log = temp_project_dir / "nonexistent.log"
    
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, '{"success": true, "message": "ok"}', 0.01, "test")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=non_existent_log,
                    quiet=True
                )
            
            call_args = mock_agent.call_args
            instruction = call_args[1]['instruction']
            assert "No previous verification logs found" in instruction


# ============================================================================
# C. AGENT EXECUTION SUCCESS TESTS
# ============================================================================

def test_run_agentic_verify_valid_json_response(temp_project_dir, mock_template, valid_json_response):
    """Test successful execution with valid JSON response."""
    json_output = json.dumps(valid_json_response)
    
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, json_output, 0.025, "claude-3")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    success, message, cost, model, changed_files = result
    assert success is True
    assert message == "Fixed the issue successfully"
    assert cost == 0.025
    assert model == "claude-3"


def test_run_agentic_verify_json_in_markdown(temp_project_dir, mock_template, valid_json_response):
    """Test JSON extraction from markdown code blocks."""
    markdown_output = f"Here's the result:\n```json\n{json.dumps(valid_json_response)}\n```\n"
    
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, markdown_output, 0.01, "test")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    success, message, cost, model, changed_files = result
    assert success is True
    assert message == "Fixed the issue successfully"


def test_run_agentic_verify_raw_json_with_extra_text(temp_project_dir, mock_template, valid_json_response):
    """Test JSON extraction when surrounded by extra text."""
    output_with_text = f"Starting task...\n{json.dumps(valid_json_response)}\nTask complete."
    
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, output_with_text, 0.01, "test")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    success, message, cost, model, changed_files = result
    assert success is True


def test_run_agentic_verify_invalid_json(temp_project_dir, mock_template):
    """Test handling of invalid JSON in agent output."""
    invalid_output = "This is not JSON at all"
    
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, invalid_output, 0.01, "test")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    success, message, cost, model, changed_files = result
    # Should fail because JSON couldn't be parsed
    assert success is False
    assert message == invalid_output  # Falls back to raw output


def test_run_agentic_verify_malformed_json(temp_project_dir, mock_template):
    """Test handling of malformed JSON."""
    malformed = '{"success": true, "message": "incomplete'
    
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, malformed, 0.01, "test")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    success, message, cost, model, changed_files = result
    assert success is False


# ============================================================================
# D. AGENT EXECUTION FAILURE TESTS
# ============================================================================

def test_run_agentic_verify_agent_task_fails(temp_project_dir, mock_template):
    """Test when agent task fails completely."""
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (False, "Agent failed to execute", 0.0, "none")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    success, message, cost, model, changed_files = result
    assert success is False


def test_run_agentic_verify_agent_reports_failure(temp_project_dir, mock_template):
    """Test when agent runs but reports failure in JSON."""
    failure_response = {
        "success": False,
        "message": "Could not fix the issue",
        "cost": 0.01,
        "model": "test",
        "changed_files": []
    }
    
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, json.dumps(failure_response), 0.01, "test")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    success, message, cost, model, changed_files = result
    assert success is False
    assert message == "Could not fix the issue"


# ============================================================================
# E. FILE CHANGE DETECTION TESTS
# ============================================================================

def test_run_agentic_verify_detects_modified_files(temp_project_dir, mock_template):
    """Test detection of modified files through mtime changes."""
    code_file = temp_project_dir / "code.py"
    original_mtime = code_file.stat().st_mtime
    
    def modify_file(*args, **kwargs):
        # Simulate file modification during agent execution
        time.sleep(0.01)  # Ensure time difference
        code_file.write_text("# Modified code")
        return (True, '{"success": true, "message": "ok"}', 0.01, "test")
    
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task', side_effect=modify_file):
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=code_file,
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    success, message, cost, model, changed_files = result
    assert "code.py" in changed_files


def test_run_agentic_verify_detects_new_files(temp_project_dir, mock_template):
    """Test detection of newly created files."""
    new_file = temp_project_dir / "new_file.py"
    
    def create_file(*args, **kwargs):
        new_file.write_text("# New file")
        return (True, '{"success": true, "message": "ok"}', 0.01, "test")
    
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task', side_effect=create_file):
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    success, message, cost, model, changed_files = result
    assert "new_file.py" in changed_files


def test_run_agentic_verify_no_file_changes(temp_project_dir, mock_template):
    """Test when no files are changed during execution."""
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, '{"success": true, "message": "ok"}', 0.01, "test")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    success, message, cost, model, changed_files = result
    assert changed_files == []


def test_run_agentic_verify_ignores_git_directory(temp_project_dir, mock_template):
    """Test that files in .git directory are ignored."""
    git_dir = temp_project_dir / ".git"
    git_dir.mkdir()
    git_file = git_dir / "config"
    
    def modify_git_file(*args, **kwargs):
        git_file.write_text("git config")
        return (True, '{"success": true, "message": "ok"}', 0.01, "test")
    
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task', side_effect=modify_git_file):
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    success, message, cost, model, changed_files = result
    # Git files should be ignored
    assert not any(".git" in f for f in changed_files)


# ============================================================================
# F. RETURN VALUE TESTS
# ============================================================================

def test_run_agentic_verify_return_tuple_structure(temp_project_dir, mock_template):
    """Test that return value has correct 5-tuple structure."""
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, '{"success": true, "message": "ok"}', 0.042, "gpt-4")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    assert isinstance(result, tuple)
    assert len(result) == 5
    
    success, message, cost, model, changed_files = result
    assert isinstance(success, bool)
    assert isinstance(message, str)
    assert isinstance(cost, float)
    assert isinstance(model, str)
    assert isinstance(changed_files, list)


def test_run_agentic_verify_passes_through_cost_and_model(temp_project_dir, mock_template):
    """Test that cost and model from agent are passed through correctly."""
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, '{"success": true, "message": "ok"}', 0.123, "claude-opus")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    success, message, cost, model, changed_files = result
    assert cost == 0.123
    assert model == "claude-opus"


# ============================================================================
# G. FLAG BEHAVIOR TESTS
# ============================================================================

def test_run_agentic_verify_verbose_flag(temp_project_dir, mock_template):
    """Test that verbose flag is passed to agent task."""
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, '{"success": true, "message": "ok"}', 0.01, "test")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    verbose=True,
                    quiet=False
                )
            
            call_kwargs = mock_agent.call_args[1]
            assert call_kwargs['verbose'] is True


def test_run_agentic_verify_quiet_flag(temp_project_dir, mock_template, capsys):
    """Test that quiet flag suppresses output."""
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, '{"success": true, "message": "ok"}', 0.01, "test")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
            
            call_kwargs = mock_agent.call_args[1]
            assert call_kwargs['quiet'] is True


# ============================================================================
# H. EDGE CASES
# ============================================================================

def test_run_agentic_verify_nested_json_objects(temp_project_dir, mock_template):
    """Test parsing of nested JSON structures."""
    nested_json = {
        "success": True,
        "message": "Fixed",
        "cost": 0.01,
        "model": "test",
        "changed_files": ["a.py", "b.py"],
        "metadata": {
            "attempts": 3,
            "duration": 45.2
        }
    }
    
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, json.dumps(nested_json), 0.01, "test")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    success, message, cost, model, changed_files = result
    assert success is True
    assert message == "Fixed"


def test_run_agentic_verify_with_subdirectories(temp_project_dir, mock_template):
    """Test file change detection in subdirectories."""
    subdir = temp_project_dir / "src"
    subdir.mkdir()
    subfile = subdir / "module.py"
    
    def create_subfile(*args, **kwargs):
        subfile.write_text("# Module")
        return (True, '{"success": true, "message": "ok"}', 0.01, "test")
    
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task', side_effect=create_subfile):
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    success, message, cost, model, changed_files = result
    assert any("src" in f and "module.py" in f for f in changed_files)


def test_run_agentic_verify_agent_params_passed_correctly(temp_project_dir, mock_template):
    """Test that all parameters are passed correctly to run_agentic_task."""
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, '{"success": true, "message": "ok"}', 0.01, "test")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    verbose=True,
                    quiet=False
                )
            
            call_kwargs = mock_agent.call_args[1]
            assert 'instruction' in call_kwargs
            assert call_kwargs['cwd'] == temp_project_dir
            assert call_kwargs['verbose'] is True
            assert call_kwargs['quiet'] is False
            assert call_kwargs['label'] == "verify-explore"


def test_run_agentic_verify_json_with_unicode(temp_project_dir, mock_template):
    """Test JSON parsing with unicode characters."""
    unicode_json = {
        "success": True,
        "message": "Fixed issue with émojis 🎉 and spëcial chars",
        "cost": 0.01,
        "model": "test",
        "changed_files": []
    }
    
    with patch('pdd.agentic_verify.load_prompt_template', return_value=mock_template):
        with patch('pdd.agentic_verify.run_agentic_task') as mock_agent:
            mock_agent.return_value = (True, json.dumps(unicode_json, ensure_ascii=False), 0.01, "test")
            with patch('pdd.agentic_verify.Path.cwd', return_value=temp_project_dir):
                result = run_agentic_verify(
                    prompt_file=temp_project_dir / "prompt.txt",
                    code_file=temp_project_dir / "code.py",
                    program_file=temp_project_dir / "program.py",
                    verification_log_file=temp_project_dir / "verification.log",
                    quiet=True
                )
    
    success, message, cost, model, changed_files = result
    assert success is True
    assert "émojis" in message
    assert "🎉" in message