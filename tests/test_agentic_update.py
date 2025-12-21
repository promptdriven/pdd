import os
import sys
import time
from pathlib import Path
from typing import List, Tuple
from unittest.mock import MagicMock, patch

import pytest

# Import the module under test
from pdd.agentic_update import run_agentic_update

# Constants for mocking
MOCK_TEMPLATE = "Update prompt {prompt_path} for code {code_path} using tests {test_paths}"

@pytest.fixture
def mock_dependencies():
    """
    Fixture to mock external dependencies:
    - get_available_agents
    - load_prompt_template
    - run_agentic_task
    - console (to suppress output)
    """
    with patch("pdd.agentic_update.get_available_agents") as mock_get_agents, \
         patch("pdd.agentic_update.load_prompt_template") as mock_load_template, \
         patch("pdd.agentic_update.run_agentic_task") as mock_run_task, \
         patch("pdd.agentic_update.console") as mock_console:
        
        # Default happy path setup
        mock_get_agents.return_value = ["claude"]
        mock_load_template.return_value = MOCK_TEMPLATE
        mock_run_task.return_value = (True, "Task completed", 0.01, "claude")
        
        yield mock_get_agents, mock_load_template, mock_run_task, mock_console

@pytest.fixture
def project_root_mock(tmp_path):
    """
    Mock PROJECT_ROOT to point to tmp_path for file discovery tests.
    This ensures that relative path calculations in the module work against our temp dir.
    """
    with patch("pdd.agentic_update.PROJECT_ROOT", tmp_path):
        yield tmp_path

def create_dummy_file(path: Path, content: str = ""):
    """Helper to create a file and set its mtime to the past."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    # Set mtime to the past to ensure updates are detectable
    old_time = time.time() - 100
    os.utime(path, (old_time, old_time))

def test_missing_prompt_file(mock_dependencies, tmp_path):
    """Test failure when prompt file does not exist."""
    prompt_file = tmp_path / "non_existent_prompt.md"
    code_file = tmp_path / "code.py"
    create_dummy_file(code_file)
    
    success, msg, cost, _, _ = run_agentic_update(str(prompt_file), str(code_file), quiet=True)
    
    assert not success
    assert "Prompt file not found" in msg
    assert cost == 0.0

def test_missing_code_file(mock_dependencies, tmp_path):
    """Test failure when code file does not exist."""
    prompt_file = tmp_path / "prompt.md"
    code_file = tmp_path / "non_existent_code.py"
    create_dummy_file(prompt_file)
    
    success, msg, cost, _, _ = run_agentic_update(str(prompt_file), str(code_file), quiet=True)
    
    assert not success
    assert "Code file not found" in msg

def test_no_agents_available(mock_dependencies, tmp_path):
    """Test failure when no agents are available."""
    mock_get_agents, _, _, _ = mock_dependencies
    mock_get_agents.return_value = []
    
    prompt_file = tmp_path / "prompt.md"
    code_file = tmp_path / "code.py"
    create_dummy_file(prompt_file)
    create_dummy_file(code_file)
    
    success, msg, cost, _, _ = run_agentic_update(str(prompt_file), str(code_file), quiet=True)
    
    assert not success
    assert "No agentic CLI available" in msg

def test_missing_explicit_test_file(mock_dependencies, tmp_path):
    """Test failure when an explicitly provided test file is missing."""
    prompt_file = tmp_path / "prompt.md"
    code_file = tmp_path / "code.py"
    create_dummy_file(prompt_file)
    create_dummy_file(code_file)
    
    missing_test = tmp_path / "tests" / "missing_test.py"
    
    success, msg, _, _, _ = run_agentic_update(
        str(prompt_file), 
        str(code_file), 
        test_files=[missing_test], 
        quiet=True
    )
    
    assert not success
    assert "Test file(s) not found" in msg
    assert str(missing_test) in msg

def test_template_loading_failure(mock_dependencies, tmp_path):
    """Test failure when template cannot be loaded."""
    _, mock_load_template, _, _ = mock_dependencies
    mock_load_template.return_value = None
    
    prompt_file = tmp_path / "prompt.md"
    code_file = tmp_path / "code.py"
    create_dummy_file(prompt_file)
    create_dummy_file(code_file)
    
    success, msg, _, _, _ = run_agentic_update(str(prompt_file), str(code_file), quiet=True)
    
    assert not success
    assert "could not be loaded" in msg

def test_template_formatting_error(mock_dependencies, tmp_path):
    """Test failure when template formatting fails (e.g. missing keys)."""
    _, mock_load_template, _, _ = mock_dependencies
    mock_load_template.return_value = "Invalid template with {missing_key}"
    
    prompt_file = tmp_path / "prompt.md"
    code_file = tmp_path / "code.py"
    create_dummy_file(prompt_file)
    create_dummy_file(code_file)
    
    success, msg, _, _, _ = run_agentic_update(str(prompt_file), str(code_file), quiet=True)
    
    assert not success
    assert "Error formatting" in msg

def test_agent_task_exception(mock_dependencies, tmp_path):
    """Test handling of exception during agent task execution."""
    _, _, mock_run_task, _ = mock_dependencies
    mock_run_task.side_effect = Exception("Agent crashed")
    
    prompt_file = tmp_path / "prompt.md"
    code_file = tmp_path / "code.py"
    create_dummy_file(prompt_file)
    create_dummy_file(code_file)
    
    success, msg, _, _, _ = run_agentic_update(str(prompt_file), str(code_file), quiet=True)
    
    assert not success
    assert "Agentic task failed" in msg
    assert "Agent crashed" in msg

def test_success_flow_with_modification(mock_dependencies, project_root_mock):
    """
    Test successful update where prompt file is modified.
    Uses project_root_mock to ensure relative paths work correctly.
    """
    _, _, mock_run_task, _ = mock_dependencies
    
    # Setup files in the mocked project root
    prompt_file = project_root_mock / "prompt.md"
    code_file = project_root_mock / "src" / "main.py"
    test_file = project_root_mock / "src" / "test_main.py" # Should be auto-discovered
    
    create_dummy_file(prompt_file)
    create_dummy_file(code_file)
    create_dummy_file(test_file)
    
    # Define side effect to modify prompt file
    def agent_action(*args, **kwargs):
        # Simulate agent modifying the prompt file
        prompt_file.write_text("Updated content")
        return (True, "Updated prompt", 0.05, "claude-3-opus")
    
    mock_run_task.side_effect = agent_action
    
    success, msg, cost, provider, changed = run_agentic_update(
        str(prompt_file), 
        str(code_file), 
        quiet=True
    )
    
    assert success is True
    assert "Prompt file updated successfully" in msg
    assert cost == 0.05
    assert provider == "claude-3-opus"
    assert str(prompt_file) in changed
    
    # Verify instruction contained correct paths
    call_args = mock_run_task.call_args
    instruction = call_args[1]['instruction']
    assert str(prompt_file.relative_to(project_root_mock)) in instruction
    assert str(code_file.relative_to(project_root_mock)) in instruction
    assert str(test_file.relative_to(project_root_mock)) in instruction

def test_success_flow_no_modification(mock_dependencies, project_root_mock):
    """Test agent runs successfully but does not modify the prompt file."""
    _, _, mock_run_task, _ = mock_dependencies
    
    prompt_file = project_root_mock / "prompt.md"
    code_file = project_root_mock / "main.py"
    create_dummy_file(prompt_file)
    create_dummy_file(code_file)
    
    # Agent does nothing to files
    mock_run_task.return_value = (True, "No changes needed", 0.02, "gemini")
    
    success, msg, cost, _, changed = run_agentic_update(
        str(prompt_file), 
        str(code_file), 
        quiet=True
    )
    
    assert success is False
    assert "did not modify the prompt file" in msg
    assert len(changed) == 0

def test_explicit_test_files(mock_dependencies, project_root_mock):
    """Test using explicitly provided test files."""
    _, _, mock_run_task, _ = mock_dependencies
    
    prompt_file = project_root_mock / "prompt.md"
    code_file = project_root_mock / "main.py"
    explicit_test = project_root_mock / "custom_tests" / "test_custom.py"
    
    create_dummy_file(prompt_file)
    create_dummy_file(code_file)
    create_dummy_file(explicit_test)
    
    # Side effect to modify prompt
    def agent_action(*args, **kwargs):
        prompt_file.write_text("Updated")
        return (True, "Done", 0.0, "codex")
    mock_run_task.side_effect = agent_action
    
    success, _, _, _, _ = run_agentic_update(
        str(prompt_file), 
        str(code_file), 
        test_files=[explicit_test],
        quiet=True
    )
    
    assert success is True
    
    # Verify instruction contains explicit test path
    instruction = mock_run_task.call_args[1]['instruction']
    assert str(explicit_test.relative_to(project_root_mock)) in instruction

def test_detect_changed_files_logic(mock_dependencies, project_root_mock):
    """
    Test that _detect_changed_files logic works correctly via the main function.
    We simulate file creation and modification.
    """
    _, _, mock_run_task, _ = mock_dependencies
    
    prompt_file = project_root_mock / "prompt.md"
    code_file = project_root_mock / "main.py"
    create_dummy_file(prompt_file)
    create_dummy_file(code_file)
    
    # Use a filename that matches the test discovery pattern so it gets detected.
    # The code only scans for changes in prompt, code, and discoverable tests.
    new_file = project_root_mock / "test_main_new.py"
    
    def agent_action(*args, **kwargs):
        # Modify prompt
        prompt_file.write_text("Modified")
        # Create new file
        new_file.write_text("New content")
        return (True, "Changes made", 0.1, "claude")
    
    mock_run_task.side_effect = agent_action
    
    success, _, _, _, changed_files = run_agentic_update(
        str(prompt_file), 
        str(code_file), 
        quiet=True
    )
    
    assert success is True
    assert str(prompt_file) in changed_files
    assert str(new_file) in changed_files
    assert str(code_file) not in changed_files

def test_auto_discovery_locations(mock_dependencies, project_root_mock):
    """
    Test that tests are discovered in:
    1. tests/ relative to code
    2. same dir as code
    3. project root tests/
    """
    _, _, mock_run_task, _ = mock_dependencies
    
    prompt_file = project_root_mock / "prompt.md"
    # Structure:
    # src/code.py
    # src/tests/test_code_1.py
    # src/test_code_2.py
    # tests/test_code_3.py
    
    src_dir = project_root_mock / "src"
    src_dir.mkdir()
    (src_dir / "tests").mkdir()
    (project_root_mock / "tests").mkdir()
    
    code_file = src_dir / "code.py"
    test1 = src_dir / "tests" / "test_code_1.py"
    test2 = src_dir / "test_code_2.py"
    test3 = project_root_mock / "tests" / "test_code_3.py"
    
    create_dummy_file(prompt_file)
    create_dummy_file(code_file)
    create_dummy_file(test1)
    create_dummy_file(test2)
    create_dummy_file(test3)
    
    # We just want to check the instruction passed to the agent
    run_agentic_update(str(prompt_file), str(code_file), quiet=True)
    
    instruction = mock_run_task.call_args[1]['instruction']
    
    # Check that all 3 tests are in the instruction
    assert str(test1.relative_to(project_root_mock)) in instruction
    assert str(test2.relative_to(project_root_mock)) in instruction
    assert str(test3.relative_to(project_root_mock)) in instruction