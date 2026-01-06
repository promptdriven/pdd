# tests/test_load_prompt_template.py

import os
import pytest
from unittest.mock import patch, mock_open
from pathlib import Path

# Assuming the module is located at pdd/load_prompt_template.py
from pdd.load_prompt_template import load_prompt_template

# Test Case 1: Successful loading of a prompt template
def test_load_prompt_template_success(monkeypatch):
    prompt_name = "example_prompt"
    expected_content = "This is a sample prompt template."

    # Mock the PDD_PATH environment variable
    monkeypatch.setenv("PDD_PATH", "/fake/project/path")

    # Construct the expected prompt file path
    prompt_path = Path("/fake/project/path") / "prompts" / f"{prompt_name}.prompt"

    with patch.object(Path, 'exists', return_value=True) as mock_exists:
        with patch("builtins.open", mock_open(read_data=expected_content)) as mock_file:
            result = load_prompt_template(prompt_name)
            
            # Assert that the function returns the expected content
            assert result == expected_content
            
            # Assert that Path.exists was called correctly
            mock_exists.assert_called_once_with()
            
            # Assert that the file was opened correctly
            mock_file.assert_called_once_with(prompt_path, 'r', encoding='utf-8')

# Test Case 2: PDD_PATH environment variable is not set
def test_load_prompt_template_missing_pdd_path(monkeypatch, capsys):
    prompt_name = "example_prompt"

    # Ensure PDD_PATH is not set
    monkeypatch.delenv("PDD_PATH", raising=False)

    result = load_prompt_template(prompt_name)

    # Assert that the function returns None
    assert result is None

    # Capture the printed error message (should list tried candidate locations)
    captured = capsys.readouterr()
    assert "Prompt file not found in any candidate locations" in captured.out

# Test Case 3: Prompt file does not exist
def test_load_prompt_template_file_not_found(monkeypatch, capsys):
    prompt_name = "nonexistent_prompt"

    # Mock the PDD_PATH environment variable
    monkeypatch.setenv("PDD_PATH", "/fake/project/path")

    # Construct the expected prompt file path
    prompt_path = Path("/fake/project/path") / "prompts" / f"{prompt_name}.prompt"

    with patch.object(Path, 'exists', return_value=False) as mock_exists:
        result = load_prompt_template(prompt_name)
        
        # Assert that the function returns None
        assert result is None
        
        # Assert that Path.exists was called for each candidate location
        # We now check 2 paths per candidate root (PDD_PATH, repo root, CWD):
        # - <root>/prompts/<name>.prompt
        # - <root>/pdd/prompts/<name>.prompt
        # So total should be 3 roots * 2 paths = 6 calls
        assert mock_exists.call_count == 6
        
        # Capture the printed error message and ensure it includes the PDD_PATH-based candidate
        captured = capsys.readouterr()
        assert "Prompt file not found in any candidate locations" in captured.out
        assert str(prompt_path) in captured.out

# Test Case 4: IOError when reading the prompt file
def test_load_prompt_template_io_error(monkeypatch, capsys):
    prompt_name = "io_error_prompt"

    # Mock the PDD_PATH environment variable
    monkeypatch.setenv("PDD_PATH", "/fake/project/path")

    # Construct the expected prompt file path
    prompt_path = Path("/fake/project/path") / "prompts" / f"{prompt_name}.prompt"

    with patch.object(Path, 'exists', return_value=True):
        with patch("builtins.open", mock_open()) as mock_file:
            # Configure the mock to raise an IOError when open is called
            mock_file.side_effect = IOError("Unable to read file")
            
            result = load_prompt_template(prompt_name)
            
            # Assert that the function returns None
            assert result is None
            
            # Assert that the file was attempted to be opened correctly
            mock_file.assert_called_once_with(prompt_path, 'r', encoding='utf-8')
            
            # Capture the printed error message
            captured = capsys.readouterr()
            assert f"Error reading prompt file {prompt_name}: Unable to read file" in captured.out

# Additional Test Case: Empty prompt name
def test_load_prompt_template_empty_prompt_name(monkeypatch, capsys):
    prompt_name = ""

    # Mock the PDD_PATH environment variable
    monkeypatch.setenv("PDD_PATH", "/fake/project/path")

    # Construct the expected prompt file path
    prompt_path = Path("/fake/project/path") / "prompts" / ".prompt"

    with patch.object(Path, 'exists', return_value=True):
        with patch("builtins.open", mock_open(read_data="")) as mock_file:
            result = load_prompt_template(prompt_name)
            
            # Assert that the function returns the empty string
            assert result == ""
            
            # Assert that the file was opened correctly
            mock_file.assert_called_once_with(prompt_path, 'r', encoding='utf-8')
            
            # Capture the printed success message
            captured = capsys.readouterr()
            assert f"Successfully loaded prompt: {prompt_name}" in captured.out

# Additional Test Case: Non-string prompt name
def test_load_prompt_template_non_string_prompt_name(monkeypatch, capsys):
    prompt_name = None  # Non-string input

    # Mock the PDD_PATH environment variable
    monkeypatch.setenv("PDD_PATH", "/fake/project/path")

    with patch("builtins.open", mock_open()):
        result = load_prompt_template(prompt_name)
        
        # Assert that the function returns None due to TypeError
        assert result is None
        
        # Capture the printed error message
        captured = capsys.readouterr()
        assert "Unexpected error loading prompt template" in captured.out

# Test Case: Simulates installed package scenario where prompts should be in pdd/prompts/
def test_load_prompt_template_installed_package_location(monkeypatch, capsys, tmp_path):
    """
    Reproduces the issue where load_prompt_template fails to find prompts
    in an installed package location. This happens because the function
    doesn't check for prompts in the pdd/prompts/ subdirectory within
    the installed package.
    
    Error scenario from the bug report:
    - PDD_PATH is not set (user doesn't have local development setup)
    - CWD doesn't contain prompts
    - The package is installed at a location like:
      /Users/user/.local/share/uv/tools/pdd-cli/lib/python3.13/site-packages/
    - Prompts should be at:
      site-packages/pdd/prompts/unfinished_prompt_LLM.prompt
    - But the code looks for them at:
      site-packages/prompts/unfinished_prompt_LLM.prompt
    """
    prompt_name = "unfinished_prompt_LLM"
    expected_content = "This is the unfinished prompt template."
    
    # Simulate an installed package structure
    # site-packages/
    #   pdd/
    #     prompts/
    #       unfinished_prompt_LLM.prompt
    site_packages = tmp_path / "site-packages"
    pdd_package = site_packages / "pdd"
    prompts_dir = pdd_package / "prompts"
    prompts_dir.mkdir(parents=True)
    
    prompt_file = prompts_dir / f"{prompt_name}.prompt"
    prompt_file.write_text(expected_content, encoding='utf-8')
    
    # Create a fake __file__ path that simulates the installed package location
    fake_module_file = pdd_package / "path_resolution.py"
    fake_module_file.touch()

    # Ensure PDD_PATH is not set and CWD doesn't have prompts
    monkeypatch.delenv("PDD_PATH", raising=False)
    monkeypatch.setattr(Path, "cwd", lambda: tmp_path / "user_project")

    # Mock __file__ in path_resolution module (where get_default_resolver reads package_root)
    import pdd.path_resolution as pr_module
    monkeypatch.setattr(pr_module, "__file__", str(fake_module_file))
    
    # Call load_prompt_template
    result = load_prompt_template(prompt_name)
    
    # This test will FAIL with current implementation because it looks for:
    # site-packages/prompts/unfinished_prompt_LLM.prompt
    # instead of:
    # site-packages/pdd/prompts/unfinished_prompt_LLM.prompt
    
    if result is None:
        # Capture the error message to show the bug
        captured = capsys.readouterr()
        # The test is expected to fail initially, showing the bug exists
        pytest.fail(
            f"Bug reproduced: load_prompt_template failed to find prompt in installed package.\n"
            f"Expected to find: {prompt_file}\n"
            f"Error output:\n{captured.out}"
        )
    
    # Once fixed, this assertion should pass
    assert result == expected_content, f"Expected to load prompt from installed package location"
