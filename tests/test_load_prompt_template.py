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

    # Capture the printed error message
    captured = capsys.readouterr()
    assert "[red]PDD_PATH environment variable is not set[/red]" in captured.out

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
        
        # Assert that Path.exists was called correctly
        mock_exists.assert_called_once_with()
        
        # Capture the printed error message
        captured = capsys.readouterr()
        assert f"[red]Prompt file not found: {prompt_path}[/red]" in captured.out

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
            assert f"[red]Error reading prompt file {prompt_name}: Unable to read file[/red]" in captured.out

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
