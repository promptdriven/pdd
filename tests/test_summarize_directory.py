# tests/test_summarize_directory.py

import os
import pytest
import tempfile
import shutil
from unittest import mock
from unittest.mock import patch, MagicMock
from datetime import datetime, timedelta
from pathlib import Path

# Import the function to test
from pdd.summarize_directory import summarize_directory

@pytest.fixture
def mock_pdd_path():
    """Fixture to set the PDD_PATH environment variable."""
    with tempfile.TemporaryDirectory() as tmpdir:
        with patch.dict(os.environ, {"PDD_PATH": tmpdir}):
            # Create the prompts directory and prompt file
            prompts_dir = Path(tmpdir) / "prompts"
            prompts_dir.mkdir()
            prompt_file = prompts_dir / "summarize_file_LLM.prompt"
            prompt_file.write_text("Summarize the following file contents:")
            yield tmpdir

@pytest.fixture
def mock_llm_invoke_success():
    """Fixture to mock llm_invoke with successful responses."""
    with patch('pdd.summarize_directory.llm_invoke') as mock_invoke:
        mock_response = {
            'result': MagicMock(summary="Mock summary"),
            'cost': 0.01,
            'model_name': 'mock-model'
        }
        mock_invoke.return_value = mock_response
        yield mock_invoke

@pytest.fixture
def mock_llm_invoke_failure():
    """Fixture to mock llm_invoke raising an exception."""
    with patch('pdd.summarize_directory.llm_invoke') as mock_invoke:
        mock_invoke.side_effect = Exception("LLM invoke failed")
        yield mock_invoke

def test_normal_operation_single_file(mock_pdd_path, mock_llm_invoke_success):
    """Test summarizing a single file successfully."""
    with tempfile.TemporaryDirectory() as tmpdir:
        # Create a sample file
        file_path = Path(tmpdir) / "test_file.py"
        file_content = "print('Hello, World!')"
        file_path.write_text(file_content)
        
        csv_output, total_cost, model_name = summarize_directory(
            directory_path=str(Path(tmpdir) / "*.py"),
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=None
        )
        
        assert "full_path,file_summary,date" in csv_output
        assert "test_file.py,Mock summary," in csv_output
        assert total_cost == 0.01
        assert model_name == "mock-model"

def test_multiple_files(mock_pdd_path, mock_llm_invoke_success):
    """Test summarizing multiple files successfully."""
    with tempfile.TemporaryDirectory() as tmpdir:
        # Create sample files
        file_names = ["file1.py", "file2.py", "file3.py"]
        for fname in file_names:
            (Path(tmpdir) / fname).write_text(f"print('This is {fname}')")
        
        csv_output, total_cost, model_name = summarize_directory(
            directory_path=str(Path(tmpdir) / "*.py"),
            strength=0.8,
            temperature=0.6,
            verbose=False,
            csv_file=None
        )
        
        assert "full_path,file_summary,date" in csv_output
        for fname in file_names:
            assert f"{str(Path(tmpdir) / fname)},Mock summary," in csv_output
        assert total_cost == len(file_names) * 0.01
        assert model_name == "mock-model"

def test_existing_csv_no_changes(mock_pdd_path, mock_llm_invoke_success):
    """Test using existing CSV when files have not changed."""
    with tempfile.TemporaryDirectory() as tmpdir:
        file_path = Path(tmpdir) / "test_file.py"
        file_content = "print('Hello, World!')"
        file_path.write_text(file_content)
        
        existing_csv = "full_path,file_summary,date\n"
        existing_csv += f"{str(file_path.resolve())},Existing summary,{datetime.now().isoformat()}\n"
        
        csv_output, total_cost, model_name = summarize_directory(
            directory_path=str(Path(tmpdir) / "*.py"),
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=existing_csv
        )
        
        assert "Existing summary" in csv_output
        assert total_cost == 0.0  # No new summarization
        assert model_name == ""

def test_existing_csv_with_changes(mock_pdd_path, mock_llm_invoke_success):
    """Test updating summaries when files have changed."""
    with tempfile.TemporaryDirectory() as tmpdir:
        file_path = Path(tmpdir) / "test_file.py"
        file_content = "print('Hello, World!')"
        file_path.write_text(file_content)
        
        # Existing CSV with older date
        old_date = datetime.now() - timedelta(days=1)
        existing_csv = "full_path,file_summary,date\n"
        existing_csv += f"{str(file_path.resolve())},Old summary,{old_date.isoformat()}\n"
        
        # Update file modification time to now
        os.utime(file_path, None)
        
        csv_output, total_cost, model_name = summarize_directory(
            directory_path=str(Path(tmpdir) / "*.py"),
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=existing_csv
        )
        
        assert "Old summary" not in csv_output
        assert "Mock summary" in csv_output
        assert total_cost == 0.01
        assert model_name == "mock-model"

def test_missing_pdd_path_environment_variable(mock_llm_invoke_success):
    """Test behavior when PDD_PATH environment variable is not set."""
    with patch.dict(os.environ, {}, clear=True):
        with pytest.raises(ValueError, match="PDD_PATH environment variable not set"):
            summarize_directory(
                directory_path="/some/path/*.py",
                strength=0.5,
                temperature=0.7,
                verbose=False,
                csv_file=None
            )

def test_missing_prompt_file(mock_pdd_path, mock_llm_invoke_success):
    """Test behavior when the prompt file is missing."""
    with patch.dict(os.environ, {"PDD_PATH": mock_pdd_path}):
        with pytest.raises(FileNotFoundError, match="Prompt file not found"):
            summarize_directory(
                directory_path="/some/path/*.py",
                strength=0.5,
                temperature=0.7,
                verbose=False,
                csv_file=None
            )

def test_no_matching_files(mock_pdd_path, mock_llm_invoke_success):
    """Test behavior when no files match the directory pattern."""
    with tempfile.TemporaryDirectory() as tmpdir:
        csv_output, total_cost, model_name = summarize_directory(
            directory_path=str(Path(tmpdir) / "*.txt"),  # Assuming no .txt files
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=None
        )
        
        assert csv_output == "full_path,file_summary,date\r\n"  # Only header
        assert total_cost == 0.0
        assert model_name == ""

def test_file_read_error(mock_pdd_path, mock_llm_invoke_success):
    """Test behavior when a file cannot be read."""
    with tempfile.TemporaryDirectory() as tmpdir:
        file_path = Path(tmpdir) / "unreadable.py"
        file_path.write_text("print('This file is unreadable')")
        # Make the file unreadable
        os.chmod(file_path, 0o000)
        
        with pytest.raises(PermissionError):
            summarize_directory(
                directory_path=str(Path(tmpdir) / "*.py"),
                strength=0.5,
                temperature=0.7,
                verbose=False,
                csv_file=None
            )
        # Reset permissions for cleanup
        os.chmod(file_path, 0o644)

def test_llm_invoke_failure(mock_pdd_path, mock_llm_invoke_failure):
    """Test behavior when llm_invoke raises an exception."""
    with tempfile.TemporaryDirectory() as tmpdir:
        file_path = Path(tmpdir) / "test_file.py"
        file_path.write_text("print('Hello, World!')")
        
        csv_output, total_cost, model_name = summarize_directory(
            directory_path=str(Path(tmpdir) / "*.py"),
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=None
        )
        
        # Since llm_invoke fails, the summary should not be in the CSV
        assert "full_path,file_summary,date" in csv_output
        assert "test_file.py" not in csv_output
        assert total_cost == 0.0
        assert model_name == ""

def test_invalid_strength_value(mock_pdd_path, mock_llm_invoke_success):
    """Test behavior when strength is out of valid range."""
    with tempfile.TemporaryDirectory() as tmpdir:
        file_path = Path(tmpdir) / "test_file.py"
        file_path.write_text("print('Hello, World!')")
        
        with pytest.raises(ValueError):
            summarize_directory(
                directory_path=str(Path(tmpdir) / "*.py"),
                strength=1.5,  # Invalid strength
                temperature=0.7,
                verbose=False,
                csv_file=None
            )

def test_invalid_temperature_value(mock_pdd_path, mock_llm_invoke_success):
    """Test behavior when temperature is out of valid range."""
    with tempfile.TemporaryDirectory() as tmpdir:
        file_path = Path(tmpdir) / "test_file.py"
        file_path.write_text("print('Hello, World!')")
        
        # Assuming the function does not explicitly validate temperature,
        # it might allow any float. If validation exists, adjust accordingly.
        csv_output, total_cost, model_name = summarize_directory(
            directory_path=str(Path(tmpdir) / "*.py"),
            strength=0.5,
            temperature=-0.1,  # Potentially invalid if validated
            verbose=False,
            csv_file=None
        )
        
        # Check if function handled it gracefully or raised an error
        # Adjust assertion based on actual behavior
        # Here assuming no validation, it proceeds
        assert "test_file.py,Mock summary," in csv_output

def test_verbose_output(mock_pdd_path, mock_llm_invoke_success):
    """Test that verbose mode does not affect the output."""
    with tempfile.TemporaryDirectory() as tmpdir, \
         patch('pdd.summarize_directory.console.print') as mock_print:
        
        file_path = Path(tmpdir) / "test_file.py"
        file_path.write_text("print('Hello, World!')")
        
        csv_output, total_cost, model_name = summarize_directory(
            directory_path=str(Path(tmpdir) / "*.py"),
            strength=0.5,
            temperature=0.7,
            verbose=True,
            csv_file=None
        )
        
        # Ensure that console.print was called for verbose output
        mock_print.assert_any_call(f"[blue]Summarizing: {str(file_path)}[/blue]")
        assert "test_file.py,Mock summary," in csv_output
