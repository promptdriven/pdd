import os
import pytest
import tempfile
import shutil
from unittest import mock
from unittest.mock import mock_open, MagicMock
from pathlib import Path
from datetime import datetime
from pdd.summarize_directory import summarize_directory, normalize_path

# Helper function to create a temporary prompt file
def create_temp_prompt_file(pdd_path, content="Prompt Template"):
    prompts_dir = Path(pdd_path) / "prompts"
    prompts_dir.mkdir(parents=True, exist_ok=True)
    prompt_file = prompts_dir / "summarize_file_LLM.prompt"
    prompt_file.write_text(content)
    return str(prompt_file)

@pytest.fixture
def mock_pdd_path():
    with tempfile.TemporaryDirectory() as tmpdir:
        yield tmpdir

@pytest.fixture
def mock_files_directory():
    with tempfile.TemporaryDirectory() as tmpdir:
        # Create some dummy files
        file1 = Path(tmpdir) / "file1.py"
        file2 = Path(tmpdir) / "file2.py"
        file1.write_text("# file1 contents")
        file2.write_text("# file2 contents")
        yield tmpdir, [str(file1), str(file2)]

@pytest.fixture
def mock_existing_csv():
    csv_content = """full_path,file_summary,date
/path/to/file1.py,Summary 1,2023-10-01T12:00:00
/path/to/file2.py,Summary 2,2023-10-02T12:00:00
"""
    return csv_content

def normalize_line_endings(text: str) -> str:
    """Normalize line endings for test comparison."""
    return text.replace('\n', '\r\n').replace('\r\r\n', '\r\n')

def test_missing_pdd_path():
    with mock.patch.dict(os.environ, {}, clear=True):
        with pytest.raises(ValueError) as excinfo:
            summarize_directory(
                directory_path="*.py",
                strength=0.5,
                temperature=0.7
            )
        assert "PDD_PATH environment variable not set" in str(excinfo.value)

def test_missing_prompt_file(mock_pdd_path):
    with mock.patch.dict(os.environ, {"PDD_PATH": mock_pdd_path}):
        with pytest.raises(FileNotFoundError) as excinfo:
            summarize_directory(
                directory_path="*.py",
                strength=0.5,
                temperature=0.7
            )
        expected_prompt_path = Path(mock_pdd_path) / "prompts" / "summarize_file_LLM.prompt"
        assert f"Prompt file not found: {expected_prompt_path}" in str(excinfo.value)

def test_no_matching_files(mock_pdd_path):
    # Create prompt file
    create_temp_prompt_file(mock_pdd_path)

    with mock.patch.dict(os.environ, {"PDD_PATH": mock_pdd_path}):
        with mock.patch("glob.glob", return_value=[]):
            csv_output, total_cost, model_name = summarize_directory(
                directory_path="*.py",
                strength=0.5,
                temperature=0.7
            )
            assert csv_output == "full_path,file_summary,date\r\n"
            assert total_cost == 0.0
            assert model_name == ""

def test_file_read_error(mock_pdd_path, mock_files_directory):
    # Create prompt file
    create_temp_prompt_file(mock_pdd_path)

    directory, files = mock_files_directory

    with mock.patch.dict(os.environ, {"PDD_PATH": mock_pdd_path}):
        with mock.patch("glob.glob", return_value=files):
            # Mock open to raise an exception when reading files
            with mock.patch("builtins.open", side_effect=Exception("Read error")):
                csv_output, total_cost, model_name = summarize_directory(
                    directory_path=f"{directory}/*.py",
                    strength=0.5,
                    temperature=0.7
                )
                # Expect empty CSV since reading files failed
                assert csv_output == "full_path,file_summary,date\r\n"
                assert total_cost == 0.0
                assert model_name == ""

def test_llm_invoke_error(mock_pdd_path, mock_files_directory):
    # Create prompt file
    create_temp_prompt_file(mock_pdd_path)

    directory, files = mock_files_directory

    with mock.patch.dict(os.environ, {"PDD_PATH": mock_pdd_path}):
        with mock.patch("glob.glob", return_value=files):
            # Mock open to read file contents normally
            m = mock_open(read_data="# file contents")
            with mock.patch("builtins.open", m):
                # Mock llm_invoke to raise an exception
                with mock.patch("pdd.summarize_directory.llm_invoke", side_effect=Exception("LLM error")):
                    csv_output, total_cost, model_name = summarize_directory(
                        directory_path=f"{directory}/*.py",
                        strength=0.5,
                        temperature=0.7
                    )
                    # Expect empty CSV since summarization failed
                    assert csv_output == "full_path,file_summary,date\r\n"
                    assert total_cost == 0.0
                    assert model_name == ""

def test_normal_operation_without_existing_csv(mock_pdd_path, mock_files_directory):
    # Create prompt file
    create_temp_prompt_file(mock_pdd_path)

    directory, files = mock_files_directory
    normalized_files = [normalize_path(f) for f in files]

    mock_llm_response = {
        'result': MagicMock(file_summary="Mock summary"),
        'cost': 0.01,
        'model_name': "MockModel"
    }

    with mock.patch.dict(os.environ, {"PDD_PATH": mock_pdd_path}):
        with mock.patch("glob.glob", return_value=files):
            m = mock_open(read_data="# file contents")
            with mock.patch("builtins.open", m):
                with mock.patch("pdd.summarize_directory.llm_invoke", return_value=mock_llm_response):
                    csv_output, total_cost, model_name = summarize_directory(
                        directory_path=f"{directory}/*.py",
                        strength=0.5,
                        temperature=0.7
                    )
                    lines = normalize_line_endings(csv_output.strip()).split('\r\n')
                    assert len(lines) == 3
                    assert lines[0] == "full_path,file_summary,date"

def test_normal_operation_with_existing_csv(mock_pdd_path, mock_files_directory, mock_existing_csv):
    # Create prompt file
    create_temp_prompt_file(mock_pdd_path)

    directory, files = mock_files_directory
    normalized_files = [normalize_path(f) for f in files]

    newer_file = files[0]
    os.utime(newer_file, (datetime.now().timestamp(), datetime.now().timestamp()))

    mock_llm_response = {
        'result': MagicMock(file_summary="New Mock summary"),
        'cost': 0.02,
        'model_name': "MockModelV2"
    }

    # Create a mapping of file contents
    file_contents = {
        files[0]: "# Contents of file1.py",
        files[1]: "# Contents of file2.py"
    }

    def mock_open_side_effect(file_path, *args, **kwargs):
        if file_path in file_contents:
            return mock_open(read_data=file_contents[file_path])(*args, **kwargs)
        return mock_open(read_data="")(*args, **kwargs)

    with mock.patch.dict(os.environ, {"PDD_PATH": mock_pdd_path}):
        with mock.patch("glob.glob", return_value=files):
            with mock.patch("pdd.summarize_directory.read_existing_csv", return_value={
                normalized_files[0]: {
                    "file_summary": "Summary 1",
                    "date": datetime.fromisoformat("2023-10-01T12:00:00")
                },
                normalized_files[1]: {
                    "file_summary": "Summary 2",
                    "date": datetime.fromisoformat("2023-10-02T12:00:00")
                }
            }):
                with mock.patch("builtins.open", side_effect=mock_open_side_effect):
                    def llm_invoke_side_effect(*args, **kwargs):
                        if 'input_json' in kwargs and 'file_contents' in kwargs['input_json']:
                            content = kwargs['input_json']['file_contents']
                            if "Contents of file1.py" in content:
                                return mock_llm_response
                        return {
                            'result': MagicMock(file_summary="Summary 2"),
                            'cost': 0.01,
                            'model_name': "MockModel"
                        }

                    with mock.patch("pdd.summarize_directory.llm_invoke", side_effect=llm_invoke_side_effect):
                        csv_output, total_cost, model_name = summarize_directory(
                            directory_path=f"{directory}/*.py",
                            strength=0.5,
                            temperature=0.7,
                            csv_file=mock_existing_csv,
                            verbose=True
                        )
                        lines = normalize_line_endings(csv_output.strip()).split('\r\n')
                        assert len(lines) == 3
                        assert "New Mock summary" in csv_output

def test_invalid_strength(mock_pdd_path, mock_files_directory):
    # Create prompt file
    create_temp_prompt_file(mock_pdd_path)

    directory, files = mock_files_directory

    with mock.patch.dict(os.environ, {"PDD_PATH": mock_pdd_path}):
        with mock.patch("glob.glob", return_value=files):
            with pytest.raises(ValueError):
                # Assuming the function should raise ValueError for invalid strength
                summarize_directory(
                    directory_path=f"{directory}/*.py",
                    strength=1.5,  # invalid strength
                    temperature=0.7
                )

def test_invalid_temperature(mock_pdd_path, mock_files_directory):
    # Create prompt file
    create_temp_prompt_file(mock_pdd_path)

    directory, files = mock_files_directory

    with mock.patch.dict(os.environ, {"PDD_PATH": mock_pdd_path}):
        with mock.patch("glob.glob", return_value=files):
            with pytest.raises(ValueError):
                # Assuming the function should raise ValueError for invalid temperature
                summarize_directory(
                    directory_path=f"{directory}/*.py",
                    strength=0.5,
                    temperature=1.5  # invalid temperature
                )