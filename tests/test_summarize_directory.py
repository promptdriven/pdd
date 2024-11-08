import os
import pytest
import tempfile
import shutil
from unittest import mock
from unittest.mock import mock_open, MagicMock
from pathlib import Path
from datetime import datetime
from pdd.summarize_directory import summarize_directory

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

    mock_llm_response = {
        'result': MagicMock(file_summary="Mock summary"),
        'cost': 0.01,
        'model_name': "MockModel"
    }

    with mock.patch.dict(os.environ, {"PDD_PATH": mock_pdd_path}):
        with mock.patch("glob.glob", return_value=files):
            # Mock open to read file contents normally
            m = mock_open(read_data="# file contents")
            with mock.patch("builtins.open", m):
                # Mock llm_invoke to return a successful response
                with mock.patch("pdd.summarize_directory.llm_invoke", return_value=mock_llm_response):
                    csv_output, total_cost, model_name = summarize_directory(
                        directory_path=f"{directory}/*.py",
                        strength=0.5,
                        temperature=0.7
                    )
                    # Parse CSV output
                    lines = csv_output.strip().split("\n")
                    assert len(lines) == 3  # header + 2 files
                    assert lines[0] == "full_path,file_summary,date"
                    for line in lines[1:]:
                        parts = line.split(",")
                        assert len(parts) == 3
                        assert parts[1] == "Mock summary"
                        # Check if date is a valid ISO format
                        datetime.fromisoformat(parts[2])

                    assert total_cost == 0.02  # 2 files * 0.01
                    assert model_name == "MockModel"

def test_normal_operation_with_existing_csv(mock_pdd_path, mock_files_directory, mock_existing_csv):
    # Create prompt file
    create_temp_prompt_file(mock_pdd_path)

    directory, files = mock_files_directory

    # Modify one file's modification time to be newer
    newer_file = files[0]
    os.utime(newer_file, (datetime.now().timestamp(), datetime.now().timestamp()))

    mock_llm_response = {
        'result': MagicMock(file_summary="New Mock summary"),
        'cost': 0.02,
        'model_name': "MockModelV2"
    }

    with mock.patch.dict(os.environ, {"PDD_PATH": mock_pdd_path}):
        with mock.patch("glob.glob", return_value=files):
            # Mock read_existing_csv to return data
            with mock.patch("pdd.summarize_directory.read_existing_csv", return_value={
                "/path/to/file1.py": {
                    "file_summary": "Summary 1",
                    "date": datetime.fromisoformat("2023-10-01T12:00:00")
                },
                "/path/to/file2.py": {
                    "file_summary": "Summary 2",
                    "date": datetime.fromisoformat("2023-10-02T12:00:00")
                }
            }):
                # Mock open to read file contents normally
                m = mock_open(read_data="# file contents")
                with mock.patch("builtins.open", m):
                    # Mock llm_invoke to return a successful response only for the newer file
                    def llm_invoke_side_effect(*args, **kwargs):
                        if "/file1.py" in args[1]['file_contents']:
                            return mock_llm_response
                        else:
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
                            csv_file=mock_existing_csv
                        )
                        # Parse CSV output
                        lines = csv_output.strip().split("\n")
                        assert len(lines) == 3  # header + 2 files
                        assert lines[0] == "full_path,file_summary,date"
                        # The first file should have the new summary
                        assert "Mock summary" in lines[1]
                        # The second file should retain the existing summary
                        assert "Summary 2" in lines[2]

                        assert total_cost == 0.02 + 0.01  # Only one new summary * 0.02 + one reused * 0.0
                        assert model_name == "MockModelV2"

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