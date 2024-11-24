# tests/test_summarize_directory.py

import pytest
from unittest.mock import patch, mock_open, MagicMock
from pdd.summarize_directory import summarize_directory
import os
from datetime import datetime
import csv
from io import StringIO

@pytest.fixture
def mock_load_prompt_template():
    with patch('pdd.summarize_directory.load_prompt_template') as mock:
        mock.return_value = "Summarize the following file contents."
        yield mock

@pytest.fixture
def mock_llm_invoke():
    with patch('pdd.summarize_directory.llm_invoke') as mock:
        # Define a default mock response
        mock_response = {
            'result': MagicMock(file_summary="This is a summary."),
            'cost': 0.01,
            'model_name': "TestModel"
        }
        mock.return_value = mock_response
        yield mock

def test_valid_inputs_no_existing_csv(tmp_path, mock_load_prompt_template, mock_llm_invoke):
    # Create some temporary files
    file1 = tmp_path / "file1.py"
    file1.write_text("print('Hello World')")
    file2 = tmp_path / "file2.py"
    file2.write_text("def foo(): pass")

    directory_path = str(tmp_path / "*.py")
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = None

    csv_output, total_cost, model_name = summarize_directory(
        directory_path=directory_path,
        strength=strength,
        temperature=temperature,
        verbose=verbose,
        csv_file=csv_file
    )

    # Parse CSV output
    reader = csv.DictReader(StringIO(csv_output))
    rows = list(reader)
    assert len(rows) == 2
    for row in rows:
        assert 'full_path' in row
        assert 'file_summary' in row
        assert 'date' in row
        assert row['file_summary'] == "This is a summary."

    assert total_cost == 0.02  # Two files summarized
    assert model_name == "TestModel"

def test_valid_inputs_with_existing_csv(tmp_path, mock_load_prompt_template, mock_llm_invoke):
    # Create temporary files
    file1 = tmp_path / "file1.py"
    file1.write_text("print('Hello World')")
    file2 = tmp_path / "file2.py"
    file2.write_text("def foo(): pass")

    # Create existing CSV with file1
    existing_csv = f'''full_path,file_summary,date
"{os.path.relpath(str(file1))}","Existing summary.",{datetime.utcnow().isoformat()}
'''

    directory_path = str(tmp_path / "*.py")
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = existing_csv

    # Mock file modification time
    with patch('pdd.summarize_directory.os.path.getmtime') as mock_getmtime:
        # file1 has not changed
        mock_getmtime.side_effect = [
            file1.stat().st_mtime,
            file2.stat().st_mtime
        ]

        csv_output, total_cost, model_name = summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )

    # Parse CSV output
    reader = csv.DictReader(StringIO(csv_output))
    rows = list(reader)
    assert len(rows) == 2

    # Check that file1 reused summary
    for row in rows:
        if row['full_path'] == os.path.relpath(str(file1)):
            assert row['file_summary'] == "Existing summary."
        elif row['full_path'] == os.path.relpath(str(file2)):
            assert row['file_summary'] == "This is a summary."

    assert total_cost == 0.01  # Only file2 was summarized
    assert model_name == "TestModel"

def test_empty_directory(tmp_path, mock_load_prompt_template, mock_llm_invoke):
    directory_path = str(tmp_path / "*.py")
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = None

    csv_output, total_cost, model_name = summarize_directory(
        directory_path=directory_path,
        strength=strength,
        temperature=temperature,
        verbose=verbose,
        csv_file=csv_file
    )

    # Check CSV output has only headers
    reader = csv.DictReader(StringIO(csv_output))
    rows = list(reader)
    assert len(rows) == 0

    assert total_cost == 0.0
    assert model_name == "None"

def test_invalid_directory_path(mock_load_prompt_template, mock_llm_invoke):
    directory_path = ""  # Invalid
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = None

    with pytest.raises(ValueError, match="Invalid 'directory_path'."):
        summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )

def test_invalid_strength(mock_load_prompt_template, mock_llm_invoke):
    directory_path = "/path/to/*.py"
    strength = 1.5  # Invalid
    temperature = 0.7
    verbose = False
    csv_file = None

    with pytest.raises(ValueError, match="Invalid 'strength' value."):
        summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )

def test_invalid_temperature(mock_load_prompt_template, mock_llm_invoke):
    directory_path = "/path/to/*.py"
    strength = 0.5
    temperature = -0.1  # Invalid
    verbose = False
    csv_file = None

    with pytest.raises(ValueError, match="Invalid 'temperature' value."):
        summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )

def test_invalid_verbose(mock_load_prompt_template, mock_llm_invoke):
    directory_path = "/path/to/*.py"
    strength = 0.5
    temperature = 0.7
    verbose = "yes"  # Invalid
    csv_file = None

    with pytest.raises(ValueError, match="Invalid 'verbose' value."):
        summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )

def test_invalid_existing_csv(tmp_path, mock_load_prompt_template, mock_llm_invoke):
    # Create temporary files
    file1 = tmp_path / "file1.py"
    file1.write_text("print('Hello World')")

    # Create invalid existing CSV
    existing_csv = "invalid,csv,content"

    directory_path = str(tmp_path / "*.py")
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = existing_csv

    with pytest.raises(ValueError, match="Invalid CSV file format."):
        summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )

def test_llm_invoke_error(tmp_path, mock_load_prompt_template):
    # Create temporary file
    file1 = tmp_path / "file1.py"
    file1.write_text("print('Hello World')")

    directory_path = str(tmp_path / "*.py")
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = None

    # Mock llm_invoke to return an error
    with patch('pdd.summarize_directory.llm_invoke') as mock_llm:
        mock_llm.return_value = {
            'error': "LLM service failed."
        }

        csv_output, total_cost, model_name = summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )

    # Parse CSV output
    reader = csv.DictReader(StringIO(csv_output))
    rows = list(reader)
    assert len(rows) == 1
    row = rows[0]
    assert row['file_summary'] == "Error in summarization."
    assert total_cost == 0.0  # No cost accumulated
    assert model_name == "None"

def test_load_prompt_template_not_found(tmp_path, mock_llm_invoke):
    # Create temporary file
    file1 = tmp_path / "file1.py"
    file1.write_text("print('Hello World')")

    directory_path = str(tmp_path / "*.py")
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = None

    # Mock load_prompt_template to return None
    with patch('pdd.summarize_directory.load_prompt_template') as mock_load:
        mock_load.return_value = None

        with pytest.raises(FileNotFoundError, match="Prompt template 'summarize_file_LLM.prompt' not found."):
            summarize_directory(
                directory_path=directory_path,
                strength=strength,
                temperature=temperature,
                verbose=verbose,
                csv_file=csv_file
            )

def test_partial_summarization(tmp_path, mock_load_prompt_template, mock_llm_invoke):
    # Create multiple temporary files
    file1 = tmp_path / "file1.py"
    file1.write_text("print('Hello World')")
    file2 = tmp_path / "file2.py"
    file2.write_text("def foo(): pass")
    file3 = tmp_path / "file3.py"
    file3.write_text("import os")

    # Create existing CSV with file1 and file2
    existing_csv = f'''full_path,file_summary,date
"{os.path.relpath(str(file1))}","Existing summary.",{datetime.utcnow().isoformat()}
"{os.path.relpath(str(file2))}","Existing summary.",{datetime.utcnow().isoformat()}
'''

    directory_path = str(tmp_path / "*.py")
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = existing_csv

    # Mock file modification time: file1 not changed, file2 modified, file3 new
    with patch('pdd.summarize_directory.os.path.getmtime') as mock_getmtime:
        current_time = datetime.utcnow().timestamp()
        mock_getmtime.side_effect = [
            file1.stat().st_mtime,  # file1
            current_time + 100,      # file2 modified
            file3.stat().st_mtime   # file3
        ]

        csv_output, total_cost, model_name = summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )

    # Parse CSV output
    reader = csv.DictReader(StringIO(csv_output))
    rows = list(reader)
    assert len(rows) == 3

    summaries = {row['full_path']: row['file_summary'] for row in rows}
    assert summaries[os.path.relpath(str(file1))] == "Existing summary."
    assert summaries[os.path.relpath(str(file2))] == "This is a summary."
    assert summaries[os.path.relpath(str(file3))] == "This is a summary."

    assert total_cost == 0.02  # file2 and file3 summarized
    assert model_name == "TestModel"

def test_non_python_files(tmp_path, mock_load_prompt_template, mock_llm_invoke):
    # Create non-Python files
    file1 = tmp_path / "file1.txt"
    file1.write_text("Just some text.")
    file2 = tmp_path / "file2.md"
    file2.write_text("# Markdown file")

    directory_path = str(tmp_path / "*.*")
    strength = 0.5
    temperature = 0.7
    verbose = False
    csv_file = None

    # Mock file modification time
    with patch('pdd.summarize_directory.os.path.getmtime') as mock_getmtime:
        mock_getmtime.side_effect = [
            file1.stat().st_mtime,
            file2.stat().st_mtime
        ]

        csv_output, total_cost, model_name = summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )

    # Parse CSV output
    reader = csv.DictReader(StringIO(csv_output))
    rows = list(reader)
    assert len(rows) == 2
    for row in rows:
        assert 'full_path' in row
        assert 'file_summary' in row
        assert 'date' in row
        assert row['file_summary'] == "This is a summary."

    assert total_cost == 0.02  # Two files summarized
    assert model_name == "TestModel"