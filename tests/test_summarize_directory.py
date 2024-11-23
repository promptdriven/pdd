import pytest
from unittest.mock import patch, mock_open, MagicMock
from datetime import datetime
from pdd.summarize_directory import summarize_directory

# Helper function to create a mock datetime
def mock_datetime_now(target, mock_now):
    class MockedDatetime(datetime):
        @classmethod
        def now(cls, tz=None):
            return mock_now
    return patch(target, MockedDatetime)

@pytest.fixture
def mock_files():
    return [
        "/path/to/directory/file1.py",
        "/path/to/directory/file2.py",
        "/path/to/directory/file3.py"
    ]

@pytest.fixture
def existing_csv():
    return (
        "full_path,file_summary,date\n"
        "/path/to/directory/file1.py,Summary of file1,2023-10-01 12:00:00\n"
    )

@pytest.fixture
def mock_file_contents():
    return {
        "/path/to/directory/file1.py": "print('Hello, World!')",
        "/path/to/directory/file2.py": "def foo(): pass",
        "/path/to/directory/file3.py": "import os"
    }

@pytest.fixture
def fixed_now():
    return datetime(2023, 10, 2, 15, 30, 00)

def test_successful_summarization(
    mock_files, mock_file_contents, existing_csv, fixed_now
):
    with patch('pdd.summarize_directory.glob.glob', return_value=mock_files) as mock_glob, \
         patch('pdd.summarize_directory.os.stat') as mock_stat, \
         patch('pdd.summarize_directory.open') as mock_file, \
         patch('pdd.summarize_directory.load_prompt_template', return_value="Summarize the file.") as mock_load_prompt, \
         patch('pdd.summarize_directory.llm_invoke') as mock_llm_invoke, \
         mock_datetime_now('pdd.summarize_directory.datetime', fixed_now) as mock_datetime:
        
        def mock_stat_side_effect(file_path, **kwargs):
            mock_stat_result = MagicMock()
            if file_path == '/path/to/directory/file1.py':
                mock_stat_result.st_mtime = datetime(2023, 10, 1, 11, 0, 0).timestamp()
            else:
                mock_stat_result.st_mtime = fixed_now.timestamp()
            return mock_stat_result
        mock_stat.side_effect = mock_stat_side_effect
        
        mock_file_instances = {}
        def mock_open_side_effect(file_path, mode='r', encoding=None):
            if file_path not in mock_file_instances:
                mock = MagicMock()
                mock.__enter__.return_value = mock
                mock.name = file_path
                if file_path in mock_file_contents:
                    mock.read.return_value = mock_file_contents[file_path]
                mock_file_instances[file_path] = mock
            return mock_file_instances[file_path]
        mock_file.side_effect = mock_open_side_effect
        
        def llm_invoke_side_effect(*args, **kwargs):
            file_contents = kwargs['input_json']['file_contents']
            if file_contents == mock_file_contents['/path/to/directory/file1.py']:
                summary = "Summary of file1"
            else:
                if "def foo" in file_contents:
                    summary = "Summary of def foo"
                elif "import os" in file_contents:
                    summary = "Summary of import o"
                else:
                    summary = f"Summary of {file_contents[:10]}"
            return {
                'result': MagicMock(file_summary=summary),
                'cost': 0.01,
                'model_name': 'MockModel'
            }
        mock_llm_invoke.side_effect = llm_invoke_side_effect
        
        csv_output, total_cost, model_name = summarize_directory(
            directory_path="/path/to/directory/*.py",
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=existing_csv
        )
        
        expected_csv = (
            "full_path,file_summary,date\r\n"
            "/path/to/directory/file1.py,Summary of file1,2023-10-01 12:00:00\r\n"
            "/path/to/directory/file2.py,Summary of def foo,2023-10-02 15:30:00\r\n"
            "/path/to/directory/file3.py,Summary of import o,2023-10-02 15:30:00\r\n"
        )
        assert csv_output == expected_csv
        assert total_cost == 0.02  # Corrected total cost
        assert model_name == 'MockModel'

def test_existing_csv_unchanged_files(
    mock_files, existing_csv, mock_file_contents, fixed_now
):
    with patch('pdd.summarize_directory.glob.glob', return_value=mock_files) as mock_glob, \
         patch('pdd.summarize_directory.os.stat') as mock_stat, \
         patch('pdd.summarize_directory.open', mock_open()) as mock_file, \
         patch('pdd.summarize_directory.load_prompt_template', return_value="Summarize the file.") as mock_load_prompt, \
         patch('pdd.summarize_directory.llm_invoke') as mock_llm_invoke, \
         mock_datetime_now('pdd.summarize_directory.datetime', fixed_now) as mock_datetime:
        
        def stat_side_effect(path, follow_symlinks=True):
            if str(path).endswith("file1.py"):
                return MagicMock(st_mtime=datetime(2023, 9, 30, 10, 0, 0).timestamp())
            return MagicMock(st_mtime=fixed_now.timestamp())
        mock_stat.side_effect = stat_side_effect
        
        handle = mock_file()
        def read_side_effect():
            for path, content in mock_file_contents.items():
                if path in str(handle.name):
                    return content
            return ""
        handle.read.side_effect = read_side_effect
        
        mock_llm_invoke.return_value = {
            'result': MagicMock(file_summary="New summary"),
            'cost': 0.01,
            'model_name': 'MockModel'
        }
        
        csv_output, total_cost, model_name = summarize_directory(
            directory_path="/path/to/directory/*.py",
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=existing_csv
        )
        
        expected_csv = (
            "full_path,file_summary,date\r\n"
            "/path/to/directory/file1.py,Summary of file1,2023-10-01 12:00:00\r\n"
            "/path/to/directory/file2.py,New summary,2023-10-02 15:30:00\r\n"
            "/path/to/directory/file3.py,New summary,2023-10-02 15:30:00\r\n"
        )
        assert csv_output == expected_csv
        assert total_cost == 0.02
        assert model_name == 'MockModel'

def test_no_files_found(existing_csv, fixed_now):
    with patch('pdd.summarize_directory.glob.glob', return_value=[]), \
         mock_datetime_now('pdd.summarize_directory.datetime', fixed_now):
        
        # Call the function under test
        csv_output, total_cost, model_name = summarize_directory(
            directory_path="/path/to/nonexistent/*.py",
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=existing_csv
        )
        
        # Assertions
        expected_csv = (
            "full_path,file_summary,date\r\n"
            "/path/to/directory/file1.py,Summary of file1,2023-10-01 12:00:00\r\n"
        )
        assert csv_output == expected_csv
        assert total_cost == 0.0
        assert model_name == ''

def test_load_prompt_template_failure(existing_csv):
    with patch('pdd.summarize_directory.load_prompt_template', return_value=None):
        with pytest.raises(ValueError) as exc_info:
            summarize_directory(
                directory_path="/path/to/directory/*.py",
                strength=0.5,
                temperature=0.7,
                verbose=False,
                csv_file=existing_csv
            )
        assert str(exc_info.value) == "Failed to load prompt template"

def test_llm_invoke_exception(
    mock_files, existing_csv, mock_file_contents, fixed_now
):
    with patch('pdd.summarize_directory.glob.glob', return_value=mock_files), \
         patch('pdd.summarize_directory.os.stat') as mock_stat, \
         patch('pdd.summarize_directory.open') as mock_file, \
         patch('pdd.summarize_directory.load_prompt_template', return_value="Summarize the file."), \
         patch('pdd.summarize_directory.llm_invoke') as mock_llm_invoke, \
         mock_datetime_now('pdd.summarize_directory.datetime', fixed_now):

        def mock_stat_side_effect(file_path, **kwargs):
            mock_stat_result = MagicMock()
            if file_path == '/path/to/directory/file1.py':
                mock_stat_result.st_mtime = datetime(2023, 10, 1, 11, 0, 0).timestamp()
            else:
                mock_stat_result.st_mtime = fixed_now.timestamp()
            return mock_stat_result
        mock_stat.side_effect = mock_stat_side_effect

        def mock_open_side_effect(file_path, mode='r', encoding=None):
            mock = MagicMock()
            mock.__enter__.return_value = mock
            mock.name = file_path
            if file_path in mock_file_contents:
                mock.read.return_value = mock_file_contents[file_path]
            else:
                mock.read.return_value = ""
            return mock
        mock_file.side_effect = mock_open_side_effect

        def llm_invoke_side_effect(*args, **kwargs):
            if "def foo" in kwargs['input_json']['file_contents']:
                raise RuntimeError("LLM invocation failed")
            return {
                'result': MagicMock(file_summary="Valid summary"),
                'cost': 0.01,
                'model_name': 'MockModel'
            }
        mock_llm_invoke.side_effect = llm_invoke_side_effect

        csv_output, total_cost, model_name = summarize_directory(
            directory_path="/path/to/directory/*.py",
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=existing_csv
        )

        expected_csv = (
            "full_path,file_summary,date\r\n"
            "/path/to/directory/file1.py,Summary of file1,2023-10-01 12:00:00\r\n"
            "/path/to/directory/file3.py,Valid summary,2023-10-02 15:30:00\r\n"
        )
        assert csv_output == expected_csv
        assert total_cost == 0.01
        assert model_name == 'MockModel'

def test_empty_directory_no_csv():
    with patch('pdd.summarize_directory.glob.glob', return_value=[]), \
         mock_datetime_now('pdd.summarize_directory.datetime', datetime(2023, 10, 2, 15, 30, 00)):
        
        # Call the function under test without existing CSV
        csv_output, total_cost, model_name = summarize_directory(
            directory_path="/empty/directory/*.py",
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=None
        )
        
        # Assertions
        expected_csv = "full_path,file_summary,date\r\n"
        assert csv_output == expected_csv
        assert total_cost == 0.0
        assert model_name == ''

def test_invalid_directory_path():
    with patch('pdd.summarize_directory.glob.glob', side_effect=Exception("Invalid directory")), \
         patch('pdd.summarize_directory.load_prompt_template', return_value="Summarize the file."):
        
        with pytest.raises(Exception) as exc_info:
            summarize_directory(
                directory_path="/invalid/path/*.py",
                strength=0.5,
                temperature=0.7,
                verbose=False,
                csv_file=None
            )
        assert "Invalid directory" in str(exc_info.value)

def test_verbose_flag(capsys, mock_files, mock_file_contents, existing_csv, fixed_now):
    with patch('pdd.summarize_directory.glob.glob', return_value=mock_files), \
         patch('pdd.summarize_directory.os.stat') as mock_stat, \
         patch('pdd.summarize_directory.open') as mock_file, \
         patch('pdd.summarize_directory.load_prompt_template', return_value="Summarize the file."), \
         patch('pdd.summarize_directory.llm_invoke') as mock_llm_invoke, \
         mock_datetime_now('pdd.summarize_directory.datetime', fixed_now):

        def mock_stat_side_effect(file_path, **kwargs):
            mock_stat_result = MagicMock()
            if file_path == '/path/to/directory/file1.py':
                mock_stat_result.st_mtime = datetime(2023, 10, 1, 11, 0, 0).timestamp()
            else:
                mock_stat_result.st_mtime = fixed_now.timestamp()
            return mock_stat_result
        mock_stat.side_effect = mock_stat_side_effect

        def mock_open_side_effect(file_path, mode='r', encoding=None):
            mock = MagicMock()
            mock.__enter__.return_value = mock
            mock.name = file_path
            if file_path in mock_file_contents:
                mock.read.return_value = mock_file_contents[file_path]
            else:
                mock.read.return_value = ""
            return mock
        mock_file.side_effect = mock_open_side_effect
        
        mock_llm_invoke.return_value = {
            'result': MagicMock(file_summary="Verbose summary"),
            'cost': 0.01,
            'model_name': 'VerboseModel'
        }

        csv_output, total_cost, model_name = summarize_directory(
            directory_path="/path/to/directory/*.py",
            strength=0.5,
            temperature=0.7,
            verbose=True,
            csv_file=existing_csv
        )

        captured = capsys.readouterr()

        expected_csv = (
            "full_path,file_summary,date\r\n"
            "/path/to/directory/file1.py,Summary of file1,2023-10-01 12:00:00\r\n"
            "/path/to/directory/file2.py,Verbose summary,2023-10-02 15:30:00\r\n"
            "/path/to/directory/file3.py,Verbose summary,2023-10-02 15:30:00\r\n"
        )
        assert csv_output == expected_csv
        assert total_cost == 0.02
        assert model_name == 'VerboseModel'

        # Assertions for verbose output
        assert "Summarizing: /path/to/directory/file2.py" in captured.out
        assert "Summarizing: /path/to/directory/file3.py" in captured.out

def test_csv_file_optional():
    with patch('pdd.summarize_directory.glob.glob', return_value=[]), \
         mock_datetime_now('pdd.summarize_directory.datetime', datetime(2023, 10, 2, 15, 30, 00)):
        
        # Call the function under test without providing csv_file
        csv_output, total_cost, model_name = summarize_directory(
            directory_path="/no/csv/directory/*.py",
            strength=0.5,
            temperature=0.7,
            verbose=False,
            csv_file=None
        )
        
        # Assertions
        expected_csv = "full_path,file_summary,date\r\n"
        assert csv_output == expected_csv
        assert total_cost == 0.0
        assert model_name == ''