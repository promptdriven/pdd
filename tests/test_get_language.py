import pytest
import os
import csv
from get_language import get_language

# Mock CSV data
mock_csv_data = """language,comment,extension
Python,#,.py
Java,//,.java
Bash,#,.sh
"""

@pytest.fixture
def mock_csv_file(tmp_path):
    """Creates a temporary CSV file with mock data for testing."""
    csv_file = tmp_path / "language_format.csv"
    csv_file.write_text(mock_csv_data)
    return csv_file

@pytest.fixture
def mock_environment(monkeypatch, tmp_path):
    """Mocks the environment variable PDD_PATH to point to a temporary path."""
    monkeypatch.setenv("PDD_PATH", str(tmp_path))


def test_get_language_with_dot(mock_environment, mock_csv_file):
    """Tests get_language with a valid extension including the dot."""
    assert get_language('.py') == 'Python'


def test_get_language_without_dot(mock_environment, mock_csv_file):
    """Tests get_language with a valid extension without the dot."""
    assert get_language('java') == 'Java'


def test_get_language_case_insensitive(mock_environment, mock_csv_file):
    """Tests get_language for case insensitivity."""
    assert get_language('.PY') == 'Python'


def test_get_language_not_found(mock_environment, mock_csv_file):
    """Tests get_language with an extension not in the CSV."""
    assert get_language('.cpp') == ''


def test_get_language_empty_extension(mock_environment, mock_csv_file):
    """Tests get_language with an empty extension."""
    assert get_language('') == ''


def test_get_language_missing_environment_variable(monkeypatch):
    """Tests get_language when the PDD_PATH environment variable is not set."""
    monkeypatch.delenv("PDD_PATH", raising=False)
    with pytest.raises(ValueError, match="PDD_PATH environment variable is not set"):
        get_language('.py')


def test_get_language_file_not_found(mock_environment, tmp_path):
    """Tests get_language when the CSV file is not found."""
    with pytest.raises(FileNotFoundError):
        get_language('.py')


def test_get_language_csv_error(mock_environment, mock_csv_file):
    """Tests get_language when there's an error reading the CSV file."""
    # Corrupt the CSV file
    mock_csv_file.write_text("invalid,csv,data")
    assert get_language('.py') == ''
