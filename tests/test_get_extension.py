import pytest
from unittest.mock import patch, MagicMock
from pdd.get_extension import get_extension
import pandas as pd

# Sample data to be used in tests
SAMPLE_CSV_DATA = pd.DataFrame({
    'language': ['Python', 'Java', 'Bash', 'Makefile'],
    'comment': ['#', '//', '#', '#'],
    'extension': ['.py', '.java', '.sh', '']
})

@pytest.fixture
def mock_env_pdd_path():
    """Fixture to mock the PDD_PATH environment variable."""
    with patch('os.getenv', return_value='/fake/pdd_path') as mock_env:
        yield mock_env

@pytest.fixture
def mock_read_csv():
    """Fixture to mock pandas.read_csv returning a DataFrame."""
    with patch('pdd.get_extension.pd.read_csv', return_value=SAMPLE_CSV_DATA):
        yield

def test_get_extension_normal_case(mock_env_pdd_path, mock_read_csv):
    """Test that a valid language returns the correct extension."""
    assert get_extension('Python') == '.py'

def test_get_extension_case_insensitivity(mock_env_pdd_path, mock_read_csv):
    """Test that the function is case-insensitive."""
    assert get_extension('JaVa') == '.java'

def test_get_extension_language_not_found(mock_env_pdd_path, mock_read_csv):
    """Test that an unknown language returns an empty string."""
    assert get_extension('Ruby') == ''

def test_get_extension_invalid_extension_empty_string(mock_env_pdd_path, mock_read_csv):
    """Test that a language with an empty extension returns an empty string."""
    assert get_extension('Makefile') == ''

def test_get_extension_pdd_path_not_set():
    """Test that missing PDD_PATH environment variable raises ValueError."""
    with patch('os.getenv', return_value=None):
        with pytest.raises(ValueError, match="Environment variable PDD_PATH is not set."):
            get_extension('Python')

def test_get_extension_csv_file_not_found(mock_env_pdd_path):
    """Test that missing CSV file raises FileNotFoundError."""
    with patch('pdd.get_extension.pd.read_csv', side_effect=FileNotFoundError):
        with pytest.raises(FileNotFoundError, match="The file /fake/pdd_path/data/language_format.csv does not exist."):
            get_extension('Python')

def test_get_extension_csv_malformed(mock_env_pdd_path):
    """Test that a malformed CSV (missing 'extension' column) raises KeyError."""
    malformed_df = SAMPLE_CSV_DATA.drop(columns=['extension'])
    with patch('pdd.get_extension.pd.read_csv', return_value=malformed_df):
        with pytest.raises(KeyError, match="'extension'"):
            get_extension('Python')

def test_get_extension_extension_not_string(mock_env_pdd_path):
    """Test that a non-string extension is treated as invalid."""
    invalid_df = SAMPLE_CSV_DATA.copy()
    invalid_df.loc[0, 'extension'] = 123
    with patch('pdd.get_extension.pd.read_csv', return_value=invalid_df):
        assert get_extension('Python') == ''