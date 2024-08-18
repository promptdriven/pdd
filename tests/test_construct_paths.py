import pytest
from unittest.mock import patch, mock_open
from construct_paths import construct_paths
from click import Abort

@pytest.fixture
def mock_file_content():
    return "Mock file content"

@pytest.fixture
def mock_get_extension():
    with patch('construct_paths.get_extension') as mock:
        mock.return_value = '.py'
        yield mock

@pytest.fixture
def mock_get_language():
    with patch('construct_paths.get_language') as mock:
        mock.return_value = 'python'
        yield mock

@pytest.fixture
def mock_generate_output_paths():
    with patch('construct_paths.generate_output_paths') as mock:
        mock.return_value = {'output': '/path/to/output.py'}
        yield mock


def test_construct_paths_generate_command(mock_file_content, mock_get_extension, mock_generate_output_paths):
    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        input_file_paths = {'prompt_file': '/path/to/prompt_python'}
        result = construct_paths(input_file_paths, True, True, 'generate', {})
        
        assert result[0] == {'prompt_file': mock_file_content}
        assert result[1] == {'output': '/path/to/output.py'}
        assert result[2] == 'python'


def test_construct_paths_other_command(mock_file_content, mock_get_language, mock_get_extension, mock_generate_output_paths):
    with patch('builtins.open', mock_open(read_data=mock_file_content)):
        input_file_paths = {'code_file': '/path/to/code.py'}
        result = construct_paths(input_file_paths, True, True, 'test', {})
        
        assert result[0] == {'code_file': mock_file_content}
        assert result[1] == {'output': '/path/to/output.py'}
        assert result[2] == 'python'


def test_construct_paths_missing_extension():
    input_file_paths = {'prompt_file': '/path/to/prompt'}
    with patch('builtins.open', mock_open(read_data="content")):
        result = construct_paths(input_file_paths, True, True, 'generate', {})
        assert 'prompt_file' in result[0]
        assert result[0]['prompt_file'] == "content"


def test_construct_paths_file_not_found():
    input_file_paths = {'prompt_file': '/path/to/nonexistent_file'}
    with pytest.raises(IOError):
        construct_paths(input_file_paths, True, True, 'generate', {})


@patch('click.confirm')
def test_construct_paths_existing_output_file_force_false(mock_confirm, mock_generate_output_paths):
    mock_confirm.return_value = False
    input_file_paths = {'prompt_file': '/path/to/prompt.txt'}
    
    with patch('os.path.exists', return_value=True), \
         patch('builtins.open', mock_open(read_data="content")), \
         pytest.raises(Abort):
        construct_paths(input_file_paths, False, False, 'generate', {})


@patch('click.confirm')
def test_construct_paths_existing_output_file_force_true(mock_confirm, mock_generate_output_paths):
    input_file_paths = {'prompt_file': '/path/to/prompt.txt'}
    
    with patch('os.path.exists', return_value=True), \
         patch('builtins.open', mock_open(read_data="content")):
        result = construct_paths(input_file_paths, True, False, 'generate', {})
        assert result is not None
        mock_confirm.assert_not_called()

# Run the tests
if __name__ == "__main__":
    pytest.main(["-v", __file__])