import pytest
import os
from pathlib import Path
from unittest.mock import patch, call
from pdd.generate_output_paths import generate_output_paths

@pytest.fixture
def setup_environment():
    # Set up environment variables for testing
    os.environ['PDD_GENERATE_OUTPUT_PATH'] = '/env/path/generate'
    os.environ['PDD_FIX_TEST_OUTPUT_PATH'] = '/env/path/fix_test'
    os.environ['PDD_FIX_CODE_OUTPUT_PATH'] = '/env/path/fix_code'
    yield
    # Clean up environment variables after testing
    del os.environ['PDD_GENERATE_OUTPUT_PATH']
    del os.environ['PDD_FIX_TEST_OUTPUT_PATH']
    del os.environ['PDD_FIX_CODE_OUTPUT_PATH']

@patch('pathlib.Path.mkdir')
def test_generate_command_default(mock_mkdir):
    result = generate_output_paths('generate', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'myfile.py'}
    mock_mkdir.assert_not_called()

@patch('pathlib.Path.mkdir')
def test_generate_command_with_output_location(mock_mkdir):
    result = generate_output_paths('generate', {'output': '/custom/path/output.py'}, 'myfile', 'python', '.py')
    assert result == {'output': '/custom/path/output.py'}
    mock_mkdir.assert_called_once_with(parents=True, exist_ok=True)

@patch('pathlib.Path.mkdir')
def test_generate_command_with_output_directory(mock_mkdir):
    result = generate_output_paths('generate', {'output': '/custom/directory'}, 'myfile', 'python', '.py')
    assert result == {'output': '/custom/directory/myfile.py'}
    mock_mkdir.assert_called_once_with(parents=True, exist_ok=True)

@patch('pathlib.Path.mkdir')
def test_example_command(mock_mkdir):
    result = generate_output_paths('example', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'myfile_example.py'}
    mock_mkdir.assert_not_called()

@patch('pathlib.Path.mkdir')
def test_test_command(mock_mkdir):
    result = generate_output_paths('test', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'test_myfile.py'}
    mock_mkdir.assert_not_called()

@patch('pathlib.Path.mkdir')
def test_preprocess_command(mock_mkdir):
    result = generate_output_paths('preprocess', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'myfile_python_preprocessed.prompt'}
    mock_mkdir.assert_not_called()

@patch('pathlib.Path.mkdir')
def test_fix_command(mock_mkdir):
    result = generate_output_paths('fix', {}, 'myfile', 'python', '.py')
    assert result == {
        'output_test': 'test_myfile_fixed.py',
        'output_code': 'myfile_fixed.py',
        'output_results': 'myfile_fix_results.log'
    }
    mock_mkdir.assert_not_called()

@patch('pathlib.Path.mkdir')
def test_split_command(mock_mkdir):
    result = generate_output_paths('split', {}, 'myfile', 'python', '.py')
    assert result == {
        'output_sub': 'sub_myfile.prompt',
        'output_modified': 'modified_myfile.prompt'
    }
    mock_mkdir.assert_not_called()

@patch('pathlib.Path.mkdir')
def test_change_command(mock_mkdir):
    result = generate_output_paths('change', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'modified_myfile.prompt'}
    mock_mkdir.assert_not_called()

@patch('pathlib.Path.mkdir')
def test_update_command(mock_mkdir):
    result = generate_output_paths('update', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'modified_myfile.prompt'}
    mock_mkdir.assert_not_called()

@patch('pathlib.Path.mkdir')
def test_detect_command(mock_mkdir):
    result = generate_output_paths('detect', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'myfile_detect.csv'}
    mock_mkdir.assert_not_called()

@patch('pathlib.Path.mkdir')
def test_conflicts_command(mock_mkdir):
    result = generate_output_paths('conflicts', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'myfile_conflict.csv'}
    mock_mkdir.assert_not_called()

@patch('pathlib.Path.mkdir')
def test_crash_command(mock_mkdir):
    result = generate_output_paths('crash', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'myfile_fixed.py'}
    mock_mkdir.assert_not_called()

@patch('pathlib.Path.mkdir')
def test_fix_command_with_custom_output(mock_mkdir):
    result = generate_output_paths('fix', {'output_test': '/custom/test.py', 'output_code': '/custom/code.py'}, 'myfile', 'python', '.py')
    assert result == {
        'output_test': '/custom/test.py',
        'output_code': '/custom/code.py',
        'output_results': 'myfile_fix_results.log'
    }
    expected_calls = [
        call(parents=True, exist_ok=True),
        call(parents=True, exist_ok=True)
    ]
    mock_mkdir.assert_has_calls(expected_calls, any_order=True)

@patch('pathlib.Path.mkdir')
def test_generate_command_with_environment_variable(mock_mkdir, setup_environment):
    result = generate_output_paths('generate', {}, 'myfile', 'python', '.py')
    assert result == {'output': '/env/path/generate/myfile.py'}
    mock_mkdir.assert_called_once_with(parents=True, exist_ok=True)

@patch('pathlib.Path.mkdir')
def test_fix_command_with_environment_variables(mock_mkdir, setup_environment):
    result = generate_output_paths('fix', {}, 'myfile', 'python', '.py')
    assert result == {
        'output_test': '/env/path/fix_test/test_myfile_fixed.py',
        'output_code': '/env/path/fix_code/myfile_fixed.py',
        'output_results': 'myfile_fix_results.log'
    }
    expected_calls = [
        call(parents=True, exist_ok=True),
        call(parents=True, exist_ok=True)
    ]
    mock_mkdir.assert_has_calls(expected_calls, any_order=True)

def test_invalid_command():
    with pytest.raises(ValueError):
        generate_output_paths('invalid_command', {}, 'myfile', 'python', '.py')

@patch('pathlib.Path.mkdir')
def test_missing_file_extension(mock_mkdir):
    result = generate_output_paths('generate', {}, 'myfile', 'python', '')
    assert result == {'output': 'myfile'}
    mock_mkdir.assert_not_called()

@patch('pathlib.Path.mkdir')
def test_missing_language(mock_mkdir):
    result = generate_output_paths('preprocess', {}, 'myfile', '', '.py')
    assert result == {'output': 'myfile__preprocessed.prompt'}
    mock_mkdir.assert_not_called()
