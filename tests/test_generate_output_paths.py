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
    assert result == {
        'output': 'myfile_fixed.py',
        'output_program': 'myfile_fixed.py'
    }
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


def test_generate_output_paths():
    """
    Unit tests for the generate_output_paths function.
    Covers various scenarios and edge cases to ensure correctness.
    """
    # Test case 1: 'generate' command with a directory in output_locations
    command = 'generate'
    output_locations = {'output': 'output_dir/'}
    basename = 'example'
    language = 'python'
    file_extension = '.py'

    expected_output = {'output': os.path.join('output_dir', 'example.py')}
    assert generate_output_paths(command, output_locations, basename, language, file_extension) == expected_output

    # Test case 2: 'example' command with environment variable override
    command = 'example'
    output_locations = {'output': None}
    basename = 'example'
    language = 'python'
    file_extension = '.py'

    with patch.dict(os.environ, {'PDD_EXAMPLE_OUTPUT_PATH': 'env_output_dir'}):
        expected_output = {'output': os.path.join('env_output_dir', 'example_example.py')}
        assert generate_output_paths(command, output_locations, basename, language, file_extension) == expected_output

    # Test case 3: 'test' command with default naming convention
    command = 'test'
    output_locations = {'output': None}
    basename = 'example'
    language = 'python'
    file_extension = '.py'

    expected_output = {'output': 'test_example.py'}
    assert generate_output_paths(command, output_locations, basename, language, file_extension) == expected_output

    # Test case 4: 'fix' command with multiple outputs
    command = 'fix'
    output_locations = {'output_test': 'fix_output_dir/', 'output_code': None, 'output_results': None}
    basename = 'example'
    language = 'python'
    file_extension = '.py'

    expected_output = {
        'output_test': os.path.join('fix_output_dir', 'test_example_fixed.py'),
        'output_code': 'example_fixed.py',
        'output_results': 'example_fix_results.log'
    }
    assert generate_output_paths(command, output_locations, basename, language, file_extension) == expected_output

    # Test case 5: 'split' command with missing keys in output_locations
    command = 'split'
    output_locations = {}
    basename = 'example'
    language = 'python'
    file_extension = '.py'

    expected_output = {
        'output_sub': 'sub_example.prompt',
        'output_modified': 'modified_example.prompt'
    }
    assert generate_output_paths(command, output_locations, basename, language, file_extension) == expected_output

    # Test case 6: 'crash' command with environment variable override
    command = 'crash'
    output_locations = {'output': None, 'output_program': None}
    basename = 'example'
    language = 'python'
    file_extension = '.py'

    with patch.dict(os.environ, {'PDD_CRASH_OUTPUT_PATH': 'crash_output_dir'}):
        expected_output = {
            'output': os.path.join('crash_output_dir', 'example_fixed.py'),
            'output_program': 'example_fixed.py'
        }
        assert generate_output_paths(command, output_locations, basename, language, file_extension) == expected_output

    # Test case 7: 'bug' command with default naming convention
    command = 'bug'
    output_locations = {'output': None}
    basename = 'example'
    language = 'python'
    file_extension = '.py'

    expected_output = {'output': 'test_example_bug.py'}
    assert generate_output_paths(command, output_locations, basename, language, file_extension) == expected_output

    # Test case 8: 'auto-deps' command with environment variable override
    command = 'auto-deps'
    output_locations = {'output': None}
    basename = 'example'
    language = 'python'
    file_extension = '.py'

    with patch.dict(os.environ, {'PDD_AUTO_DEPS_OUTPUT_PATH': 'auto_deps_output_dir'}):
        expected_output = {'output': os.path.join('auto_deps_output_dir', 'example_with_deps.prompt')}
        assert generate_output_paths(command, output_locations, basename, language, file_extension) == expected_output

    # Test case 9: Invalid command should raise ValueError
    command = 'invalid_command'
    output_locations = {'output': None}
    basename = 'example'
    language = 'python'
    file_extension = '.py'

    with pytest.raises(ValueError):
        generate_output_paths(command, output_locations, basename, language, file_extension)