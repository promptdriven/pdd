import pytest
import os
from pathlib import Path
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

def test_generate_command_default():
    result = generate_output_paths('generate', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'myfile.py'}

def test_generate_command_with_output_location():
    result = generate_output_paths('generate', {'output': '/custom/path/output.py'}, 'myfile', 'python', '.py')
    assert result == {'output': '/custom/path/output.py'}

def test_generate_command_with_output_directory():
    result = generate_output_paths('generate', {'output': '/custom/directory'}, 'myfile', 'python', '.py')
    assert result == {'output': '/custom/directory/myfile.py'}

def test_example_command():
    result = generate_output_paths('example', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'myfile_example.py'}

def test_test_command():
    result = generate_output_paths('test', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'test_myfile.py'}

def test_preprocess_command():
    result = generate_output_paths('preprocess', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'myfile_python_preprocessed.prompt'}

def test_fix_command():
    result = generate_output_paths('fix', {}, 'myfile', 'python', '.py')
    assert result == {
        'output_test': 'test_myfile_fixed.py',
        'output_code': 'myfile_fixed.py'
    }

def test_split_command():
    result = generate_output_paths('split', {}, 'myfile', 'python', '.py')
    assert result == {
        'output_sub': 'sub_myfile.prompt',
        'output_modified': 'modified_myfile.prompt'
    }

def test_change_command():
    result = generate_output_paths('change', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'modified_myfile.prompt'}

def test_update_command():
    result = generate_output_paths('update', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'modified_myfile.prompt'}

def test_detect_command():
    result = generate_output_paths('detect', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'myfile_detect.csv'}

def test_conflicts_command():
    result = generate_output_paths('conflicts', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'myfile_conflict.csv'}

def test_crash_command():
    result = generate_output_paths('crash', {}, 'myfile', 'python', '.py')
    assert result == {'output': 'myfile_fixed.py'}

def test_fix_command_with_custom_output():
    result = generate_output_paths('fix', {'output_test': '/custom/test.py', 'output_code': '/custom/code.py'}, 'myfile', 'python', '.py')
    assert result == {
        'output_test': '/custom/test.py',
        'output_code': '/custom/code.py'
    }

def test_generate_command_with_environment_variable(setup_environment):
    result = generate_output_paths('generate', {}, 'myfile', 'python', '.py')
    assert result == {'output': '/env/path/generate/myfile.py'}

def test_fix_command_with_environment_variables(setup_environment):
    result = generate_output_paths('fix', {}, 'myfile', 'python', '.py')
    assert result == {
        'output_test': '/env/path/fix_test/test_myfile_fixed.py',
        'output_code': '/env/path/fix_code/myfile_fixed.py'
    }

def test_invalid_command():
    with pytest.raises(KeyError):
        generate_output_paths('invalid_command', {}, 'myfile', 'python', '.py')

def test_missing_file_extension():
    result = generate_output_paths('generate', {}, 'myfile', 'python', '')
    assert result == {'output': 'myfile'}

def test_missing_language():
    result = generate_output_paths('preprocess', {}, 'myfile', '', '.py')
    assert result == {'output': 'myfile__preprocessed.prompt'}
