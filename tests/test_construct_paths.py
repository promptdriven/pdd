import pytest
from pathlib import Path
import os
import click
from pdd.construct_paths import construct_paths, extract_basename, extract_language

# Mock the generate_output_paths function
@pytest.fixture
def mock_generate_output_paths(monkeypatch):
    def mock_func(command, output_locations, basename, language, file_extension):
        return {
            'output': f'/path/to/{basename}.{file_extension}',
            'test_output': f'/path/to/{basename}_test.{file_extension}'
        }
    monkeypatch.setattr('pdd.construct_paths.generate_output_paths', mock_func)

# Mock the get_extension function
@pytest.fixture
def mock_get_extension(monkeypatch):
    def mock_func(language):
        return 'py' if language == 'python' else 'txt'
    monkeypatch.setattr('pdd.construct_paths.get_extension', mock_func)

# Mock the get_language function
@pytest.fixture
def mock_get_language(monkeypatch):
    def mock_func(extension):
        return 'python' if extension == '.py' else 'txt'
    monkeypatch.setattr('pdd.construct_paths.get_language', mock_func)

@pytest.fixture
def temp_directory(tmp_path):
    return tmp_path

def test_extract_basename():
    assert extract_basename('/path/to/file_python.prompt', 'generate') == 'file'
    assert extract_basename('/path/to/file.py', 'detect') == 'file'
    assert extract_basename('/path/to/complex_file_name.txt', 'example') == 'complex_file_name'

def test_extract_language():
    assert extract_language('/path/to/file_python.prompt', {}) == 'python'
    assert extract_language('/path/to/file.py', {}) == 'python'
    assert extract_language('/path/to/file.txt', {'language': 'java'}) == 'java'

def test_construct_paths_basic(temp_directory, mock_generate_output_paths, mock_get_extension, mock_get_language):
    input_file = temp_directory / 'input_python.prompt'
    input_file.write_text('Sample input')
    
    input_file_paths = {'prompt_file': str(input_file)}
    force = False
    quiet = True
    command = 'generate'
    command_options = {'output': str(temp_directory / 'output.py')}

    input_strings, output_file_paths, language = construct_paths(
        input_file_paths, force, quiet, command, command_options
    )

    assert input_strings == {'prompt_file': 'Sample input'}
    assert output_file_paths == {
        'output': '/path/to/input.py',
        'test_output': '/path/to/input_test.py'
    }
    assert language == 'python'

def test_construct_paths_error_file(temp_directory, mock_generate_output_paths, mock_get_extension, mock_get_language):
    input_file = temp_directory / 'input.py'
    input_file.write_text('Sample input')
    error_file = temp_directory / 'error.txt'
    
    input_file_paths = {'code_file': str(input_file), 'error_file': str(error_file)}
    force = False
    quiet = True
    command = 'example'
    command_options = {}

    input_strings, output_file_paths, language = construct_paths(
        input_file_paths, force, quiet, command, command_options
    )

    assert 'code_file' in input_strings
    assert 'error_file' in input_strings
    assert input_strings['error_file'] == ''
    assert os.path.exists(error_file)

def test_construct_paths_force_overwrite(temp_directory, mock_generate_output_paths, mock_get_extension, mock_get_language, monkeypatch):
    input_file = temp_directory / 'input.py'
    input_file.write_text('Sample input')
    output_file = temp_directory / 'output.py'
    output_file.write_text('Existing output')
    
    input_file_paths = {'code_file': str(input_file)}
    force = True
    quiet = True
    command = 'example'
    command_options = {'output': str(output_file)}

    input_strings, output_file_paths, language = construct_paths(
        input_file_paths, force, quiet, command, command_options
    )

    assert 'code_file' in input_strings
    assert output_file_paths['output'] == '/path/to/input.py'
    assert language == 'python'

def test_construct_paths_user_confirmation(temp_directory, mock_generate_output_paths, mock_get_extension, mock_get_language, monkeypatch):
    input_file = temp_directory / 'input.py'
    input_file.write_text('Sample input')
    output_file = temp_directory / 'output.py'
    output_file.write_text('Existing output')
    
    input_file_paths = {'code_file': str(input_file)}
    force = False
    quiet = False
    command = 'example'
    command_options = {'output': str(output_file)}

    # Mock user input to confirm overwrite
    monkeypatch.setattr('click.confirm', lambda message, default: True)

    input_strings, output_file_paths, language = construct_paths(
        input_file_paths, force, quiet, command, command_options
    )

    assert 'code_file' in input_strings
    assert output_file_paths['output'] == '/path/to/input.py'
    assert language == 'python'

def test_construct_paths_user_cancellation(temp_directory, mock_generate_output_paths, mock_get_extension, mock_get_language, monkeypatch):
    input_file = temp_directory / 'input.py'
    input_file.write_text('Sample input')
    output_file = temp_directory / 'output.py'
    output_file.write_text('Existing output')
    
    input_file_paths = {'code_file': str(input_file)}
    force = False
    quiet = False
    command = 'example'
    command_options = {'output': str(output_file)}

    # Mock user input to cancel overwrite
    monkeypatch.setattr('click.confirm', lambda message, default: False)

    with pytest.raises(click.Abort):
        construct_paths(input_file_paths, force, quiet, command, command_options)

def test_construct_paths_input_file_not_found(temp_directory):
    input_file_paths = {'prompt_file': str(temp_directory / 'non_existent_file.txt')}
    force = False
    quiet = True
    command = 'generate'
    command_options = {}

    with pytest.raises(click.ClickException, match="Input file not found"):
        construct_paths(input_file_paths, force, quiet, command, command_options)

def test_construct_paths_detect_command(temp_directory, mock_generate_output_paths, mock_get_extension, mock_get_language):
    change_file = temp_directory / 'changes.txt'
    change_file.write_text('Sample changes')
    
    input_file_paths = {'change_file': str(change_file)}
    force = False
    quiet = True
    command = 'detect'
    command_options = {}

    input_strings, output_file_paths, language = construct_paths(
        input_file_paths, force, quiet, command, command_options
    )

    assert input_strings == {'change_file': 'Sample changes'}
    assert output_file_paths == {
        'output': '/path/to/changes.txt',
        'test_output': '/path/to/changes_test.txt'
    }
    assert language == 'txt'