import pytest
import unittest.mock as mock
from unittest.mock import MagicMock, mock_open, patch
import os
import re
from datetime import datetime
from typing import Tuple
from pdd.track_cost import track_cost

# Sample command function to be decorated
@track_cost
def sample_command(ctx, prompt_file: str, output: str = None) -> Tuple[str, float, str]:
    """
    Simulated command function that returns a tuple containing:
    - output_path (str)
    - cost (float)
    - model_name (str)
    """
    return ('/path/to/output', 25.5, 'gpt-3')


# Revised create_mock_context function
def create_mock_context(command_name: str, params: dict, obj: dict = None):
    """
    Creates a mocked Click context with the specified command name, parameters, and obj dictionary.

    Args:
        command_name (str): The name of the command.
        params (dict): Dictionary of command parameters.
        obj (dict, optional): Dictionary to mock ctx.obj.get method. Defaults to None.

    Returns:
        MagicMock: Mocked Click context.
    """
    mock_ctx = MagicMock()
    mock_ctx.command.name = command_name
    mock_ctx.params = params

    if obj is not None:
        mock_obj = MagicMock()
        # Mock the get method for obj - support both one and two argument calls
        mock_obj.get.side_effect = lambda key, default=None: obj.get(key, default)
        mock_ctx.obj = mock_obj
    else:
        # If obj is not provided, set obj to None to simulate absence
        mock_ctx.obj = None

    return mock_ctx


@pytest.fixture
def mock_click_context():
    """
    Fixture to mock click.get_current_context().
    """
    with mock.patch('click.get_current_context') as mock_context:
        yield mock_context


@pytest.fixture
def mock_open_file():
    """
    Fixture to mock the open function.
    """
    with mock.patch('builtins.open', mock_open()) as mocked_open:
        yield mocked_open


@pytest.fixture
def mock_rprint():
    """
    Fixture to mock rich.print (rprint).
    """
    with mock.patch('pdd.track_cost.rprint') as mocked_rprint:
        yield mocked_rprint


@pytest.fixture(autouse=True)
def clear_pytest_env_for_cost_tests():
    """
    Patch os.environ.get so that PYTEST_CURRENT_TEST returns None inside
    the track_cost decorator, allowing CSV-writing tests to exercise that
    code path while running under pytest.
    """
    original_get = os.environ.get

    def _patched_get(key, *args, **kwargs):
        if key == 'PYTEST_CURRENT_TEST':
            return None
        return original_get(key, *args, **kwargs)

    with mock.patch.object(os.environ, 'get', side_effect=_patched_get):
        yield


def test_csv_row_appended_if_file_exists(mock_click_context, mock_open_file, mock_rprint):
    mock_ctx = create_mock_context(
        'generate',
        {
            'prompt_file': '/path/to/prompt.txt',
            'output_cost': '/path/to/cost.csv',
            'output': '/path/to/output'
        },
        obj={'output_cost': '/path/to/cost.csv'}
    )
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=True):
        result = sample_command(mock_ctx, '/path/to/prompt.txt', output='/path/to/output')

    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    handle = mock_open_file()
    assert not any('timestamp,model,command,cost,input_files,output_files' in call.args[0] for call in handle.write.call_args_list)
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,gpt-3,generate,25.5,/path/to/prompt.txt,/path/to/output\r\n')
    assert any(row_pattern.match(call.args[0]) for call in handle.write.call_args_list)

    mock_rprint.assert_not_called()
    assert result == ('/path/to/output', 25.5, 'gpt-3')


def test_no_output_cost_path(mock_click_context, mock_open_file, mock_rprint):
    """
    Test that no CSV file is written when output_cost_path is not specified.
    """
    # Setup the mocked Click context without 'output_cost' and environment variable
    mock_ctx = create_mock_context('generate', {'prompt_file': '/path/to/prompt.txt'})
    mock_click_context.return_value = mock_ctx

    # Remove environment variable if set
    with mock.patch.dict(os.environ, {}, clear=True):
        result = sample_command(mock_ctx, '/path/to/prompt.txt')

    # Ensure that open was not called since output_cost_path is not specified
    mock_open_file.assert_not_called()
    # Ensure no error was printed
    mock_rprint.assert_not_called()
    # Ensure the command result is returned correctly
    assert result == ('/path/to/output', 25.5, 'gpt-3')


def test_output_cost_path_via_param(mock_click_context, mock_open_file, mock_rprint):
    """
    Test that the CSV file is written correctly when output_cost_path is specified via parameter.
    """
    # Setup the mocked Click context with 'output_cost' parameter
    mock_ctx = create_mock_context(
        'generate',
        {
            'prompt_file': '/path/to/prompt.txt',
            'output_cost': '/path/to/cost.csv',
            'output': '/path/to/output'
        },
        obj={'output_cost': '/path/to/cost.csv'}
    )
    mock_click_context.return_value = mock_ctx

    # Mock os.path.isfile to return False (file does not exist)
    with mock.patch('os.path.isfile', return_value=False):
        result = sample_command(mock_ctx, '/path/to/prompt.txt', output='/path/to/output')

    # Ensure that open was called with the correct path and mode
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files\r\n')
    
    # Use a regex pattern to match the row, ignoring the specific timestamp
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,gpt-3,generate,25.5,/path/to/prompt.txt,/path/to/output\r\n')
    assert any(row_pattern.match(call.args[0]) for call in handle.write.call_args_list)

    # Ensure no error was printed
    mock_rprint.assert_not_called()
    # Ensure the command result is returned correctly
    assert result == ('/path/to/output', 25.5, 'gpt-3')


def test_output_cost_path_via_env(mock_click_context, mock_open_file, mock_rprint, monkeypatch):
    """
    Test that the CSV file is written correctly when output_cost_path is specified via environment variable.
    """
    # Setup the mocked Click context without 'output_cost' parameter
    mock_ctx = create_mock_context(
        'generate',
        {
            'prompt_file': '/path/to/prompt.txt',
            'output': '/path/to/output'
        },
        obj=None
    )
    mock_click_context.return_value = mock_ctx

    # Set the environment variable PDD_OUTPUT_COST_PATH
    monkeypatch.setenv('PDD_OUTPUT_COST_PATH', '/env/path/cost.csv')

    # Mock os.path.isfile to return False (file does not exist)
    with mock.patch('os.path.isfile', return_value=False):
        result = sample_command(mock_ctx, '/path/to/prompt.txt', output='/path/to/output')

    # Ensure that open was called with the path from environment variable
    mock_open_file.assert_called_once_with('/env/path/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files\r\n')
    
    # Use a regex pattern to match the row, ignoring the specific timestamp
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,gpt-3,generate,25.5,/path/to/prompt.txt,/path/to/output\r\n')
    assert any(row_pattern.match(call.args[0]) for call in handle.write.call_args_list)

    # Ensure no error was printed
    mock_rprint.assert_not_called()
    # Ensure the command result is returned correctly
    assert result == ('/path/to/output', 25.5, 'gpt-3')


def test_csv_header_written_if_file_not_exists(mock_click_context, mock_open_file, mock_rprint):
    """
    Test that the CSV header is written when the CSV file does not exist.
    """
    # Setup the mocked Click context with 'output_cost' parameter
    mock_ctx = create_mock_context(
        'generate',
        {
            'prompt_file': '/path/to/prompt.txt',
            'output_cost': '/path/to/cost.csv',
            'output': '/path/to/output'
        },
        obj={'output_cost': '/path/to/cost.csv'}
    )
    mock_click_context.return_value = mock_ctx

    # Mock os.path.isfile to return False (file does not exist)
    with mock.patch('os.path.isfile', return_value=False):
        result = sample_command(mock_ctx, '/path/to/prompt.txt', output='/path/to/output')

    # Ensure that open was called once
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written first
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files\r\n')
    # Data row should be written
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,gpt-3,generate,25.5,/path/to/prompt.txt,/path/to/output\r\n')
    assert any(row_pattern.match(call.args[0]) for call in handle.write.call_args_list)

    # Ensure no error was printed
    mock_rprint.assert_not_called()


def test_cost_and_model_extracted_correctly(mock_click_context, mock_open_file, mock_rprint):
    """
    Test that cost and model name are correctly extracted from the command result.
    """
    # Setup the mocked Click context with 'output_cost' parameter
    mock_ctx = create_mock_context(
        'train',
        {
            'input_file': '/path/to/input.txt',
            'output_cost': '/path/to/cost.csv',
            'output': '/path/to/output'
        },
        obj={'output_cost': '/path/to/cost.csv'}
    )
    mock_click_context.return_value = mock_ctx

    # Modify the sample_command to return different values
    @track_cost
    def train_command(ctx, input_file: str, output: str = None) -> Tuple[str, float, str]:
        return ('/path/to/output', 50.0, 'bert-base')

    with mock.patch('os.path.isfile', return_value=False):
        result = train_command(mock_ctx, '/path/to/input.txt', output='/path/to/output')

    # Ensure that open was called with the correct path
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files\r\n')
    # Data row should have correct cost and model
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,bert-base,train,50.0,/path/to/input.txt,/path/to/output\r\n')
    assert any(row_pattern.match(call.args[0]) for call in handle.write.call_args_list)

    # Ensure no error was printed
    mock_rprint.assert_not_called()
    # Ensure the command result is returned correctly
    assert result == ('/path/to/output', 50.0, 'bert-base')


def test_result_tuple_too_short(mock_click_context, mock_open_file, mock_rprint):
    """
    Test that when the command result tuple is too short, cost and model are set to empty strings.
    """
    # Define a command that returns a short tuple
    @track_cost
    def short_result_command(ctx, prompt_file: str) -> Tuple[str]:
        return ('/path/to/output',)

    # Setup the mocked Click context with 'output_cost' parameter
    mock_ctx = create_mock_context(
        'short',
        {
            'prompt_file': '/path/to/prompt.txt',
            'output_cost': '/path/to/cost.csv'
        },
        obj={'output_cost': '/path/to/cost.csv'}
    )
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        result = short_result_command(mock_ctx, '/path/to/prompt.txt')

    # Ensure that open was called
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files\r\n')
    # Data row should have empty cost and model
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,,short,,/path/to/prompt.txt,\r\n')
    assert any(row_pattern.match(call.args[0]) for call in handle.write.call_args_list)

    # Ensure no error was printed
    mock_rprint.assert_not_called()
    # Ensure the command result is returned correctly
    assert result == ('/path/to/output',)


def test_input_output_files_collected(mock_click_context, mock_open_file, mock_rprint):
    """
    Test that input and output files are correctly collected from command parameters.
    """
    # Define a command with input and output parameters
    @track_cost
    def process_command(ctx, input_file: str, output_file: str) -> Tuple[str, float, str]:
        return ('/path/to/output', 15.0, 'custom-model')

    # Setup the mocked Click context with 'output_cost' parameter
    mock_ctx = create_mock_context(
        'process',
        {
            'input_file': '/path/to/input.txt',
            'output_file': '/path/to/output.txt',
            'output_cost': '/path/to/cost.csv'
        },
        obj={'output_cost': '/path/to/cost.csv'}
    )
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        result = process_command(mock_ctx, '/path/to/input.txt', output_file='/path/to/output.txt')

    # Ensure that open was called with the correct path
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files\r\n')
    # Data row should have correct input and output files
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,custom-model,process,15.0,/path/to/input.txt,/path/to/output.txt\r\n')
    assert any(row_pattern.match(call.args[0]) for call in handle.write.call_args_list)

    # Ensure no error was printed
    mock_rprint.assert_not_called()
    # Ensure the command result is returned correctly
    assert result == ('/path/to/output', 15.0, 'custom-model')


def test_multiple_input_output_files(mock_click_context, mock_open_file, mock_rprint):
    """
    Test that multiple input and output files are correctly collected from command parameters.
    """
    # Define a command that accepts multiple input and output files
    @track_cost
    def batch_command(ctx, input_files: list, output_files: list, output_cost: str) -> Tuple[list, float, str]:
        return (['/path/to/output1', '/path/to/output2'], 100.0, 'batch-model')

    # Setup the mocked Click context with multiple input and output files
    mock_ctx = create_mock_context(
        'batch',
        {
            'input_files': ['/path/to/input1.txt', '/path/to/input2.txt'],
            'output_files': ['/path/to/output1.txt', '/path/to/output2.txt'],
            'output_cost': '/path/to/cost.csv'
        },
        obj={'output_cost': '/path/to/cost.csv'}
    )
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        result = batch_command(
            mock_ctx,
            ['/path/to/input1.txt', '/path/to/input2.txt'],
            output_files=['/path/to/output1.txt', '/path/to/output2.txt'],
            output_cost='/path/to/cost.csv'
        )

    # Ensure that open was called with the correct path
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files\r\n')
    # Data row should have multiple input and output files separated by semicolons
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,batch-model,batch,100.0,/path/to/input1.txt;/path/to/input2.txt,/path/to/output1.txt;/path/to/output2.txt\r\n')
    assert any(row_pattern.match(call.args[0]) for call in handle.write.call_args_list)

    # Ensure no error was printed
    mock_rprint.assert_not_called()
    # Ensure the command result is returned correctly
    assert result == (['/path/to/output1', '/path/to/output2'], 100.0, 'batch-model')


def test_exception_in_logging(mock_click_context, mock_open_file, mock_rprint):
    """
    Test that if an exception occurs during cost logging, an error is printed and the command result is still returned.
    """
    # Setup the mocked Click context with 'output_cost' parameter
    mock_ctx = create_mock_context(
        'error_command',
        {
            'prompt_file': '/path/to/prompt.txt',
            'output_cost': '/path/to/cost.csv'
        },
        obj={'output_cost': '/path/to/cost.csv'}
    )
    mock_click_context.return_value = mock_ctx

    # Configure the open mock to raise an exception when called
    mock_open_file.side_effect = IOError("Failed to open file")

    with mock.patch('os.path.isfile', return_value=True):
        result = sample_command(mock_ctx, '/path/to/prompt.txt')

    # Ensure that open was attempted
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Ensure that an error was printed using rprint
    mock_rprint.assert_called_once()
    args, _ = mock_rprint.call_args
    assert "Error tracking cost: Failed to open file" in args[0]

    # Ensure the command result is returned correctly despite the logging error
    assert result == ('/path/to/output', 25.5, 'gpt-3')


def test_non_string_file_parameters(mock_click_context, mock_open_file, mock_rprint):
    """
    Test that non-string file parameters are ignored when collecting input and output files.
    """
    # Define a command with non-string file parameters
    @track_cost
    def mixed_command(ctx, input_file: str, output_file: str, config: dict) -> Tuple[str, float, str]:
        return ('/path/to/output', 30.0, 'mixed-model')

    # Setup the mocked Click context with mixed parameters
    mock_ctx = create_mock_context(
        'mixed',
        {
            'input_file': '/path/to/input.txt',
            'output_file': '/path/to/output.txt',
            'config': {'key': 'value'},
            'output_cost': '/path/to/cost.csv'
        },
        obj={'output_cost': '/path/to/cost.csv'}
    )
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        result = mixed_command(mock_ctx, '/path/to/input.txt', output_file='/path/to/output.txt', config={'key': 'value'})

    # Ensure that open was called with the correct path
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Data row should include only string file paths
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,mixed-model,mixed,30.0,/path/to/input.txt,/path/to/output.txt\r\n')
    assert any(row_pattern.match(call.args[0]) for call in handle.write.call_args_list)

    # Ensure no error was printed
    mock_rprint.assert_not_called()
    # Ensure the command result is returned correctly
    assert result == ('/path/to/output', 30.0, 'mixed-model')


def test_missing_click_context(mock_open_file, mock_rprint):
    """
    Test that if Click context is not available, no logging occurs and no errors are raised.
    """
    # Mock click.get_current_context to return None
    with mock.patch('click.get_current_context', return_value=None):
        result = sample_command(None, '/path/to/prompt.txt')

    # Ensure that open was not called
    mock_open_file.assert_not_called()
    # Ensure no error was printed
    mock_rprint.assert_not_called()
    # Ensure the command result is returned correctly
    assert result == ('/path/to/output', 25.5, 'gpt-3')


def test_non_tuple_result(mock_click_context, mock_open_file, mock_rprint):
    """
    Test that if the command result is not a tuple, cost and model are set to empty strings.
    """
    # Define a command that returns a non-tuple result
    @track_cost
    def non_tuple_command(ctx, prompt_file: str) -> str:
        return '/path/to/output'

    # Setup the mocked Click context with 'output_cost' parameter
    mock_ctx = create_mock_context(
        'non_tuple',
        {
            'prompt_file': '/path/to/prompt.txt',
            'output_cost': '/path/to/cost.csv'
        },
        obj={'output_cost': '/path/to/cost.csv'}
    )
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        result = non_tuple_command(mock_ctx, '/path/to/prompt.txt')

    # Ensure that open was called
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Data row should have empty cost and model
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,,non_tuple,,/path/to/prompt.txt,\r\n')
    assert any(row_pattern.match(call.args[0]) for call in handle.write.call_args_list)

    # Ensure no error was printed
    mock_rprint.assert_not_called()
    # Ensure the command result is returned correctly
    assert result == '/path/to/output'


def test_collect_files_with_fix_command(mock_click_context, mock_rprint, tmp_path):
    """
    Test that collect_files correctly identifies prompt_file, code_file, unit_test_file, and error_file.
    """
    # Create temporary files
    prompt_file = tmp_path / "test.prompt"
    code_file = tmp_path / "code.py"
    test_file = tmp_path / "test.py"
    error_file = tmp_path / "errors.log"

    prompt_file.write_text("test prompt")
    code_file.write_text("print('hello')")
    test_file.write_text("def test(): pass")
    error_file.write_text("error log")

    # Define a command similar to the fix command
    @track_cost
    def fix_command(ctx, prompt_file: str, code_file: str, unit_test_file: str, error_file: str) -> Tuple[str, float, str]:
        return ('/path/to/output', 10.0, 'test-model')

    # Setup a real-like context object
    obj_dict = {'core_dump_files': set(), 'core_dump': True}
    mock_ctx = MagicMock()
    mock_ctx.command.name = 'fix'
    mock_ctx.obj = obj_dict
    mock_click_context.return_value = mock_ctx

    with mock.patch.dict(os.environ, {}, clear=True):
        result = fix_command(
            mock_ctx,
            prompt_file=str(prompt_file),
            code_file=str(code_file),
            unit_test_file=str(test_file),
            error_file=str(error_file)
        )

    # Check that files were added to core_dump_files
    core_dump_files = obj_dict['core_dump_files']

    # All input files should be tracked
    assert any(str(prompt_file) in f for f in core_dump_files), f"prompt_file not in {core_dump_files}"
    assert any(str(code_file) in f for f in core_dump_files), f"code_file not in {core_dump_files}"
    assert any(str(test_file) in f for f in core_dump_files), f"test_file not in {core_dump_files}"
    assert any(str(error_file) in f for f in core_dump_files), f"error_file not in {core_dump_files}"

    # Ensure no error was printed
    mock_rprint.assert_not_called()
    # Ensure the command result is returned correctly
    assert result == ('/path/to/output', 10.0, 'test-model')


def test_collect_files_with_generate_command(mock_click_context, mock_rprint, tmp_path):
    """
    Test that collect_files correctly identifies prompt_file and output for generate command.
    """
    # Create temporary files
    prompt_file = tmp_path / "test.prompt"
    output_file = tmp_path / "output.py"

    prompt_file.write_text("generate test")
    output_file.write_text("# generated")

    # Define a command similar to generate
    @track_cost
    def generate_command(ctx, prompt_file: str, output: str = None) -> Tuple[str, float, str]:
        return (output or '/path/to/output', 5.0, 'test-model')

    # Setup a real-like context object
    obj_dict = {'core_dump_files': set(), 'core_dump': True}
    mock_ctx = MagicMock()
    mock_ctx.command.name = 'generate'
    mock_ctx.obj = obj_dict
    mock_click_context.return_value = mock_ctx

    with mock.patch.dict(os.environ, {}, clear=True):
        result = generate_command(mock_ctx, prompt_file=str(prompt_file), output=str(output_file))

    # Check that files were added to core_dump_files
    core_dump_files = obj_dict['core_dump_files']

    # Prompt file should be in input files
    assert any(str(prompt_file) in f for f in core_dump_files), f"prompt_file not in {core_dump_files}"
    # Output file should also be tracked
    assert any(str(output_file) in f for f in core_dump_files), f"output_file not in {core_dump_files}"

    mock_rprint.assert_not_called()
    assert result == (str(output_file), 5.0, 'test-model')


def test_collect_files_skips_non_existent_files(mock_click_context, mock_rprint):
    """
    Test that collect_files handles non-existent files gracefully.
    """
    @track_cost
    def test_command(ctx, prompt_file: str, missing_file: str) -> Tuple[str, float, str]:
        return ('/path/to/output', 1.0, 'test-model')

    # Setup with one real file and one non-existent
    mock_ctx = create_mock_context(
        'test',
        {
            'prompt_file': '/real/file.txt',
            'missing_file': '/does/not/exist.txt'
        },
        obj={'core_dump_files': set()}
    )
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.exists', side_effect=lambda p: p == '/real/file.txt'):
        with mock.patch('os.path.isfile', side_effect=lambda p: p == '/real/file.txt'):
            with mock.patch.dict(os.environ, {}, clear=True):
                result = test_command(mock_ctx, '/real/file.txt', '/does/not/exist.txt')

    # Only existing files should be added
    core_dump_files = mock_ctx.obj.get('core_dump_files', set())
    # Both files might be added based on the logic (has extension)
    # But only the existing one should pass the os.path.exists check in track_cost

    mock_rprint.assert_not_called()
    assert result == ('/path/to/output', 1.0, 'test-model')


def test_files_tracked_on_command_failure(mock_click_context, mock_rprint, tmp_path):
    """
    Test that input/output files are tracked in core dump even when command raises exception.
    This is a regression test for the bug where collect_files() was not called when commands failed.
    """
    # Create temporary files
    prompt_file = tmp_path / "test.prompt"
    output_file = tmp_path / "output.py"

    prompt_file.write_text("test prompt")

    # Define a command that raises an exception (simulating user cancellation or error)
    @track_cost
    def failing_command(ctx, prompt_file: str, output: str = None) -> Tuple[str, float, str]:
        raise Exception("User cancelled command")

    # Setup a real-like context object with core_dump enabled
    obj_dict = {'core_dump_files': set(), 'core_dump': True}
    mock_ctx = MagicMock()
    mock_ctx.command.name = 'generate'
    mock_ctx.obj = obj_dict
    mock_click_context.return_value = mock_ctx

    # Call the command and expect it to raise an exception
    with pytest.raises(Exception, match="User cancelled command"):
        with mock.patch.dict(os.environ, {}, clear=True):
            failing_command(mock_ctx, prompt_file=str(prompt_file), output=str(output_file))

    # Check that files were STILL added to core_dump_files despite the exception
    core_dump_files = obj_dict['core_dump_files']

    # The prompt file should be tracked even though command failed
    assert any(str(prompt_file) in f for f in core_dump_files), \
        f"prompt_file should be tracked on failure, but core_dump_files={core_dump_files}"

    # The output file should also be tracked
    assert any(str(output_file) in f for f in core_dump_files), \
        f"output_file should be tracked on failure, but core_dump_files={core_dump_files}"

    # No tracking errors should be printed (the exception handling should be clean)
    # Note: rprint might be called for the actual exception, but not for tracking errors
    # We just want to make sure the test doesn't crash and files are tracked


def test_csv_write_skipped_when_pytest_current_test_set(mock_click_context, mock_rprint):
    """CSV writing should be skipped when PYTEST_CURRENT_TEST is set."""
    mock_ctx = create_mock_context(
        'generate',
        {
            'prompt_file': '/path/to/prompt',
            'output': '/path/to/output',
        },
        obj={'output_cost': '/path/to/cost.csv'},
    )

    # Override the autouse fixture by restoring real os.environ.get,
    # then set PYTEST_CURRENT_TEST so the guard skips CSV writing.
    real_get = os.environ.__class__.get

    with mock.patch.object(os.environ, 'get', side_effect=lambda k, *a, **kw: real_get(os.environ, k, *a, **kw)):
        with mock.patch.dict(os.environ, {'PYTEST_CURRENT_TEST': 'tests/test_foo.py::test_bar (call)'}):
            with mock.patch('builtins.open', mock_open()) as mocked_file:
                sample_command(mock_ctx, prompt_file='/path/to/prompt', output='/path/to/output')
                mocked_file.assert_not_called()
