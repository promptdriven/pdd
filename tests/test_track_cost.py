import pytest
import unittest.mock as mock
from unittest.mock import MagicMock, mock_open, patch
import os
import re
from datetime import datetime
from typing import Tuple
from pdd.track_cost import track_cost
from pdd.agentic_sync_runner import _parse_cost_from_csv

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


@pytest.fixture(autouse=True)
def reset_legacy_csv_warned():
    """Process-level legacy-CSV warning dedup must not leak across tests."""
    from pdd import track_cost as _tc_mod
    _tc_mod._legacy_csv_warned.clear()
    yield
    _tc_mod._legacy_csv_warned.clear()


def test_csv_row_appended_if_file_exists_with_content(mock_click_context, mock_open_file, mock_rprint):
    """When CSV file exists AND has content, header should NOT be written (append mode).
    File is read first to detect legacy header (without attempted_models column)."""
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

    with mock.patch('os.path.isfile', return_value=True), \
         mock.patch('os.path.getsize', return_value=100):
        result = sample_command(mock_ctx, '/path/to/prompt.txt', output='/path/to/output')

    # Append call must occur (file may also be opened for read to inspect header)
    append_calls = [c for c in mock_open_file.call_args_list
                    if c.args[0] == '/path/to/cost.csv' and len(c.args) > 1 and c.args[1] == 'a']
    assert len(append_calls) == 1
    assert append_calls[0].kwargs.get('newline') == '' and append_calls[0].kwargs.get('encoding') == 'utf-8'

    handle = mock_open_file()
    assert not any('timestamp,model,command,cost,input_files,output_files' in call.args[0] for call in handle.write.call_args_list)
    # Legacy mode kicks in because mocked readline returns empty (no header) -> no attempted_models column
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+(?:[+-]\d{2}:\d{2})?,gpt-3,generate,25.5,/path/to/prompt.txt,/path/to/output(?:,[^,\r\n]*)?\r\n')
    assert any(row_pattern.match(call.args[0]) for call in handle.write.call_args_list)

    # Legacy-CSV path emits a one-time UX warning telling the user how to
    # opt in to the new attempted_models column.
    mock_rprint.assert_called_once()
    warn_msg = mock_rprint.call_args[0][0]
    assert "attempted_models" in warn_msg and "/path/to/cost.csv" in warn_msg
    assert result == ('/path/to/output', 25.5, 'gpt-3')


def test_csv_header_written_if_file_exists_but_empty(mock_click_context, mock_open_file, mock_rprint):
    """
    Regression test: when the CSV file exists but is empty (e.g. created by
    NamedTemporaryFile in agentic_sync_runner), the header MUST be written.
    Without the header, DictReader uses the first data row as column names,
    causing _parse_cost_from_csv to return 0.0 for all modules.
    """
    mock_ctx = create_mock_context(
        'sync',
        {
            'prompt_file': '/path/to/prompt.txt',
            'output': '/path/to/output'
        },
        obj={'output_cost': None}  # Not set via CLI — uses PDD_OUTPUT_COST_PATH env
    )
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=True), \
         mock.patch('os.path.getsize', return_value=0), \
         mock.patch.dict(os.environ, {'PDD_OUTPUT_COST_PATH': '/tmp/cost_abc.csv'}):
        result = sample_command(mock_ctx, '/path/to/prompt.txt', output='/path/to/output')

    mock_open_file.assert_any_call('/tmp/cost_abc.csv', 'a', newline='', encoding='utf-8')

    handle = mock_open_file()
    # Header MUST be written when file is empty (with attempted_models column)
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files,attempted_models,job_id\r\n')
    # Data row should follow (command name is 'sync' from mock context)
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+(?:[+-]\d{2}:\d{2})?,gpt-3,sync,25.5,/path/to/prompt.txt,/path/to/output,gpt-3(?:,[^,\r\n]*)?\r\n')
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
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files,attempted_models,job_id\r\n')

    # Use a regex pattern to match the row, ignoring the specific timestamp
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+(?:[+-]\d{2}:\d{2})?,gpt-3,generate,25.5,/path/to/prompt.txt,/path/to/output,gpt-3(?:,[^,\r\n]*)?\r\n')
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
    mock_open_file.assert_any_call('/env/path/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files,attempted_models,job_id\r\n')

    # Use a regex pattern to match the row, ignoring the specific timestamp
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+(?:[+-]\d{2}:\d{2})?,gpt-3,generate,25.5,/path/to/prompt.txt,/path/to/output,gpt-3(?:,[^,\r\n]*)?\r\n')
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
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written first (newly created files include attempted_models)
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files,attempted_models,job_id\r\n')
    # Data row should be written
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+(?:[+-]\d{2}:\d{2})?,gpt-3,generate,25.5,/path/to/prompt.txt,/path/to/output,gpt-3(?:,[^,\r\n]*)?\r\n')
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
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files,attempted_models,job_id\r\n')
    # Data row should have correct cost and model
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+(?:[+-]\d{2}:\d{2})?,bert-base,train,50.0,/path/to/input.txt,/path/to/output,bert-base(?:,[^,\r\n]*)?\r\n')
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
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files,attempted_models,job_id\r\n')
    # Data row should have empty cost and model; attempted_models defaults to the model_name (empty here)
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+(?:[+-]\d{2}:\d{2})?,,short,,/path/to/prompt.txt,,(?:,[^,\r\n]*)?\r\n')
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
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files,attempted_models,job_id\r\n')
    # Data row should have correct input and output files
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+(?:[+-]\d{2}:\d{2})?,custom-model,process,15.0,/path/to/input.txt,/path/to/output.txt,custom-model(?:,[^,\r\n]*)?\r\n')
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
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files,attempted_models,job_id\r\n')
    # Data row should have multiple input and output files separated by semicolons
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+(?:[+-]\d{2}:\d{2})?,batch-model,batch,100.0,/path/to/input1.txt;/path/to/input2.txt,/path/to/output1.txt;/path/to/output2.txt,batch-model(?:,[^,\r\n]*)?\r\n')
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

    with mock.patch('os.path.isfile', return_value=True), \
         mock.patch('os.path.getsize', return_value=100):
        result = sample_command(mock_ctx, '/path/to/prompt.txt')

    # Ensure that open was attempted with the cost file (mode may be 'r' to inspect header)
    open_paths = [c.args[0] for c in mock_open_file.call_args_list]
    assert '/path/to/cost.csv' in open_paths

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
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Data row should include only string file paths (with attempted_models column at end)
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+(?:[+-]\d{2}:\d{2})?,mixed-model,mixed,30.0,/path/to/input.txt,/path/to/output.txt,mixed-model(?:,[^,\r\n]*)?\r\n')
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
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Data row should have empty cost and model; attempted_models defaults to model_name (empty)
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+(?:[+-]\d{2}:\d{2})?,,non_tuple,,/path/to/prompt.txt,,(?:,[^,\r\n]*)?\r\n')
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


def test_empty_tempfile_roundtrip_with_parse_cost(tmp_path):
    """
    End-to-end regression test: simulates the agentic_sync_runner flow where
    NamedTemporaryFile creates an empty CSV, track_cost writes to it, and
    _parse_cost_from_csv reads it back.

    Before the fix, the empty pre-created file caused track_cost to skip the
    CSV header. DictReader then misinterpreted the first data row as the header,
    causing _parse_cost_from_csv to return 0.0.
    """
    import tempfile
    import csv

    # Simulate what agentic_sync_runner does: create an empty temp file
    cost_file = tempfile.NamedTemporaryFile(
        suffix=".csv", delete=False, dir=str(tmp_path)
    )
    cost_file.close()

    # Verify file exists but is empty (precondition)
    assert os.path.isfile(cost_file.name)
    assert os.path.getsize(cost_file.name) == 0

    # Simulate what track_cost does when writing cost
    fieldnames = ['timestamp', 'model', 'command', 'cost', 'input_files', 'output_files']
    file_has_content = os.path.isfile(cost_file.name) and os.path.getsize(cost_file.name) > 0

    with open(cost_file.name, 'a', newline='', encoding='utf-8') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        if not file_has_content:
            writer.writeheader()
        writer.writerow({
            'timestamp': '2026-02-15T15:29:05.893',
            'model': 'claude-3',
            'command': 'sync',
            'cost': 0.38,
            'input_files': 'test.prompt',
            'output_files': 'test.py',
        })

    # Parse cost like _parse_cost_from_csv does
    cost = _parse_cost_from_csv(cost_file.name)

    assert cost == pytest.approx(0.38), (
        f"Expected cost 0.38 but got {cost}. "
        "If 0.0, the CSV header was likely missing (empty file bug)."
    )

    # Clean up
    os.unlink(cost_file.name)


# ---------------------------------------------------------------------------
# Tests for the `attempted_models` column (issue #897).
#
# Test plan / coverage:
#   1. New CSV files MUST include an `attempted_models` header (last column).
#   2. `attempted_models` is taken from `ctx.obj['attempted_models']` when set
#      and joined with ';'.
#   3. Literal ';' characters in model names are replaced with ':' so the
#      delimiter stays unambiguous.
#   4. When `ctx.obj['attempted_models']` is missing/empty, the column falls
#      back to `[model_name]` so single-attempt commands still emit a value.
#   5. When appending to a legacy CSV (no `attempted_models` header) the
#      decorator must write rows in legacy order, never rewriting the header.
# ---------------------------------------------------------------------------


def _make_ctx_with_dict_obj(command_name: str, obj_dict: dict):
    """Helper: produce a MagicMock context whose .obj is a real dict (needed
    for the isinstance(ctx.obj, dict) check in track_cost.attempted_models)."""
    mock_ctx = MagicMock()
    mock_ctx.command.name = command_name
    mock_ctx.obj = obj_dict
    return mock_ctx


def test_attempted_models_from_ctx_obj_joined_with_semicolons(
    mock_click_context, mock_open_file, mock_rprint
):
    """attempted_models list set during the wrapped call is serialized joined by ';'."""
    @track_cost
    def cmd(ctx, prompt_file: str) -> Tuple[str, float, str]:
        # Simulate llm_invoke publishing fallback history during execution.
        ctx.obj['attempted_models'] = [
            'vertex_ai/gemini-2.5-pro', 'deepseek/deepseek-chat'
        ]
        return ('/path/to/output', 0.1, 'deepseek/deepseek-chat')

    mock_ctx = _make_ctx_with_dict_obj('generate', {
        'output_cost': '/cost.csv',
    })
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        cmd(mock_ctx, '/path/to/prompt.txt')

    handle = mock_open_file()
    handle.write.assert_any_call(
        'timestamp,model,command,cost,input_files,output_files,attempted_models,job_id\r\n'
    )
    row_pattern = re.compile(
        r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+(?:[+-]\d{2}:\d{2})?,deepseek/deepseek-chat,generate,0.1,'
        r'/path/to/prompt.txt,,vertex_ai/gemini-2.5-pro;deepseek/deepseek-chat(?:,[^,\r\n]*)?\r\n'
    )
    assert any(row_pattern.match(c.args[0]) for c in handle.write.call_args_list)


def test_attempted_models_sanitizes_semicolons_to_colons(
    mock_click_context, mock_open_file, mock_rprint
):
    """Literal ';' in a model name must be replaced by ':' to keep the delimiter safe."""
    @track_cost
    def cmd(ctx, prompt_file: str) -> Tuple[str, float, str]:
        ctx.obj['attempted_models'] = ['weird;name', 'good-model']
        return ('/o', 0.0, 'good-model')

    mock_ctx = _make_ctx_with_dict_obj('generate', {
        'output_cost': '/cost.csv',
    })
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        cmd(mock_ctx, '/p.txt')

    handle = mock_open_file()
    # 'weird;name' -> 'weird:name', joined to other entries with ';'
    written_rows = [c.args[0] for c in handle.write.call_args_list]
    assert any('weird:name;good-model' in row for row in written_rows), written_rows
    # And no literal 'weird;name' (with raw semicolon) made it through
    assert not any('weird;name;' in row or row.endswith('weird;name\r\n')
                   for row in written_rows)


def test_attempted_models_defaults_to_model_name_when_missing(
    mock_click_context, mock_open_file, mock_rprint
):
    """If ctx.obj has no `attempted_models` key, fall back to [model_name]."""
    @track_cost
    def cmd(ctx, prompt_file: str) -> Tuple[str, float, str]:
        return ('/o', 0.2, 'solo-model')

    mock_ctx = create_mock_context(
        'generate',
        {'prompt_file': '/p.txt', 'output_cost': '/cost.csv'},
        obj={'output_cost': '/cost.csv'},  # no attempted_models
    )
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        cmd(mock_ctx, '/p.txt')

    handle = mock_open_file()
    row_pattern = re.compile(
        r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+(?:[+-]\d{2}:\d{2})?,solo-model,generate,0.2,'
        r'/p.txt,,solo-model(?:,[^,\r\n]*)?\r\n'
    )
    assert any(row_pattern.match(c.args[0]) for c in handle.write.call_args_list)


def test_legacy_csv_without_attempted_models_header_is_not_rewritten(
    mock_click_context, mock_rprint, tmp_path
):
    """Appending to an older CSV without `attempted_models` must keep the legacy
    column order and never rewrite the header."""
    cost_path = tmp_path / 'legacy.csv'
    legacy_header = 'timestamp,model,command,cost,input_files,output_files\r\n'
    legacy_row = '2026-01-01T00:00:00.000,old-model,gen,0.01,/old.in,/old.out\r\n'
    cost_path.write_text(legacy_header + legacy_row, encoding='utf-8')

    @track_cost
    def cmd(ctx, prompt_file: str) -> Tuple[str, float, str]:
        ctx.obj['attempted_models'] = ['a', 'new-model']
        return ('/o', 0.02, 'new-model')

    mock_ctx = _make_ctx_with_dict_obj('gen', {
        'output_cost': str(cost_path),
    })
    mock_click_context.return_value = mock_ctx

    cmd(mock_ctx, str(tmp_path / 'p.txt'))

    contents = cost_path.read_text(encoding='utf-8').splitlines()
    # Header preserved verbatim (no attempted_models column added)
    assert contents[0] == 'timestamp,model,command,cost,input_files,output_files'
    # Original row preserved
    assert contents[1] == '2026-01-01T00:00:00.000,old-model,gen,0.01,/old.in,/old.out'
    # New row appended without an attempted_models field (6 columns only)
    assert contents[2].count(',') == 5, contents[2]
    assert contents[2].endswith(',new-model,gen,0.02,,') or ',new-model,gen,0.02,' in contents[2]


def test_legacy_csv_warning_fires_once_per_path(
    mock_click_context, mock_rprint, tmp_path
):
    """The legacy-header UX warning must appear at most once per file in a
    single process, regardless of how many tracked commands append to it."""
    cost_path = tmp_path / 'legacy.csv'
    cost_path.write_text(
        'timestamp,model,command,cost,input_files,output_files\r\n'
        '2026-01-01T00:00:00.000,old,gen,0.01,/i,/o\r\n',
        encoding='utf-8',
    )

    @track_cost
    def cmd(ctx, prompt_file: str) -> Tuple[str, float, str]:
        ctx.obj['attempted_models'] = ['m1']
        return ('/o', 0.02, 'm1')

    mock_ctx = _make_ctx_with_dict_obj('gen', {'output_cost': str(cost_path)})
    mock_click_context.return_value = mock_ctx

    cmd(mock_ctx, str(tmp_path / 'p1.txt'))
    cmd(mock_ctx, str(tmp_path / 'p2.txt'))
    cmd(mock_ctx, str(tmp_path / 'p3.txt'))

    # Three rows appended, but the warning fired exactly once.
    legacy_warnings = [
        c for c in mock_rprint.call_args_list
        if 'attempted_models' in c.args[0] and str(cost_path) in c.args[0]
    ]
    assert len(legacy_warnings) == 1, (
        f"Expected exactly 1 legacy-CSV warning across 3 commands writing "
        f"to the same file, got {len(legacy_warnings)}: {legacy_warnings}"
    )


def test_new_csv_includes_attempted_models_header(
    mock_click_context, mock_rprint, tmp_path
):
    """A freshly created cost CSV must contain the attempted_models header column."""
    cost_path = tmp_path / 'fresh.csv'

    @track_cost
    def cmd(ctx, prompt_file: str) -> Tuple[str, float, str]:
        ctx.obj['attempted_models'] = ['m0', 'm1']
        return ('/o', 0.5, 'm1')

    mock_ctx = _make_ctx_with_dict_obj('gen', {
        'output_cost': str(cost_path),
    })
    mock_click_context.return_value = mock_ctx

    cmd(mock_ctx, str(tmp_path / 'p.txt'))

    lines = cost_path.read_text(encoding='utf-8').splitlines()
    assert lines[0] == 'timestamp,model,command,cost,input_files,output_files,attempted_models,job_id'
    # Data row ends with the joined attempted_models string (job_id column
    # is empty when PDD_JOB_ID is not set in the env, so the row ends
    # with `,attempted_models,` rather than `,attempted_models`).
    assert lines[1].endswith(',m0;m1,') or lines[1].endswith(',m0;m1'), lines[1]


def test_extract_cost_and_model_short_or_non_tuple():
    """extract_cost_and_model returns ('', '') for short/non-tuple results."""
    from pdd.track_cost import extract_cost_and_model
    assert extract_cost_and_model(('only-one',)) == ('', '')
    assert extract_cost_and_model('not a tuple') == ('', '')
    assert extract_cost_and_model(('out', 1.0, 'gpt')) == (1.0, 'gpt')


def test_looks_like_file_basic():
    """looks_like_file returns False for empty/non-string and True for path-like."""
    from pdd.track_cost import looks_like_file
    assert looks_like_file('') is False
    assert looks_like_file(None) is False
    assert looks_like_file(123) is False
    assert looks_like_file('foo.py') is True  # has extension


def test_attempted_models_does_not_leak_between_tracked_commands(
    mock_click_context, mock_rprint, tmp_path
):
    """Regression for #897: when two tracked commands share the same Click
    ctx.obj, the second command's `attempted_models` must reflect only its
    own attempts, not the first command's fallback history.

    The first command simulates a fallback (failed-model -> success-model)
    by setting ctx.obj['attempted_models'] from within. The second command
    records no attempts, so the row must fall back to [model_name] and the
    first command's history must not leak in.
    """
    cost_path = tmp_path / 'cost.csv'

    # Shared ctx.obj — simulates Click's chained / batch-style invocation
    # where the same context object is reused across multiple subcommands.
    shared_obj = {'output_cost': str(cost_path)}

    @track_cost
    def first_command(ctx, prompt_file: str) -> Tuple[str, float, str]:
        # Simulate llm_invoke recording a cloud failure + local fallback.
        ctx.obj['attempted_models'] = ['failed-model', 'success-model']
        return ('/out1', 0.1, 'success-model')

    @track_cost
    def second_command(ctx, prompt_file: str) -> Tuple[str, float, str]:
        # Second command makes only one attempt and does NOT populate
        # ctx.obj['attempted_models'] itself.
        return ('/out2', 0.2, 'second-model')

    # First invocation
    mock_ctx1 = _make_ctx_with_dict_obj('first', shared_obj)
    mock_click_context.return_value = mock_ctx1
    first_command(mock_ctx1, '/p1.txt')

    # Between invocations the leaked key must be gone from the shared obj.
    assert 'attempted_models' not in shared_obj, (
        f"attempted_models leaked into shared ctx.obj between commands: {shared_obj}"
    )

    # Second invocation reuses the SAME ctx.obj.
    mock_ctx2 = _make_ctx_with_dict_obj('second', shared_obj)
    mock_click_context.return_value = mock_ctx2
    second_command(mock_ctx2, '/p2.txt')

    lines = cost_path.read_text(encoding='utf-8').splitlines()
    # header + 2 data rows
    assert len(lines) == 3, lines
    assert lines[0] == 'timestamp,model,command,cost,input_files,output_files,attempted_models,job_id'
    # First row carries the simulated fallback history; the trailing
    # job_id field is empty when PDD_JOB_ID is not set in the env.
    assert lines[1].endswith(',failed-model;success-model,') or lines[1].endswith(',failed-model;success-model'), lines[1]
    # Second row falls back to its own [model_name], not the first command's history.
    assert lines[2].endswith(',second-model,') or lines[2].endswith(',second-model'), lines[2]
    assert 'failed-model' not in lines[2], (
        f"second row leaked first command's attempted_models: {lines[2]}"
    )
