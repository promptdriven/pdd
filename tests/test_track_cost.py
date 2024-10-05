# tests/test_track_cost.py

import pytest
import unittest.mock as mock
from unittest.mock import MagicMock, mock_open, patch
import os
from datetime import datetime
from typing import Tuple
import csv

# Import the decorator from the pdd.track_cost module
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


# Helper function to create a mocked Click context
def create_mock_context(command_name: str, params: dict):
    """
    Creates a mocked Click context with the specified command name and parameters.
    """
    mock_ctx = MagicMock()
    mock_ctx.command.name = command_name
    mock_ctx.params = params
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


def test_no_output_cost_path(mock_click_context, mock_open_file, mock_rprint):
    """
    Test that no CSV file is written when output_cost_path is not specified.
    """
    # Setup the mocked Click context without 'output_cost' and environment variable
    mock_ctx = create_mock_context('generate', {'prompt_file': '/path/to/prompt.txt'})
    mock_click_context.return_value = mock_ctx

    # Remove environment variable if set
    with mock.patch.dict(os.environ, {}, clear=True):
        result = sample_command('/path/to/prompt.txt')

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
    mock_ctx = create_mock_context('generate', {
        'prompt_file': '/path/to/prompt.txt',
        'output_cost': '/path/to/cost.csv',
        'output': '/path/to/output'
    })
    mock_click_context.return_value = mock_ctx

    # Mock os.path.isfile to return False (file does not exist)
    with mock.patch('os.path.isfile', return_value=False):
        result = sample_command('/path/to/prompt.txt', output='/path/to/output')

    # Ensure that open was called with the correct path and mode
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files\r\n')
    handle.write.assert_any_call(
        f"{mock.ANY},gpt-3,generate,25.5,/path/to/prompt.txt,/path/to/output\r\n"
    )

    # Ensure no error was printed
    mock_rprint.assert_not_called()
    # Ensure the command result is returned correctly
    assert result == ('/path/to/output', 25.5, 'gpt-3')


def test_output_cost_path_via_env(mock_click_context, mock_open_file, mock_rprint, monkeypatch):
    """
    Test that the CSV file is written correctly when output_cost_path is specified via environment variable.
    """
    # Setup the mocked Click context without 'output_cost' parameter
    mock_ctx = create_mock_context('generate', {
        'prompt_file': '/path/to/prompt.txt',
        'output': '/path/to/output'
    })
    mock_click_context.return_value = mock_ctx

    # Set the environment variable PDD_OUTPUT_COST_PATH
    monkeypatch.setenv('PDD_OUTPUT_COST_PATH', '/env/path/cost.csv')

    # Mock os.path.isfile to return False (file does not exist)
    with mock.patch('os.path.isfile', return_value=False):
        result = sample_command('/path/to/prompt.txt', output='/path/to/output')

    # Ensure that open was called with the path from environment variable
    mock_open_file.assert_called_once_with('/env/path/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files\r\n')
    handle.write.assert_any_call(
        f"{mock.ANY},gpt-3,generate,25.5,/path/to/prompt.txt,/path/to/output\r\n"
    )

    # Ensure no error was printed
    mock_rprint.assert_not_called()
    # Ensure the command result is returned correctly
    assert result == ('/path/to/output', 25.5, 'gpt-3')


def test_csv_header_written_if_file_not_exists(mock_click_context, mock_open_file, mock_rprint):
    """
    Test that the CSV header is written when the CSV file does not exist.
    """
    # Setup the mocked Click context with 'output_cost' parameter
    mock_ctx = create_mock_context('generate', {
        'prompt_file': '/path/to/prompt.txt',
        'output_cost': '/path/to/cost.csv',
        'output': '/path/to/output'
    })
    mock_click_context.return_value = mock_ctx

    # Mock os.path.isfile to return False (file does not exist)
    with mock.patch('os.path.isfile', return_value=False):
        result = sample_command('/path/to/prompt.txt', output='/path/to/output')

    # Ensure that open was called once
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written first
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files\r\n')
    # Data row should be written
    handle.write.assert_any_call(
        f"{mock.ANY},gpt-3,generate,25.5,/path/to/prompt.txt,/path/to/output\r\n"
    )

    # Ensure no error was printed
    mock_rprint.assert_not_called()


def test_csv_row_appended_if_file_exists(mock_click_context, mock_open_file, mock_rprint):
    """
    Test that a new row is appended to the CSV file when it already exists.
    """
    # Setup the mocked Click context with 'output_cost' parameter
    mock_ctx = create_mock_context('generate', {
        'prompt_file': '/path/to/prompt.txt',
        'output_cost': '/path/to/cost.csv',
        'output': '/path/to/output'
    })
    mock_click_context.return_value = mock_ctx

    # Mock os.path.isfile to return True (file exists)
    with mock.patch('os.path.isfile', return_value=True):
        result = sample_command('/path/to/prompt.txt', output='/path/to/output')

    # Ensure that open was called once
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should NOT be written
    handle.write.assert_not_any_call('timestamp,model,command,cost,input_files,output_files\r\n')
    # Only data row should be written
    handle.write.assert_any_call(
        f"{mock.ANY},gpt-3,generate,25.5,/path/to/prompt.txt,/path/to/output\r\n"
    )

    # Ensure no error was printed
    mock_rprint.assert_not_called()


def test_cost_and_model_extracted_correctly(mock_click_context, mock_open_file, mock_rprint):
    """
    Test that cost and model name are correctly extracted from the command result.
    """
    # Setup the mocked Click context with 'output_cost' parameter
    mock_ctx = create_mock_context('train', {
        'input_file': '/path/to/input.txt',
        'output_cost': '/path/to/cost.csv',
        'output': '/path/to/output'
    })
    mock_click_context.return_value = mock_ctx

    # Modify the sample_command to return different values
    @track_cost
    def train_command(ctx, input_file: str, output: str = None) -> Tuple[str, float, str]:
        return ('/path/to/output', 50.0, 'bert-base')

    with mock.patch('os.path.isfile', return_value=False):
        result = train_command('/path/to/input.txt', output='/path/to/output')

    # Ensure that open was called with the correct path
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files\r\n')
    # Data row should have correct cost and model
    handle.write.assert_any_call(
        f"{mock.ANY},bert-base,train,50.0,/path/to/input.txt,/path/to/output\r\n"
    )

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
    mock_ctx = create_mock_context('short', {
        'prompt_file': '/path/to/prompt.txt',
        'output_cost': '/path/to/cost.csv'
    })
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        result = short_result_command('/path/to/prompt.txt')

    # Ensure that open was called
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files\r\n')
    # Data row should have empty cost and model
    handle.write.assert_any_call(
        f"{mock.ANY},,short,,/path/to/prompt.txt,\r\n"
    )

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
    mock_ctx = create_mock_context('process', {
        'input_file': '/path/to/input.txt',
        'output_file': '/path/to/output.txt',
        'output_cost': '/path/to/cost.csv'
    })
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        result = process_command('/path/to/input.txt', output_file='/path/to/output.txt')

    # Ensure that open was called with the correct path
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files\r\n')
    # Data row should have correct input and output files
    handle.write.assert_any_call(
        f"{mock.ANY},custom-model,process,15.0,/path/to/input.txt,/path/to/output.txt\r\n"
    )

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
    mock_ctx = create_mock_context('batch', {
        'input_files': ['/path/to/input1.txt', '/path/to/input2.txt'],
        'output_files': ['/path/to/output1.txt', '/path/to/output2.txt'],
        'output_cost': '/path/to/cost.csv'
    })
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        result = batch_command(
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
    handle.write.assert_any_call(
        f"{mock.ANY},batch-model,batch,100.0,/path/to/input1.txt;/path/to/input2.txt,/path/to/output1.txt;/path/to/output2.txt\r\n"
    )

    # Ensure no error was printed
    mock_rprint.assert_not_called()
    # Ensure the command result is returned correctly
    assert result == (['/path/to/output1', '/path/to/output2'], 100.0, 'batch-model')


def test_exception_in_logging(mock_click_context, mock_open_file, mock_rprint):
    """
    Test that if an exception occurs during cost logging, an error is printed and the command result is still returned.
    """
    # Setup the mocked Click context with 'output_cost' parameter
    mock_ctx = create_mock_context('error_command', {
        'prompt_file': '/path/to/prompt.txt',
        'output_cost': '/path/to/cost.csv'
    })
    mock_click_context.return_value = mock_ctx

    # Configure the open mock to raise an exception when called
    mock_open_file.side_effect = IOError("Failed to open file")

    with mock.patch('os.path.isfile', return_value=True):
        result = sample_command('/path/to/prompt.txt')

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
    mock_ctx = create_mock_context('mixed', {
        'input_file': '/path/to/input.txt',
        'output_file': '/path/to/output.txt',
        'config': {'key': 'value'},
        'output_cost': '/path/to/cost.csv'
    })
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        result = mixed_command('/path/to/input.txt', output_file='/path/to/output.txt', config={'key': 'value'})

    # Ensure that open was called with the correct path
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Data row should include only string file paths
    handle.write.assert_any_call(
        f"{mock.ANY},mixed-model,mixed,30.0,/path/to/input.txt,/path/to/output.txt\r\n"
    )

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
        result = sample_command('/path/to/prompt.txt')

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
    mock_ctx = create_mock_context('non_tuple', {
        'prompt_file': '/path/to/prompt.txt',
        'output_cost': '/path/to/cost.csv'
    })
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        result = non_tuple_command('/path/to/prompt.txt')

    # Ensure that open was called
    mock_open_file.assert_called_once_with('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Data row should have empty cost and model
    handle.write.assert_any_call(
        f"{mock.ANY},,non_tuple,,/path/to/prompt.txt,\r\n"
    )

    # Ensure no error was printed
    mock_rprint.assert_not_called()
    # Ensure the command result is returned correctly
    assert result == '/path/to/output'
