# Test plan for pdd.track_cost (spec: prompts/track_cost_python.prompt)
# ---------------------------------------------------------------------
# Existing tests (kept as-is) cover:
#   * CSV row appended when file exists with content (no header rewrite)
#   * CSV header written when file does not exist
#   * CSV header written when file exists but is empty (regression)
#   * output_cost path resolved via ctx.obj vs PDD_OUTPUT_COST_PATH env
#   * cost and model name extracted from legacy result tuple
#   * Short / non-tuple results -> empty cost & model
#   * Input/output file collection (single, multiple, mixed types)
#   * Exception during CSV logging surfaces via rprint
#   * Missing Click context returns command result without logging
#   * Files still tracked for core dump when the wrapped command raises
#   * PYTEST_CURRENT_TEST env var skips CSV writing
#   * _parse_cost_from_csv roundtrip with an empty pre-created CSV
#
# New tests appended below cover the spec additions for the
# `attempted_models` column:
#   * Header column order matches the spec exactly
#   * Enriched result shape: dict last element supplies cost/model/attempted
#   * Enriched dict attempted_models serialized as ';'-joined chain
#   * command-scoped ctx.obj['attempted_models'] takes precedence over the result dict
#   * Empty string used in the CSV when no chain is recorded
#   * Empty command-scoped attempted_models falls back to the result dict's chain
import pytest
import unittest.mock as mock
from unittest.mock import MagicMock, mock_open, patch
import os
import re
from datetime import datetime
from typing import Tuple
from pdd.track_cost import track_cost, extract_cost_and_model
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


def test_csv_row_appended_if_file_exists_with_content(mock_click_context, mock_open_file, mock_rprint):
    """When CSV file exists AND has content, header should NOT be written (append mode)."""
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

    # The writer peeks only the header of the existing file (to detect a
    # missing 'attempted_models' column) before opening for append, so we
    # expect both calls.
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    handle = mock_open_file()
    assert not any('timestamp,model,command,cost,input_files,output_files' in call.args[0] for call in handle.write.call_args_list)
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,gpt-3,generate,25.5,/path/to/prompt.txt,/path/to/output,\r\n')
    assert any(row_pattern.match(call.args[0]) for call in handle.write.call_args_list)

    mock_rprint.assert_not_called()
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

    # Lock-file open (cost.csv.lock) now happens alongside the cost.csv
    # append; assert the cost.csv 'a' open occurred, not that it was the
    # ONLY open call.
    mock_open_file.assert_any_call('/tmp/cost_abc.csv', 'a', newline='', encoding='utf-8')

    handle = mock_open_file()
    # Header MUST be written when file is empty
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files,attempted_models\r\n')
    # Data row should follow (command name is 'sync' from mock context)
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,gpt-3,sync,25.5,/path/to/prompt.txt,/path/to/output,\r\n')
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
    # Lock-file open (cost.csv.lock) now happens alongside the cost.csv
    # append; assert the cost.csv 'a' open occurred, not that it was the
    # ONLY open call.
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files,attempted_models\r\n')
    
    # Use a regex pattern to match the row, ignoring the specific timestamp
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,gpt-3,generate,25.5,/path/to/prompt.txt,/path/to/output,\r\n')
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

    # Ensure that open was called with the path from environment variable.
    # Lock-file open (cost.csv.lock) now happens alongside; assert the
    # cost.csv 'a' open occurred, not that it was the ONLY open call.
    mock_open_file.assert_any_call('/env/path/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files,attempted_models\r\n')
    
    # Use a regex pattern to match the row, ignoring the specific timestamp
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,gpt-3,generate,25.5,/path/to/prompt.txt,/path/to/output,\r\n')
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
    # Lock-file open (cost.csv.lock) now happens alongside the cost.csv
    # append; assert the cost.csv 'a' open occurred, not that it was the
    # ONLY open call.
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written first
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files,attempted_models\r\n')
    # Data row should be written
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,gpt-3,generate,25.5,/path/to/prompt.txt,/path/to/output,\r\n')
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
    # Lock-file open (cost.csv.lock) now happens alongside the cost.csv
    # append; assert the cost.csv 'a' open occurred, not that it was the
    # ONLY open call.
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files,attempted_models\r\n')
    # Data row should have correct cost and model
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,bert-base,train,50.0,/path/to/input.txt,/path/to/output,\r\n')
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
    # Lock-file open (cost.csv.lock) now happens alongside the cost.csv
    # append; assert the cost.csv 'a' open occurred, not that it was the
    # ONLY open call.
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files,attempted_models\r\n')
    # Data row should have empty cost and model
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,,short,,/path/to/prompt.txt,,\r\n')
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
    # Lock-file open (cost.csv.lock) now happens alongside the cost.csv
    # append; assert the cost.csv 'a' open occurred, not that it was the
    # ONLY open call.
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files,attempted_models\r\n')
    # Data row should have correct input and output files
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,custom-model,process,15.0,/path/to/input.txt,/path/to/output.txt,\r\n')
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
    # Lock-file open (cost.csv.lock) now happens alongside the cost.csv
    # append; assert the cost.csv 'a' open occurred, not that it was the
    # ONLY open call.
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Header should be written
    handle.write.assert_any_call('timestamp,model,command,cost,input_files,output_files,attempted_models\r\n')
    # Data row should have multiple input and output files separated by semicolons
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,batch-model,batch,100.0,/path/to/input1.txt;/path/to/input2.txt,/path/to/output1.txt;/path/to/output2.txt,\r\n')
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

    # Ensure that open was attempted for append (a prior read-open may also
    # have been issued for the migration check; both raise IOError).
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

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
    # Lock-file open (cost.csv.lock) now happens alongside the cost.csv
    # append; assert the cost.csv 'a' open occurred, not that it was the
    # ONLY open call.
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Data row should include only string file paths
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,mixed-model,mixed,30.0,/path/to/input.txt,/path/to/output.txt,\r\n')
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
    # Lock-file open (cost.csv.lock) now happens alongside the cost.csv
    # append; assert the cost.csv 'a' open occurred, not that it was the
    # ONLY open call.
    mock_open_file.assert_any_call('/path/to/cost.csv', 'a', newline='', encoding='utf-8')

    # Retrieve the file handle to check written content
    handle = mock_open_file()
    # Data row should have empty cost and model
    row_pattern = re.compile(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,,non_tuple,,/path/to/prompt.txt,,\r\n')
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
# Tests for the spec additions: enriched result shape and attempted_models.
# ---------------------------------------------------------------------------


def test_header_column_order_matches_spec(mock_click_context, mock_open_file, mock_rprint):
    """The CSV header must be exactly:
    timestamp,model,command,cost,input_files,output_files,attempted_models
    """
    mock_ctx = create_mock_context(
        'generate',
        {'prompt_file': '/path/to/prompt.txt', 'output_cost': '/p/c.csv'},
        obj={'output_cost': '/p/c.csv'},
    )
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        sample_command(mock_ctx, '/path/to/prompt.txt')

    handle = mock_open_file()
    handle.write.assert_any_call(
        'timestamp,model,command,cost,input_files,output_files,attempted_models\r\n'
    )


def test_enriched_result_dict_supplies_cost_and_model(
    mock_click_context, mock_open_file, mock_rprint
):
    """When the last tuple element is a dict, read cost/model_name from it."""
    @track_cost
    def enriched_command(ctx, prompt_file: str):
        return ('/path/to/output', {
            'cost': 0.42,
            'model_name': 'claude-opus',
            'attempted_models': ['claude-opus'],
        })

    mock_ctx = create_mock_context(
        'enriched',
        {'prompt_file': '/path/to/prompt.txt', 'output_cost': '/p/c.csv'},
        obj={'output_cost': '/p/c.csv'},
    )
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        result = enriched_command(mock_ctx, '/path/to/prompt.txt')

    handle = mock_open_file()
    row_pattern = re.compile(
        r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+,'
        r'claude-opus,enriched,0\.42,/path/to/prompt\.txt,,claude-opus\r\n'
    )
    assert any(row_pattern.match(call.args[0]) for call in handle.write.call_args_list), \
        f"No matching row in: {[c.args[0] for c in handle.write.call_args_list]}"
    assert result[0] == '/path/to/output'


def test_enriched_attempted_models_serialized_chronologically(
    mock_click_context, mock_open_file, mock_rprint
):
    """attempted_models chain is serialized as ';'-joined in chronological order."""
    @track_cost
    def chain_command(ctx, prompt_file: str):
        return ('/path/to/output', {
            'cost': 0.1,
            'model_name': 'final-model',
            'attempted_models': ['first-try', 'second-try', 'final-model'],
        })

    mock_ctx = create_mock_context(
        'chain',
        {'prompt_file': '/path/to/prompt.txt', 'output_cost': '/p/c.csv'},
        obj={'output_cost': '/p/c.csv'},
    )
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        chain_command(mock_ctx, '/path/to/prompt.txt')

    handle = mock_open_file()
    writes = [c.args[0] for c in handle.write.call_args_list]
    assert any('first-try;second-try;final-model\r\n' in w for w in writes), \
        f"Chain not serialized chronologically. writes={writes}"


def test_command_scoped_attempted_models_takes_precedence(
    mock_click_context, mock_rprint, tmp_path
):
    """The chain populated during this command wins over the result dict."""
    from pdd.llm_invoke import _propagate_attempted_models_to_ctx

    csv_path = tmp_path / "cost.csv"
    shared_obj = {'output_cost': str(csv_path)}

    @track_cost
    def both_command(ctx, prompt_file: str):
        _propagate_attempted_models_to_ctx(['ctx-A', 'ctx-B'])
        return ('/path/to/output', {
            'cost': 0.5,
            'model_name': 'final',
            'attempted_models': ['from-result-only'],
        })

    mock_ctx = MagicMock()
    mock_ctx.command.name = 'both'
    mock_ctx.params = {'prompt_file': '/path/to/prompt.txt'}
    mock_ctx.obj = shared_obj
    mock_click_context.return_value = mock_ctx

    both_command(mock_ctx, '/path/to/prompt.txt')

    import csv as _csv
    with open(csv_path, newline='', encoding='utf-8') as fp:
        rows = list(_csv.DictReader(fp))
    assert rows[-1]['attempted_models'] == 'ctx-A;ctx-B'
    assert rows[-1]['attempted_models'] != 'from-result-only'
    assert 'attempted_models' not in shared_obj


def test_attempted_models_empty_when_no_chain(
    mock_click_context, mock_open_file, mock_rprint
):
    """Empty string used in the CSV when neither ctx.obj nor result supplies a chain."""
    @track_cost
    def no_chain_command(ctx, prompt_file: str):
        # Legacy shape, no attempted_models anywhere.
        return ('/path/to/output', 0.05, 'gpt-4')

    mock_ctx = create_mock_context(
        'no_chain',
        {'prompt_file': '/path/to/prompt.txt', 'output_cost': '/p/c.csv'},
        obj={'output_cost': '/p/c.csv'},
    )
    mock_click_context.return_value = mock_ctx

    with mock.patch('os.path.isfile', return_value=False):
        no_chain_command(mock_ctx, '/path/to/prompt.txt')

    handle = mock_open_file()
    writes = [c.args[0] for c in handle.write.call_args_list]
    # Expect the row to END with `,\r\n` for the empty attempted_models cell.
    data_rows = [w for w in writes if 'no_chain' in w]
    assert data_rows, f"No data row found. writes={writes}"
    assert data_rows[0].endswith(',\r\n'), \
        f"Row should end with empty attempted_models, got: {data_rows[0]!r}"


def test_empty_command_attempted_models_falls_back_to_result_dict(
    mock_click_context, mock_rprint, tmp_path
):
    """Precedence: the command-scoped chain must be non-empty to win."""
    csv_path = tmp_path / "cost.csv"
    shared_obj = {'output_cost': str(csv_path), 'attempted_models': []}

    @track_cost
    def fallback_command(ctx, prompt_file: str):
        return ('/path/to/output', {
            'cost': 0.2,
            'model_name': 'm',
            'attempted_models': ['from-result'],
        })

    mock_ctx = MagicMock()
    mock_ctx.command.name = 'fallback'
    mock_ctx.params = {'prompt_file': '/path/to/prompt.txt'}
    mock_ctx.obj = shared_obj
    mock_click_context.return_value = mock_ctx

    fallback_command(mock_ctx, '/path/to/prompt.txt')

    import csv as _csv
    with open(csv_path, newline='', encoding='utf-8') as fp:
        rows = list(_csv.DictReader(fp))
    assert rows[-1]['attempted_models'] == 'from-result'
    assert shared_obj['attempted_models'] == []


def test_extract_cost_and_model_enriched_shape():
    """extract_cost_and_model reads cost/model/attempted from a dict last element."""
    result = ('out', {
        'cost': 0.33,
        'model_name': 'modelX',
        'attempted_models': ['a', 'b'],
    })
    cost, model, attempted = extract_cost_and_model(result)
    assert cost == 0.33
    assert model == 'modelX'
    assert attempted == ['a', 'b']


def test_extract_cost_and_model_legacy_shape():
    """Legacy: (..., cost, model_name) returns no attempted_models chain."""
    result = ('out', 0.07, 'gpt-4')
    cost, model, attempted = extract_cost_and_model(result)
    assert cost == 0.07
    assert model == 'gpt-4'
    assert attempted == []


def test_extract_cost_and_model_non_tuple_returns_empty():
    """Non-tuple result returns the empty-string sentinel for cost & model."""
    cost, model, attempted = extract_cost_and_model('just a string')
    assert cost == ''
    assert model == ''
    assert attempted == []


def test_existing_csv_without_attempted_models_is_migrated(
    mock_click_context, mock_rprint, tmp_path
):
    """An existing 6-column cost.csv should be migrated to include the new
    'attempted_models' header so subsequent rows are addressable by name via
    csv.DictReader instead of leaking into ``None``.
    """
    csv_path = tmp_path / "cost.csv"
    # Pre-existing CSV with the old six-column schema.
    csv_path.write_text(
        "timestamp,model,command,cost,input_files,output_files\n"
        "2026-01-01T00:00:00.000,gpt-4,generate,1.0,a.txt,b.txt\n",
        encoding="utf-8",
    )

    from pdd.llm_invoke import _propagate_attempted_models_to_ctx

    shared_obj = {'output_cost': str(csv_path)}
    mock_ctx = MagicMock()
    mock_ctx.command.name = 'generate'
    mock_ctx.params = {
        'prompt_file': '/path/to/prompt.txt',
        'output_cost': str(csv_path),
        'output': '/path/to/output',
    }
    mock_ctx.obj = shared_obj
    mock_click_context.return_value = mock_ctx

    @track_cost
    def migrating_command(ctx, prompt_file: str, output: str):
        _propagate_attempted_models_to_ctx(['vertex_ai/gemini', 'deepseek/chat'])
        return (output, 25.5, 'deepseek/chat')

    migrating_command(mock_ctx, '/path/to/prompt.txt', output='/path/to/output')

    content = csv_path.read_text(encoding='utf-8')
    lines = content.strip().splitlines()
    header = lines[0].split(',')
    assert header[:6] == [
        'timestamp', 'model', 'command', 'cost', 'input_files', 'output_files'
    ]
    assert header[-1] == 'attempted_models'

    # csv.DictReader should now expose the new column under its proper name
    # (instead of dumping the extra value into ``None``).
    import csv as _csv
    with open(csv_path, newline='', encoding='utf-8') as fp:
        rows = list(_csv.DictReader(fp))
    assert rows[-1]['attempted_models'] == 'vertex_ai/gemini;deepseek/chat'
    assert None not in rows[-1]

    mock_rprint.assert_not_called()


def test_track_cost_captures_chain_when_ctx_obj_created_in_command(
    mock_click_context, mock_rprint, tmp_path
):
    """Regression (codex round 4, P2): when a @track_cost command starts
    with ctx.obj is None and the wrapped func promotes it inside the call
    (e.g. via ctx.ensure_object(dict)), the attempted_models chain that
    llm_invoke populates on the newly-created ctx.obj must still land in
    the CSV row. Previously the post-command capture was gated on
    attempted_models_scoped, which is False when ctx.obj is None at entry,
    so the captured chain stayed empty and the row's attempted_models
    column was blank even though a chain had been recorded.
    """
    csv_path = tmp_path / "cost.csv"

    mock_ctx = MagicMock()
    mock_ctx.command.name = 'generate'
    mock_ctx.params = {
        'prompt_file': '/path/to/prompt.txt',
        'output_cost': str(csv_path),
        'output': '/path/to/output',
    }
    # Entry state: ctx.obj is None. The snapshot/restore guard in
    # @track_cost will NOT fire because hasattr(None, '__setitem__') is
    # False. Capture must still happen post-command.
    mock_ctx.obj = None
    mock_click_context.return_value = mock_ctx

    @track_cost
    def cmd(ctx, prompt_file, output):
        # Simulate the command (or its callees, e.g. llm_invoke) promoting
        # ctx.obj inside the call.
        mock_ctx.obj = {
            'output_cost': str(csv_path),
            'attempted_models': ['m1'],
        }
        return (output, 1.0, 'm1')

    cmd(mock_ctx, '/path/to/prompt.txt', output='/path/to/output')

    import csv as _csv
    with open(csv_path, newline='', encoding='utf-8') as fp:
        rows = list(_csv.DictReader(fp))
    assert rows, "Expected at least one row in cost CSV"
    assert rows[-1]['attempted_models'] == 'm1', (
        f"Expected captured chain 'm1', got {rows[-1]['attempted_models']!r}"
    )

    mock_rprint.assert_not_called()


def test_attempted_models_scoped_to_single_command_invocation(
    mock_click_context, mock_rprint, tmp_path
):
    """Regression for issue #1086: when two @track_cost commands share a
    ctx.obj (chained / batched CLI run), the second command's CSV row must
    contain ONLY its own attempted models — not those accumulated during a
    prior command's execution. Previously _propagate_attempted_models_to_ctx
    appended to a shared ctx.obj entry that track_cost never reset, so the
    second row leaked the first command's fallback chain.
    """
    from pdd.llm_invoke import _propagate_attempted_models_to_ctx

    csv_path = tmp_path / "cost.csv"
    shared_obj = {'output_cost': str(csv_path)}

    @track_cost
    def cmd_one(ctx, prompt_file: str):
        _propagate_attempted_models_to_ctx(['m1'])
        return ('/path/to/out1', 0.1, 'm1')

    @track_cost
    def cmd_two(ctx, prompt_file: str):
        _propagate_attempted_models_to_ctx(['m2'])
        return ('/path/to/out2', 0.2, 'm2')

    # Use a SHARED real dict for ctx.obj across both commands so the
    # production aliasing pattern is faithfully reproduced.
    mock_ctx_one = MagicMock()
    mock_ctx_one.command.name = 'cmd_one'
    mock_ctx_one.params = {'prompt_file': '/p.txt'}
    mock_ctx_one.obj = shared_obj

    mock_ctx_two = MagicMock()
    mock_ctx_two.command.name = 'cmd_two'
    mock_ctx_two.params = {'prompt_file': '/p.txt'}
    mock_ctx_two.obj = shared_obj

    mock_click_context.return_value = mock_ctx_one
    cmd_one(mock_ctx_one, '/p.txt')

    mock_click_context.return_value = mock_ctx_two
    cmd_two(mock_ctx_two, '/p.txt')

    import csv as _csv
    with open(csv_path, newline='', encoding='utf-8') as fp:
        rows = list(_csv.DictReader(fp))
    rows_by_command = {row['command']: row for row in rows}
    assert 'cmd_one' in rows_by_command, f"missing cmd_one row: {rows}"
    assert 'cmd_two' in rows_by_command, f"missing cmd_two row: {rows}"

    assert rows_by_command['cmd_one']['attempted_models'] == 'm1'
    # The critical assertion: cmd_two must NOT inherit m1 from the prior
    # command's scope. It must contain only its own attempt.
    assert rows_by_command['cmd_two']['attempted_models'] == 'm2', (
        f"cmd_two leaked attempted_models from cmd_one: "
        f"{rows_by_command['cmd_two']['attempted_models']!r}"
    )
    # And the shared ctx.obj should have been restored to a clean state
    # (no 'attempted_models' key persists after the last @track_cost wrapper
    # exits, because there was no prior value to restore to).
    assert 'attempted_models' not in shared_obj


import sys


def test_migration_serialized_by_lock(
    mock_click_context, mock_rprint, tmp_path
):
    """Regression (codex round-7 finding 3, 3rd-pass review): concurrent
    @track_cost invocations against a legacy 6-column cost.csv must not
    lose rows to the migrate+append race. The portable atomic lock
    (O_CREAT|O_EXCL) serializes both the migration and the subsequent
    append on POSIX and Windows alike — no fcntl fallback.

    This is a structural smoke test using threads (which serialize via
    the GIL during the critical section) — full multi-process race
    coverage would require subprocess fixture machinery. The
    lock acquire/release code path is exercised end-to-end, proving
    the lock is opened/closed correctly and the migration completes
    under the lock.
    """
    import threading

    csv_path = tmp_path / "cost.csv"
    # Pre-existing 6-column CSV (legacy schema).
    csv_path.write_text(
        "timestamp,model,command,cost,input_files,output_files\n"
        "2026-01-01T00:00:00.000,gpt-4,sync,0.01,a.py,b.py\n",
        encoding="utf-8",
    )

    def _do_append(model_name):
        # Each thread gets its own mock ctx so command-name doesn't collide.
        ctx = MagicMock()
        ctx.command.name = 'generate'
        ctx.params = {
            'prompt_file': '/p.txt',
            'output_cost': str(csv_path),
            'output': '/o.txt',
        }
        ctx.obj = {'output_cost': str(csv_path)}

        @track_cost
        def cmd(ctx_arg, prompt_file, output):
            return (output, 0.5, model_name)

        # Each thread needs its own get_current_context patch — patch the
        # underlying module-level function so all threads see the same patch
        # but it returns the per-thread mock ctx via a thread-local sentinel.
        # Simpler: use a per-thread patch context manager.
        with patch('pdd.track_cost.click.get_current_context', return_value=ctx):
            cmd(ctx, '/p.txt', output='/o.txt')

    threads = [
        threading.Thread(target=_do_append, args=('m1',)),
        threading.Thread(target=_do_append, args=('m2',)),
    ]
    for t in threads:
        t.start()
    for t in threads:
        t.join()

    content = csv_path.read_text(encoding='utf-8')
    lines = [line for line in content.splitlines() if line.strip()]
    # Header (migrated, 7-column) + 1 original legacy row + 2 new rows.
    assert len(lines) == 4, (
        f"expected 4 lines (1 header + 1 legacy + 2 new), got "
        f"{len(lines)}: {lines!r}"
    )
    assert 'attempted_models' in lines[0], (
        f"header must be migrated to 7-column, got: {lines[0]!r}"
    )
    # Both new rows must be present (no lost-update).
    joined = '\n'.join(lines)
    assert ',m1,' in joined and ',m2,' in joined, (
        f"both appended rows must survive the race; got:\n{joined}"
    )

    mock_rprint.assert_not_called()


def test_acquire_atomic_lock_steals_lock_with_dead_pid(tmp_path):
    """Regression (4th-pass review, finding 2): staleness is determined by
    PID liveness, not by mtime. A lock whose holder PID is no longer alive
    must be reclaimed immediately — the previous mtime-only logic would
    either steal too eagerly (deleting a legitimately slow holder's lock)
    or wait the full mtime threshold even for dead processes.
    """
    import os
    from pdd.track_cost import (
        _acquire_atomic_lock,
        _release_atomic_lock,
    )

    lock_path = str(tmp_path / "cost.csv.lock")

    # Plant a lock whose recorded PID is definitely dead — pick a value
    # above MAX_PID on Linux/macOS so os.kill(pid, 0) raises immediately.
    dead_pid = 999_999_999
    with open(lock_path, 'w', encoding='utf-8') as f:
        f.write(f"{dead_pid}-stalefakenoncehex")

    handle, contended = _acquire_atomic_lock(lock_path)
    try:
        assert handle is not None, (
            "lock with dead PID must be reclaimed immediately; "
            "_acquire_atomic_lock returned None"
        )
        fd, nonce = handle
        # The nonce we wrote must NOT be the planted dead-PID nonce.
        assert "stalefakenoncehex" not in nonce, (
            "fresh nonce must replace the dead holder's identifier"
        )
    finally:
        _release_atomic_lock(handle, lock_path)

    assert not os.path.exists(lock_path), (
        "after release, the lock file must be unlinked"
    )


def test_acquire_atomic_lock_does_not_steal_live_pid(tmp_path):
    """Regression (4th-pass review, finding 2): a lock held by a LIVE
    PID must NOT be stolen even after the mtime ``_LOCK_STALE_SECONDS``
    threshold. The previous design treated any lock older than 60s as
    stale, which would clobber a legitimate slow migration.
    """
    import os
    import time
    from pdd.track_cost import _acquire_atomic_lock, _LOCK_STALE_SECONDS

    lock_path = str(tmp_path / "cost.csv.lock")

    # Plant a lock whose recorded PID IS us — definitely alive — and
    # backdate the mtime well past the safety-net threshold.
    with open(lock_path, 'w', encoding='utf-8') as f:
        f.write(f"{os.getpid()}-livepidnoncehex")
    very_old = time.time() - (_LOCK_STALE_SECONDS * 5)
    os.utime(lock_path, (very_old, very_old))

    # The acquire MUST exhaust retries (because the holder is alive) and
    # report contention. We use a short manual retry by patching the
    # constant via monkeypatching the module — but simplest: just call
    # and check it returned None + contended=True quickly. The 30s
    # default budget would make this slow, so monkey-patch the retry
    # cap down to keep CI fast.
    import pdd.track_cost as _tc
    saved_max = _tc._LOCK_RETRY_MAX
    _tc._LOCK_RETRY_MAX = 5  # 0.5s total — fast for a "must not steal" assert
    try:
        handle, contended = _acquire_atomic_lock(lock_path)
    finally:
        _tc._LOCK_RETRY_MAX = saved_max

    try:
        assert handle is None, (
            "lock held by a LIVE PID must NOT be stolen regardless of "
            "mtime; _acquire_atomic_lock returned a handle anyway"
        )
        assert contended is True, (
            "contention must be reported when the live holder kept us out"
        )
        assert os.path.exists(lock_path), (
            "the live holder's lock file must remain untouched"
        )
    finally:
        # Clean up our planted file so tmp_path teardown succeeds.
        try:
            os.unlink(lock_path)
        except OSError:
            pass


def test_release_atomic_lock_does_not_unlink_after_steal(tmp_path):
    """Regression (4th-pass review, finding 3): if our lock was stolen by
    another process while we held it, our release must NOT delete the
    new owner's lock file. The nonce check on release prevents this race.
    """
    import os
    from pdd.track_cost import _acquire_atomic_lock, _release_atomic_lock

    lock_path = str(tmp_path / "cost.csv.lock")

    # Acquire normally; capture the handle (fd, nonce).
    handle, _ = _acquire_atomic_lock(lock_path)
    assert handle is not None, "initial acquire must succeed"

    # Simulate a stale-steal: another owner overwrites the lock file with
    # their own nonce.
    other_owner_content = "12345-otheownernoncehex"
    with open(lock_path, 'w', encoding='utf-8') as f:
        f.write(other_owner_content)

    # Now release — we hold an fd to the OLD file, and the disk content
    # has a different nonce. The release MUST detect this mismatch and
    # leave the lock file alone.
    _release_atomic_lock(handle, lock_path)

    assert os.path.exists(lock_path), (
        "release after stale-steal must not unlink the new owner's lock"
    )
    with open(lock_path, 'r', encoding='utf-8') as f:
        remaining = f.read()
    assert remaining == other_owner_content, (
        "release after stale-steal must not modify the new owner's content; "
        f"got {remaining!r}"
    )

    # Cleanup for tmp_path teardown.
    os.unlink(lock_path)


def test_migration_skips_write_on_lock_failure(mock_click_context, mock_rprint, tmp_path):
    """Regression (5th-pass review, finding 1): when migration is needed
    but the lock can't be acquired (contended timeout or unsupported
    filesystem), the write MUST be skipped — not fall through unlocked
    while the original holder is still in the migration critical section.
    Falling through reopens the lost-row race.
    """
    import csv as _csv
    csv_path = tmp_path / "cost.csv"
    # Pre-existing 6-column legacy CSV — migration will trigger.
    csv_path.write_text(
        "timestamp,model,command,cost,input_files,output_files\n"
        "2026-01-01T00:00:00.000,gpt-4,sync,0.01,a.py,b.py\n",
        encoding="utf-8",
    )
    legacy_content = csv_path.read_text(encoding="utf-8")

    mock_ctx = create_mock_context(
        'sync',
        {'prompt_file': '/p.txt', 'output_cost': str(csv_path), 'output': '/o.txt'},
        obj={'output_cost': str(csv_path)}
    )
    mock_click_context.return_value = mock_ctx

    @track_cost
    def cmd(ctx_arg, prompt_file, output):
        return (output, 0.5, 'm1')

    # Force lock acquisition to fail by patching _acquire_atomic_lock.
    with patch('pdd.track_cost._acquire_atomic_lock', return_value=(None, True)):
        cmd(mock_ctx, '/p.txt', output='/o.txt')

    # The CSV must be byte-identical to the legacy content — NOT migrated,
    # NOT appended unlocked. The lost-row race only matters if we wrote;
    # by skipping, we leave the file safe for the real holder.
    after = csv_path.read_text(encoding="utf-8")
    assert after == legacy_content, (
        "migration with failed lock must skip the write entirely; got:\n" + after
    )
    # A loud warning must have fired so the user knows the row was lost.
    warn_calls = [c.args[0] for c in mock_rprint.call_args_list]
    assert any('could not acquire CSV lock for legacy migration' in w for w in warn_calls), (
        f"Expected migration-skip warning; got rprint calls: {warn_calls!r}"
    )


def test_acquire_atomic_lock_retries_on_partial_nonce_write(tmp_path, monkeypatch):
    """Regression (5th-pass review, finding 2): when nonce write fails or
    is partial, the acquire must close + unlink + retry rather than
    returning a malformed lock file that future processes wait 10 minutes
    on (the mtime stale threshold for unparseable nonces).
    """
    import os as _os
    from pdd import track_cost as _tc

    lock_path = str(tmp_path / "cost.csv.lock")

    # Patch os.write to fail the FIRST call only — second call (after
    # cleanup + retry) succeeds normally.
    real_write = _os.write
    call_count = {'n': 0}

    def flaky_write(fd, data):
        call_count['n'] += 1
        if call_count['n'] == 1:
            # Simulate partial write — returns fewer bytes than data.
            return 0
        return real_write(fd, data)

    monkeypatch.setattr(_tc.os, 'write', flaky_write)

    handle, contended = _tc._acquire_atomic_lock(lock_path)
    try:
        assert handle is not None, (
            "acquire must retry after partial-write failure; got None"
        )
        # After the first failed write, the file must have been cleaned
        # up (no malformed lock left behind). The second attempt succeeds
        # and the file now contains our valid nonce.
        with open(lock_path, 'r', encoding='utf-8') as f:
            content = f.read()
        assert '-' in content and content.startswith(str(os.getpid())), (
            f"after retry the lock file must contain our nonce; got {content!r}"
        )
    finally:
        _tc._release_atomic_lock(handle, lock_path)

    assert not os.path.exists(lock_path), (
        "after release, the lock file must be unlinked"
    )


def test_release_atomic_lock_unlinks_malformed_lock(tmp_path):
    """Regression (5th-pass review, finding 3): when the lock file
    exists but has no parseable nonce (e.g. truncated externally),
    release MUST still unlink the file. Leaving it behind would block
    every subsequent PDD invocation for the mtime stale window.
    """
    import os as _os
    from pdd import track_cost as _tc

    lock_path = str(tmp_path / "cost.csv.lock")

    # Acquire normally.
    handle, _ = _tc._acquire_atomic_lock(lock_path)
    assert handle is not None, "initial acquire must succeed"

    # Truncate the file content so _read_lock_owner returns None.
    with open(lock_path, 'w', encoding='utf-8') as f:
        f.write('')

    # Release with a malformed (empty) lock file. Previously the release
    # would silently return; now it unlinks because we hold the
    # O_EXCL-acquired fd.
    _tc._release_atomic_lock(handle, lock_path)

    assert not _os.path.exists(lock_path), (
        "release must unlink an unparseable lock that we created via "
        "O_EXCL; otherwise future PDD invocations are blocked for the "
        "mtime stale window."
    )


def test_peek_survives_malformed_csv_first_row(mock_click_context, mock_rprint, tmp_path):
    """Regression (6th-pass review, finding 1): a malformed cost.csv first
    row (csv.Error during the pre-lock peek) must NOT drop the cost row.
    Previously only OSError was caught, so csv.Error bubbled up to the
    outer except and the command silently lost its cost record.
    """
    csv_path = tmp_path / "cost.csv"
    # Malformed CSV: unterminated quoted field — csv.reader raises csv.Error.
    csv_path.write_bytes(b'timestamp,model,"command\n')

    mock_ctx = create_mock_context(
        'sync',
        {'prompt_file': '/p.txt', 'output_cost': str(csv_path), 'output': '/o.txt'},
        obj={'output_cost': str(csv_path)}
    )
    mock_click_context.return_value = mock_ctx

    @track_cost
    def cmd(ctx_arg, prompt_file, output):
        return (output, 0.5, 'm1')

    cmd(mock_ctx, '/p.txt', output='/o.txt')

    # The new cost row must be appended despite the malformed prefix.
    content = csv_path.read_bytes()
    assert b',m1,' in content, (
        "malformed CSV must not drop the cost row; final content:\n" + repr(content)
    )
    # No error rprint should fire (peek failure is non-fatal).
    error_calls = [c.args[0] for c in mock_rprint.call_args_list
                   if 'Error tracking cost' in c.args[0]]
    assert not error_calls, (
        f"peek failure must not surface as 'Error tracking cost'; got {error_calls!r}"
    )


def test_peek_survives_non_utf8_csv(mock_click_context, mock_rprint, tmp_path):
    """Regression (6th-pass review, finding 2): a cost.csv with invalid
    UTF-8 bytes must NOT drop the new cost row. Previously the peek's
    `encoding='utf-8'` open raised UnicodeDecodeError, which only OSError
    caught — so the row was lost via the outer exception handler.
    """
    csv_path = tmp_path / "cost.csv"
    # Header bytes followed by a non-UTF-8 sequence (lone 0x80 continuation).
    csv_path.write_bytes(
        b"timestamp,model,command,cost,input_files,output_files\n"
        b"2026-01-01,gpt-4,sync,0.01,a.py,\x80\x81bad.py\n"
    )

    mock_ctx = create_mock_context(
        'sync',
        {'prompt_file': '/p.txt', 'output_cost': str(csv_path), 'output': '/o.txt'},
        obj={'output_cost': str(csv_path)}
    )
    mock_click_context.return_value = mock_ctx

    @track_cost
    def cmd(ctx_arg, prompt_file, output):
        return (output, 0.5, 'm-utf8-fallback')

    cmd(mock_ctx, '/p.txt', output='/o.txt')

    content = csv_path.read_bytes()
    assert b'm-utf8-fallback' in content, (
        "non-UTF-8 CSV must not drop the cost row; final content:\n" + repr(content)
    )
    error_calls = [c.args[0] for c in mock_rprint.call_args_list
                   if 'Error tracking cost' in c.args[0]]
    assert not error_calls, (
        f"UnicodeDecodeError in peek must not surface as 'Error tracking cost'; got {error_calls!r}"
    )


def test_unsupported_fs_lock_attempts_unlocked_migration(mock_click_context, mock_rprint, tmp_path):
    """Regression (6th-pass review, finding 3): when migration is needed
    AND the filesystem doesn't support O_EXCL (unsupported lock, not
    contended), the previous behavior was to skip the cost row
    indefinitely until manual migration. The new policy attempts
    unlocked migration with a documented-tradeoff warning, so
    single-process use on such filesystems still works.
    """
    csv_path = tmp_path / "cost.csv"
    # Legacy 6-column CSV.
    csv_path.write_text(
        "timestamp,model,command,cost,input_files,output_files\n"
        "2026-01-01T00:00:00.000,gpt-4,sync,0.01,a.py,b.py\n",
        encoding="utf-8",
    )

    mock_ctx = create_mock_context(
        'sync',
        {'prompt_file': '/p.txt', 'output_cost': str(csv_path), 'output': '/o.txt'},
        obj={'output_cost': str(csv_path)}
    )
    mock_click_context.return_value = mock_ctx

    @track_cost
    def cmd(ctx_arg, prompt_file, output):
        return (output, 0.5, 'm-unsupported-fs')

    # Simulate unsupported filesystem: acquire returns (None, False).
    with patch('pdd.track_cost._acquire_atomic_lock', return_value=(None, False)):
        cmd(mock_ctx, '/p.txt', output='/o.txt')

    # CSV must be migrated AND the new row appended (single-process safe).
    content = csv_path.read_text(encoding="utf-8")
    assert 'attempted_models' in content.splitlines()[0], (
        "header must be migrated even on unsupported FS; got:\n" + content
    )
    assert 'm-unsupported-fs' in content, (
        "cost row must be appended on unsupported FS; got:\n" + content
    )
    warn_calls = [c.args[0] for c in mock_rprint.call_args_list]
    assert any('lock not supported on this filesystem' in w for w in warn_calls), (
        f"unsupported-FS tradeoff must be documented via warning; got rprint: {warn_calls!r}"
    )
