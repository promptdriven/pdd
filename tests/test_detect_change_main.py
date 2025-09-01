import pytest
import click
from click.testing import CliRunner
from unittest.mock import patch, MagicMock
from pdd.detect_change_main import detect_change_main
from pdd import DEFAULT_STRENGTH

@pytest.fixture
def mock_construct_paths():
    with patch('pdd.detect_change_main.construct_paths') as mock:
        yield mock

@pytest.fixture
def mock_detect_change():
    with patch('pdd.detect_change_main.detect_change') as mock:
        yield mock

@pytest.fixture
def mock_rprint():
    with patch('pdd.detect_change_main.rprint') as mock:
        yield mock

@pytest.fixture
def mock_csv_writer():
    with patch('pdd.detect_change_main.csv.DictWriter') as mock:
        yield mock

@pytest.fixture
def mock_open():
    with patch('pdd.detect_change_main.open') as mock:
        yield mock

@pytest.fixture
def mock_sys_exit():
    with patch('sys.exit') as mock:
        yield mock

def test_detect_change_main_success(mock_construct_paths, mock_detect_change, mock_rprint, mock_csv_writer, mock_open):
    """
    Test case for successful execution of detect_change_main.
    """
    # Setup mock data
    mock_ctx = MagicMock(spec=click.Context)
    mock_ctx.obj = {'strength': DEFAULT_STRENGTH, 'temperature': 0, 'force': False, 'quiet': False, 'time': None}
    mock_ctx.scope_depth = 0
    mock_ctx.params = {}
    mock_ctx.parent = None
    mock_ctx.command = MagicMock()
    mock_ctx.terminal_width = 80
    mock_ctx.max_content_width = 80
    mock_ctx.exit_code = 0

    prompt_files = ['prompt1.prompt', 'prompt2.prompt']
    change_file = 'change_description.prompt'
    output = 'output.csv'

    mock_construct_paths.return_value = (
        {},  # resolved_config
        {'change_file': 'change content', 'prompt_file_0': 'prompt1 content', 'prompt_file_1': 'prompt2 content'},
        {'output': 'output.csv'},
        None
    )

    mock_detect_change.return_value = (
        [{'prompt_name': 'prompt1.prompt', 'change_instructions': 'Update prompt'}],
        0.05,
        'gpt-4'
    )

    # Call the function
    result = detect_change_main(mock_ctx, prompt_files, change_file, output)

    # Assertions
    assert result == (
        [{'prompt_name': 'prompt1.prompt', 'change_instructions': 'Update prompt'}],
        0.05,
        'gpt-4'
    )

    mock_construct_paths.assert_called_once_with(
        input_file_paths={
            'change_file': 'change_description.prompt',
            'prompt_file_0': 'prompt1.prompt',
            'prompt_file_1': 'prompt2.prompt'
        },
        force=False,
        quiet=False,
        command='detect',
        command_options={'output': 'output.csv'}
    )

    mock_detect_change.assert_called_once_with(
        ['prompt1.prompt', 'prompt2.prompt'],
        'change content',
        DEFAULT_STRENGTH,
        0,
        None,
        verbose=True
    )

    mock_rprint.assert_any_call("[bold green]Change detection completed successfully.[/bold green]")
    mock_rprint.assert_any_call("[bold]Model used:[/bold] gpt-4")
    mock_rprint.assert_any_call("[bold]Total cost:[/bold] $0.050000")
    mock_rprint.assert_any_call("[bold]Results saved to:[/bold] output.csv")
    mock_rprint.assert_any_call("\n[bold]Changes needed:[/bold]")
    mock_rprint.assert_any_call("[bold]Prompt:[/bold] prompt1.prompt")
    mock_rprint.assert_any_call("[bold]Instructions:[/bold] Update prompt")

def test_detect_change_main_no_changes(mock_construct_paths, mock_detect_change, mock_rprint):
    """
    Test case for detect_change_main when no changes are detected.
    """
    # Setup mock data
    mock_ctx = MagicMock(spec=click.Context)
    mock_ctx.obj = {'strength': DEFAULT_STRENGTH, 'temperature': 0, 'force': False, 'quiet': False, 'time': None}
    mock_ctx.scope_depth = 0
    mock_ctx.params = {}
    mock_ctx.parent = None
    mock_ctx.command = MagicMock()
    mock_ctx.terminal_width = 80
    mock_ctx.max_content_width = 80
    mock_ctx.exit_code = 0

    prompt_files = ['prompt1.prompt']
    change_file = 'change_description.prompt'
    output = None

    mock_construct_paths.return_value = (
        {},  # resolved_config
        {'change_file': 'change content', 'prompt_file_0': 'prompt1 content'},
        {},
        None
    )

    mock_detect_change.return_value = ([], 0.0, 'gpt-4')

    # Call the function
    result = detect_change_main(mock_ctx, prompt_files, change_file, output)

    # Assertions
    assert result == ([], 0.0, 'gpt-4')
    mock_detect_change.assert_called_once_with(
        ['prompt1.prompt'],
        'change content',
        DEFAULT_STRENGTH,
        0,
        None,
        verbose=True
    )
    mock_rprint.assert_any_call("No changes needed for any of the analyzed prompts.")

def test_detect_change_main_error(mock_construct_paths, mock_rprint, mock_sys_exit):
    """
    Test case for detect_change_main when an error occurs.
    """
    # Setup mock data
    mock_ctx = MagicMock(spec=click.Context)
    mock_ctx.obj = {'strength': DEFAULT_STRENGTH, 'temperature': 0, 'force': False, 'quiet': False, 'time': None}
    mock_ctx.scope_depth = 0
    mock_ctx.params = {}
    mock_ctx.parent = None
    mock_ctx.command = MagicMock()
    mock_ctx.terminal_width = 80
    mock_ctx.max_content_width = 80
    mock_ctx.exit_code = 0

    prompt_files = ['prompt1.prompt']
    change_file = 'change_description.prompt'
    output = None

    mock_construct_paths.side_effect = Exception("File not found")

    # Call the function
    detect_change_main(mock_ctx, prompt_files, change_file, output)

    # Assertions
    mock_rprint.assert_called_with("[bold red]Error:[/bold red] File not found")
    mock_sys_exit.assert_called_with(1)

def test_detect_change_main_quiet_mode(mock_construct_paths, mock_detect_change, mock_rprint):
    """
    Test case for detect_change_main in quiet mode.
    """
    # Setup mock data
    mock_ctx = MagicMock(spec=click.Context)
    mock_ctx.obj = {'strength': DEFAULT_STRENGTH, 'temperature': 0, 'force': False, 'quiet': True, 'time': None}
    mock_ctx.scope_depth = 0
    mock_ctx.params = {}
    mock_ctx.parent = None
    mock_ctx.command = MagicMock()
    mock_ctx.terminal_width = 80
    mock_ctx.max_content_width = 80
    mock_ctx.exit_code = 0

    prompt_files = ['prompt1.prompt']
    change_file = 'change_description.prompt'
    output = None

    mock_construct_paths.return_value = (
        {},  # resolved_config
        {'change_file': 'change content', 'prompt_file_0': 'prompt1 content'},
        {},
        None
    )

    mock_detect_change.return_value = ([], 0.0, 'gpt-4')

    # Call the function
    detect_change_main(mock_ctx, prompt_files, change_file, output)

    # Assertions
    mock_detect_change.assert_called_once_with(
        ['prompt1.prompt'],
        'change content',
        DEFAULT_STRENGTH,
        0,
        None,
        verbose=False
    )
    mock_rprint.assert_not_called()

def test_detect_change_main_csv_output(mock_construct_paths, mock_detect_change, mock_csv_writer, mock_open):
    """
    Test case for detect_change_main when output is written to a CSV file.
    """
    # Setup mock data
    mock_ctx = MagicMock(spec=click.Context)
    mock_ctx.obj = {'strength': DEFAULT_STRENGTH, 'temperature': 0, 'force': False, 'quiet': False, 'time': None}
    mock_ctx.scope_depth = 0
    mock_ctx.params = {}
    mock_ctx.parent = None
    mock_ctx.command = MagicMock()
    mock_ctx.terminal_width = 80
    mock_ctx.max_content_width = 80
    mock_ctx.exit_code = 0

    prompt_files = ['prompt1.prompt']
    change_file = 'change_description.prompt'
    output = 'output.csv'

    mock_construct_paths.return_value = (
        {},  # resolved_config
        {'change_file': 'change content', 'prompt_file_0': 'prompt1 content'},
        {'output': 'output.csv'},
        None
    )

    mock_detect_change.return_value = (
        [{'prompt_name': 'prompt1.prompt', 'change_instructions': 'Update prompt'}],
        0.05,
        'gpt-4'
    )

    # Call the function
    detect_change_main(mock_ctx, prompt_files, change_file, output)

    # Assertions
    mock_detect_change.assert_called_once_with(
        ['prompt1.prompt'],
        'change content',
        DEFAULT_STRENGTH,
        0,
        None,
        verbose=True
    )
    mock_open.assert_called_once_with('output.csv', 'w', newline='')
    mock_csv_writer.return_value.writeheader.assert_called_once()
    mock_csv_writer.return_value.writerow.assert_called_once_with(
        {'prompt_name': 'prompt1.prompt', 'change_instructions': 'Update prompt'}
    )