import pytest
from unittest.mock import patch, MagicMock, mock_open
from typing import List, Dict, Tuple
import csv

# Assume the project structure is as follows:
# project/
# ├── pdd/
# │   └── conflicts_main.py
# └── tests/
#     └── test_conflicts_main.py

# Absolute import of the function under test
from pdd.conflicts_main import conflicts_main


@pytest.fixture
def mock_ctx():
    """Fixture to create a mock Click context with parameters."""
    ctx = MagicMock()
    ctx.params = {
        'force': False,
        'quiet': False,
        'strength': 0.9,
        'temperature': 0
    }
    return ctx


@patch('csv.DictWriter')  # Added patch for csv.DictWriter
@patch('pdd.conflicts_main.conflicts_in_prompts')
@patch('pdd.conflicts_main.construct_paths')
@patch('pdd.conflicts_main.rprint')
@patch('builtins.open', new_callable=mock_open)
def test_success_with_output(mock_file, mock_rprint, mock_construct_paths, mock_conflicts_in_prompts, mock_dict_writer, mock_ctx):
    """Test conflicts_main with valid inputs and an output path."""
    # Setup mock for construct_paths
    mock_construct_paths.return_value = (
        {
            'prompt1': 'Content of prompt1',
            'prompt2': 'Content of prompt2'
        },
        {
            'output': 'output.csv'
        },
        'some_language'
    )

    # Setup mock for conflicts_in_prompts
    sample_conflicts = [
        {'prompt_name': 'prompt_1', 'change_instructions': 'Change A'},
        {'prompt_name': 'prompt_2', 'change_instructions': 'Change B'}
    ]
    mock_conflicts_in_prompts.return_value = (sample_conflicts, 0.123456, 'model_xyz')

    # Create a mock writer instance
    mock_writer_instance = MagicMock()
    mock_dict_writer.return_value = mock_writer_instance

    # Call the function under test
    conflicts, total_cost, model_name = conflicts_main(
        ctx=mock_ctx,
        prompt1='path/to/prompt1',
        prompt2='path/to/prompt2',
        output='path/to/output.csv'
    )

    # Assertions
    assert conflicts == [
        {'prompt_name': 'path/to/prompt1', 'change_instructions': 'Change A'},
        {'prompt_name': 'path/to/prompt2', 'change_instructions': 'Change B'}
    ]
    assert total_cost == 0.123456
    assert model_name == 'model_xyz'

    # Ensure construct_paths was called correctly
    mock_construct_paths.assert_called_once_with(
        input_file_paths={
            'prompt1': 'path/to/prompt1',
            'prompt2': 'path/to/prompt2'
        },
        force=False,
        quiet=False,
        command='conflicts',
        command_options={'output': 'path/to/output.csv'}
    )

    # Ensure conflicts_in_prompts was called correctly
    mock_conflicts_in_prompts.assert_called_once_with(
        'Content of prompt1',
        'Content of prompt2',
        0.9,
        0
    )

    # Ensure CSV file was opened correctly
    mock_file.assert_called_once_with('output.csv', 'w', newline='')

    # Ensure DictWriter was instantiated correctly
    mock_dict_writer.assert_called_once_with(mock_file.return_value, fieldnames=['prompt_name', 'change_instructions'])

    # Ensure writer.writeheader() was called once
    mock_writer_instance.writeheader.assert_called_once()

    # Ensure writer.writerow() was called for each conflict
    expected_calls = [
        (({'prompt_name': 'path/to/prompt1', 'change_instructions': 'Change A'},),),
        (({'prompt_name': 'path/to/prompt2', 'change_instructions': 'Change B'},),)
    ]
    mock_writer_instance.writerow.assert_has_calls(expected_calls, any_order=False)

    # Ensure rprint was called for user feedback
    mock_rprint.assert_any_call("[bold green]Conflict analysis completed successfully.[/bold green]")
    mock_rprint.assert_any_call("[bold]Model used:[/bold] model_xyz")
    mock_rprint.assert_any_call("[bold]Total cost:[/bold] $0.123456")
    mock_rprint.assert_any_call("[bold]Results saved to:[/bold] output.csv")


@patch('pdd.conflicts_main.conflicts_in_prompts')
@patch('pdd.conflicts_main.construct_paths')
@patch('pdd.conflicts_main.rprint')
@patch('builtins.open', new_callable=mock_open)
def test_success_without_output(mock_file, mock_rprint, mock_construct_paths, mock_conflicts_in_prompts, mock_ctx):
    """Test conflicts_main with valid inputs and no output path."""
    # Setup mock for construct_paths
    mock_construct_paths.return_value = (
        {
            'prompt1': 'Content of prompt1',
            'prompt2': 'Content of prompt2'
        },
        {},
        'some_language'
    )
    
    # Setup mock for conflicts_in_prompts
    sample_conflicts = [
        {'prompt_name': 'prompt_1', 'change_instructions': 'Change A'}
    ]
    mock_conflicts_in_prompts.return_value = (sample_conflicts, 0.654321, 'model_abc')
    
    # Call the function under test
    conflicts, total_cost, model_name = conflicts_main(
        ctx=mock_ctx,
        prompt1='path/to/prompt1',
        prompt2='path/to/prompt2',
        output=None
    )
    
    # Assertions
    assert conflicts == [
        {'prompt_name': 'path/to/prompt1', 'change_instructions': 'Change A'}
    ]
    assert total_cost == 0.654321
    assert model_name == 'model_abc'
    
    # Ensure construct_paths was called correctly
    mock_construct_paths.assert_called_once_with(
        input_file_paths={
            'prompt1': 'path/to/prompt1',
            'prompt2': 'path/to/prompt2'
        },
        force=False,
        quiet=False,
        command='conflicts',
        command_options={'output': None}
    )
    
    # Ensure conflicts_in_prompts was called correctly
    mock_conflicts_in_prompts.assert_called_once_with(
        'Content of prompt1',
        'Content of prompt2',
        0.9,
        0
    )
    
    # Ensure a file was attempted to be opened and written to
    mock_file.assert_called_once_with('conflicts.json', 'w')
    mock_file().write.assert_called_once()
    
    # Ensure rprint was called for user feedback
    mock_rprint.assert_any_call("[bold green]Conflict analysis completed successfully.[/bold green]")
    mock_rprint.assert_any_call("[bold]Model used:[/bold] model_abc")
    mock_rprint.assert_any_call("[bold]Total cost:[/bold] $0.654321")
    mock_rprint.assert_any_call("[bold]Conflicts detected:[/bold]")
    mock_rprint.assert_any_call("[bold]Prompt:[/bold] path/to/prompt1")
    mock_rprint.assert_any_call("[bold]Instructions:[/bold] Change A")
    mock_rprint.assert_any_call("---")
    mock_rprint.assert_any_call("[bold]Results written to:[/bold] conflicts.json")


@patch('pdd.conflicts_main.construct_paths')
@patch('pdd.conflicts_main.rprint')
def test_missing_prompt_files(mock_rprint, mock_construct_paths, mock_ctx):
    """Test conflicts_main handling of missing prompt files."""
    # Setup construct_paths to raise FileNotFoundError
    mock_construct_paths.side_effect = FileNotFoundError("Prompt files not found.")
    
    # Call the function under test and expect it to exit
    with pytest.raises(SystemExit) as exc_info:
        conflicts_main(
            ctx=mock_ctx,
            prompt1='path/to/nonexistent_prompt1',
            prompt2='path/to/nonexistent_prompt2',
            output='path/to/output.csv'
        )
    
    # Assertions
    assert exc_info.value.code == 1
    mock_rprint.assert_any_call("[bold red]Error:[/bold red] Prompt files not found.")


@patch('pdd.conflicts_main.conflicts_in_prompts')
@patch('pdd.conflicts_main.construct_paths')
@patch('pdd.conflicts_main.rprint')
def test_conflicts_in_prompts_error(mock_rprint, mock_construct_paths, mock_conflicts_in_prompts, mock_ctx):
    """Test conflicts_main handling exceptions from conflicts_in_prompts."""
    # Setup construct_paths
    mock_construct_paths.return_value = (
        {
            'prompt1': 'Content of prompt1',
            'prompt2': 'Content of prompt2'
        },
        {
            'output': 'output.csv'
        },
        'some_language'
    )
    
    # Setup conflicts_in_prompts to raise an exception
    mock_conflicts_in_prompts.side_effect = Exception("Model error occurred.")
    
    # Call the function under test and expect it to exit
    with pytest.raises(SystemExit) as exc_info:
        conflicts_main(
            ctx=mock_ctx,
            prompt1='path/to/prompt1',
            prompt2='path/to/prompt2',
            output='path/to/output.csv'
        )
    
    # Assertions
    assert exc_info.value.code == 1
    mock_rprint.assert_any_call("[bold red]Error:[/bold red] Model error occurred.")


@patch('pdd.conflicts_main.conflicts_in_prompts')
@patch('pdd.conflicts_main.construct_paths')
@patch('pdd.conflicts_main.rprint')
def test_quiet_mode(mock_rprint, mock_construct_paths, mock_conflicts_in_prompts, mock_ctx):
    """Test conflicts_main in quiet mode."""
    # Modify context to be quiet
    mock_ctx.params['quiet'] = True
    
    # Setup construct_paths
    mock_construct_paths.return_value = (
        {
            'prompt1': 'Content of prompt1',
            'prompt2': 'Content of prompt2'
        },
        {
            'output': 'output.csv'
        },
        'some_language'
    )
    
    # Setup conflicts_in_prompts
    sample_conflicts = []
    mock_conflicts_in_prompts.return_value = (sample_conflicts, 0.0, 'model_quiet')
    
    # Call the function under test
    conflicts, total_cost, model_name = conflicts_main(
        ctx=mock_ctx,
        prompt1='path/to/prompt1',
        prompt2='path/to/prompt2',
        output=None
    )
    
    # Assertions
    assert conflicts == []
    assert total_cost == 0.0
    assert model_name == 'model_quiet'
    
    # Ensure rprint was called only for conflict detection
    # Since conflicts are empty, it should indicate no conflicts detected
    mock_rprint.assert_any_call("[bold]Conflicts detected:[/bold]")
    mock_rprint.assert_any_call("No conflicts detected or changes suggested.")


@patch('pdd.conflicts_main.conflicts_in_prompts')
@patch('pdd.conflicts_main.construct_paths')
@patch('pdd.conflicts_main.rprint')
def test_force_option(mock_rprint, mock_construct_paths, mock_conflicts_in_prompts, mock_ctx):
    """Test conflicts_main with the force option enabled."""
    # Modify context to have force=True
    mock_ctx.params['force'] = True
    
    # Setup construct_paths
    mock_construct_paths.return_value = (
        {
            'prompt1': 'Content of prompt1',
            'prompt2': 'Content of prompt2'
        },
        {
            'output': 'output.csv'
        },
        'some_language'
    )
    
    # Setup conflicts_in_prompts
    sample_conflicts = [
        {'prompt_name': 'prompt_1', 'change_instructions': 'Force Change A'}
    ]
    mock_conflicts_in_prompts.return_value = (sample_conflicts, 0.789012, 'model_force')
    
    # Call the function under test
    conflicts, total_cost, model_name = conflicts_main(
        ctx=mock_ctx,
        prompt1='path/to/prompt1',
        prompt2='path/to/prompt2',
        output='path/to/output.csv'
    )
    
    # Assertions
    assert conflicts == [
        {'prompt_name': 'path/to/prompt1', 'change_instructions': 'Force Change A'}
    ]
    assert total_cost == 0.789012
    assert model_name == 'model_force'
    
    # Ensure construct_paths was called with force=True
    mock_construct_paths.assert_called_once_with(
        input_file_paths={
            'prompt1': 'path/to/prompt1',
            'prompt2': 'path/to/prompt2'
        },
        force=True,
        quiet=False,
        command='conflicts',
        command_options={'output': 'path/to/output.csv'}
    )
    
    # Ensure rprint was called for user feedback
    mock_rprint.assert_any_call("[bold green]Conflict analysis completed successfully.[/bold green]")
    mock_rprint.assert_any_call("[bold]Model used:[/bold] model_force")
    mock_rprint.assert_any_call("[bold]Total cost:[/bold] $0.789012")
    mock_rprint.assert_any_call("[bold]Results saved to:[/bold] output.csv")


@patch('pdd.conflicts_main.conflicts_in_prompts')
@patch('pdd.conflicts_main.construct_paths')
@patch('pdd.conflicts_main.rprint')
def test_replace_prompt_names(mock_rprint, mock_construct_paths, mock_conflicts_in_prompts, mock_ctx):
    """Test that prompt names are correctly replaced with actual file paths."""
    # Setup construct_paths
    mock_construct_paths.return_value = (
        {
            'prompt1': 'Content of prompt1',
            'prompt2': 'Content of prompt2'
        },
        {
            'output': 'output.csv'
        },
        'some_language'
    )
    
    # Setup conflicts_in_prompts with prompt_name as 'prompt_1' and 'prompt_2'
    sample_conflicts = [
        {'prompt_name': 'prompt_1', 'change_instructions': 'Change A'},
        {'prompt_name': 'prompt_2', 'change_instructions': 'Change B'}
    ]
    mock_conflicts_in_prompts.return_value = (sample_conflicts, 0.333333, 'model_replace')
    
    # Call the function under test
    conflicts, total_cost, model_name = conflicts_main(
        ctx=mock_ctx,
        prompt1='path/to/prompt1',
        prompt2='path/to/prompt2',
        output=None
    )
    
    # Assertions
    assert conflicts == [
        {'prompt_name': 'path/to/prompt1', 'change_instructions': 'Change A'},
        {'prompt_name': 'path/to/prompt2', 'change_instructions': 'Change B'}
    ]
    assert total_cost == 0.333333
    assert model_name == 'model_replace'
    
    # Ensure rprint was called correctly
    mock_rprint.assert_any_call("[bold green]Conflict analysis completed successfully.[/bold green]")
    mock_rprint.assert_any_call("[bold]Model used:[/bold] model_replace")
    mock_rprint.assert_any_call("[bold]Total cost:[/bold] $0.333333")
    mock_rprint.assert_any_call("[bold]Conflicts detected:[/bold]")
    mock_rprint.assert_any_call("[bold]Prompt:[/bold] path/to/prompt1")
    mock_rprint.assert_any_call("[bold]Instructions:[/bold] Change A")
    mock_rprint.assert_any_call("---")
    mock_rprint.assert_any_call("[bold]Prompt:[/bold] path/to/prompt2")
    mock_rprint.assert_any_call("[bold]Instructions:[/bold] Change B")
    mock_rprint.assert_any_call("---")