import pytest
from unittest.mock import patch, MagicMock, mock_open
from typing import List, Dict, Tuple, Optional

from pdd.conflicts_main import conflicts_main
from pdd import DEFAULT_STRENGTH

@pytest.fixture
def mock_ctx():
    """Fixture to create a mock Click context with parameters."""
    ctx = MagicMock()
    ctx.obj = {
        'force': False,
        'quiet': False,
        'strength': DEFAULT_STRENGTH,
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
        {},  # resolved_config
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
        command_options={'output': 'path/to/output.csv'},
        context_override=None,
    )

    # Ensure conflicts_in_prompts was called correctly
    mock_conflicts_in_prompts.assert_called_once_with(
        'Content of prompt1',
        'Content of prompt2',
        DEFAULT_STRENGTH,
        0,
        0.25,
        False
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

@patch('csv.DictWriter')
@patch('pdd.conflicts_main.conflicts_in_prompts')
@patch('pdd.conflicts_main.construct_paths')
@patch('pdd.conflicts_main.rprint')
@patch('builtins.open', new_callable=mock_open)
def test_success_without_output(
    mock_file,
    mock_rprint,
    mock_construct_paths,
    mock_conflicts_in_prompts,
    mock_dict_writer,
    mock_ctx
):
    """Test conflicts_main with valid inputs and no output path."""
    # Setup mock for construct_paths
    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            'prompt1': 'Content of prompt1',
            'prompt2': 'Content of prompt2'
        },
        {
            'output': 'conflicts.csv'
        },
        'some_language'
    )
    
    # Setup mock for conflicts_in_prompts
    sample_conflicts = [
        {'prompt_name': 'prompt_1', 'change_instructions': 'Change A'}
    ]
    mock_conflicts_in_prompts.return_value = (sample_conflicts, 0.654321, 'model_abc')
    
    # Create a mock writer instance
    mock_writer_instance = MagicMock()
    mock_dict_writer.return_value = mock_writer_instance
    
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
        command_options={'output': None},
        context_override=None,
    )
    
    # Ensure conflicts_in_prompts was called correctly
    mock_conflicts_in_prompts.assert_called_once_with(
        'Content of prompt1',
        'Content of prompt2',
        DEFAULT_STRENGTH,
        0,
        0.25,
        False
    )
    
    # Ensure CSV file was opened correctly with the correct filename and mode
    mock_file.assert_called_once_with('conflicts.csv', 'w', newline='')
    
    # Ensure DictWriter was instantiated correctly
    mock_dict_writer.assert_called_once_with(mock_file.return_value, fieldnames=['prompt_name', 'change_instructions'])
    
    # Ensure writer.writeheader() was called once
    mock_writer_instance.writeheader.assert_called_once()
    
    # Ensure writer.writerow() was called for each conflict
    expected_calls = [
        (({'prompt_name': 'path/to/prompt1', 'change_instructions': 'Change A'},),)
    ]
    mock_writer_instance.writerow.assert_has_calls(expected_calls, any_order=False)
    
    # Ensure rprint was called for user feedback without output path
    mock_rprint.assert_any_call("[bold green]Conflict analysis completed successfully.[/bold green]")
    mock_rprint.assert_any_call("[bold]Model used:[/bold] model_abc")
    mock_rprint.assert_any_call("[bold]Total cost:[/bold] $0.654321")
    


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
        {},  # resolved_config
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


@patch('csv.DictWriter')
@patch('pdd.conflicts_main.conflicts_in_prompts')
@patch('pdd.conflicts_main.construct_paths')
@patch('pdd.conflicts_main.rprint')
@patch('builtins.open', new_callable=mock_open)
def test_quiet_mode(mock_file, mock_rprint, mock_construct_paths, mock_conflicts_in_prompts, mock_dict_writer, mock_ctx):
    """Test conflicts_main in quiet mode."""
    # Modify context to be quiet
    mock_ctx.obj['quiet'] = True
    
    # Setup construct_paths
    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            'prompt1': 'Content of prompt1',
            'prompt2': 'Content of prompt2'
        },
        {
            'output': 'output/output.csv'
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
    
    # Ensure conflicts_in_prompts was called correctly
    mock_conflicts_in_prompts.assert_called_once_with(
        'Content of prompt1',
        'Content of prompt2',
        DEFAULT_STRENGTH,
        0,
        0.25,
        False
    )
    
    # Ensure rprint was called only for conflict detection
    # Since conflicts are empty, it should indicate no conflicts detected
    mock_rprint.assert_any_call("[bold]Conflicts detected:[/bold]")
    mock_rprint.assert_any_call("No conflicts detected or changes suggested.")


@patch('csv.DictWriter')
@patch('pdd.conflicts_main.conflicts_in_prompts')
@patch('pdd.conflicts_main.construct_paths')
@patch('pdd.conflicts_main.rprint')
@patch('builtins.open', new_callable=mock_open)
def test_force_option(mock_file, mock_rprint, mock_construct_paths, mock_conflicts_in_prompts, mock_dict_writer, mock_ctx):
    """Test conflicts_main with the force option enabled."""
    # Modify context to have force=True
    mock_ctx.obj['force'] = True
    
    # Setup construct_paths
    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            'prompt1': 'Content of prompt1',
            'prompt2': 'Content of prompt2'
        },
        {
            'output': 'output/output.csv'
        },
        'some_language'
    )
    
    # Setup conflicts_in_prompts
    sample_conflicts = [
        {'prompt_name': 'prompt_1', 'change_instructions': 'Force Change A'}
    ]
    mock_conflicts_in_prompts.return_value = (sample_conflicts, 0.789012, 'model_force')
    
    # Create a mock writer instance
    mock_writer_instance = MagicMock()
    mock_dict_writer.return_value = mock_writer_instance
    
    # Call the function under test
    conflicts, total_cost, model_name = conflicts_main(
        ctx=mock_ctx,
        prompt1='path/to/prompt1',
        prompt2='path/to/prompt2',
        output='output/output.csv'
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
        command_options={'output': 'output/output.csv'},
        context_override=None,
    )
    
    # Ensure conflicts_in_prompts was called correctly
    mock_conflicts_in_prompts.assert_called_once_with(
        'Content of prompt1',
        'Content of prompt2',
        DEFAULT_STRENGTH,
        0,
        0.25,
        False
    )
    
    # Ensure CSV file was opened correctly
    mock_file.assert_called_once_with('output/output.csv', 'w', newline='')
    
    # Ensure DictWriter was instantiated correctly
    mock_dict_writer.assert_called_once_with(mock_file.return_value, fieldnames=['prompt_name', 'change_instructions'])
    
    # Ensure writer methods were called correctly
    mock_writer_instance.writeheader.assert_called_once()
    mock_writer_instance.writerow.assert_called_once_with(
        {'prompt_name': 'path/to/prompt1', 'change_instructions': 'Force Change A'}
    )
    
    # Ensure rprint was called for user feedback
    mock_rprint.assert_any_call("[bold green]Conflict analysis completed successfully.[/bold green]")
    mock_rprint.assert_any_call("[bold]Model used:[/bold] model_force")
    mock_rprint.assert_any_call("[bold]Total cost:[/bold] $0.789012")
    mock_rprint.assert_any_call("[bold]Results saved to:[/bold] output/output.csv")


@patch('csv.DictWriter')
@patch('pdd.conflicts_main.conflicts_in_prompts')
@patch('pdd.conflicts_main.construct_paths')
@patch('pdd.conflicts_main.rprint')
@patch('builtins.open', new_callable=mock_open)
def test_replace_prompt_names(mock_file, mock_rprint, mock_construct_paths, mock_conflicts_in_prompts, mock_dict_writer, mock_ctx):
    """Test that prompt names are correctly replaced with actual file paths."""
    # Setup construct_paths
    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            'prompt1': 'Content of prompt1',
            'prompt2': 'Content of prompt2'
        },
        {
            'output': 'output/output.csv'
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
    
    # Ensure conflicts_in_prompts was called correctly
    mock_conflicts_in_prompts.assert_called_once_with(
        'Content of prompt1',
        'Content of prompt2',
        DEFAULT_STRENGTH,
        0,
        0.25,
        False
    )
    
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


@patch('pdd.conflicts_main.conflicts_in_prompts')
@patch('pdd.conflicts_main.construct_paths')
@patch('pdd.conflicts_main.rprint')
@patch('builtins.open', new_callable=mock_open)
@patch('csv.DictWriter')
def test_verbose_mode(mock_dict_writer, mock_file, mock_rprint, mock_construct_paths, mock_conflicts_in_prompts, mock_ctx):
    """Test conflicts_main with verbose mode enabled."""
    # Setup construct_paths
    mock_construct_paths.return_value = (
        {},  # resolved_config
        {
            'prompt1': 'Verbose prompt1 content',
            'prompt2': 'Verbose prompt2 content'
        },
        {
            'output': 'verbose_output.csv'
        },
        'python'
    )

    # Setup conflicts_in_prompts
    sample_conflicts = [{'prompt_name': 'prompt_1', 'change_instructions': 'Verbose Change'}]
    mock_conflicts_in_prompts.return_value = (sample_conflicts, 0.999, 'model_verbose')

    # Create a mock writer instance for csv.DictWriter
    mock_writer_instance = MagicMock()
    mock_dict_writer.return_value = mock_writer_instance

    # Call the function under test with verbose=True
    conflicts, total_cost, model_name = conflicts_main(
        ctx=mock_ctx,
        prompt1='path/to/verbose_prompt1',
        prompt2='path/to/verbose_prompt2',
        output=None,
        verbose=True
    )

    # Assertions
    assert conflicts == [
        {'prompt_name': 'path/to/verbose_prompt1', 'change_instructions': 'Verbose Change'}
    ]
    assert total_cost == 0.999
    assert model_name == 'model_verbose'

    # Ensure conflicts_in_prompts was called correctly with verbose=True
    mock_conflicts_in_prompts.assert_called_once_with(
        'Verbose prompt1 content',
        'Verbose prompt2 content',
        DEFAULT_STRENGTH,
        0,
        0.25,
        True
    )

    # Ensure construct_paths was called (optional, but good for completeness)
    mock_construct_paths.assert_called_once_with(
        input_file_paths={
            'prompt1': 'path/to/verbose_prompt1',
            'prompt2': 'path/to/verbose_prompt2'
        },
        force=False,
        quiet=False,
        command='conflicts',
        command_options={'output': None},
        context_override=None,
    )

    # Check that CSV writing happens (even if output is None, it defaults)
    mock_file.assert_called_once_with('verbose_output.csv', 'w', newline='')
    mock_dict_writer.assert_called_once_with(mock_file.return_value, fieldnames=['prompt_name', 'change_instructions'])
    mock_writer_instance.writeheader.assert_called_once()
    mock_writer_instance.writerow.assert_called_once_with({'prompt_name': 'path/to/verbose_prompt1', 'change_instructions': 'Verbose Change'})

    # Check rprint calls for verbose output (if any specific to verbose=True, otherwise general success messages)
    # If quiet is False (default in mock_ctx), success messages should be printed.
    # The spec for conflicts_main doesn't specify different rprint output for verbose=True itself,
    # rather that verbose is passed to conflicts_in_prompts for *its* detailed output.
    # So, we just check the standard non-quiet prints.
    if not mock_ctx.obj.get('quiet', False):
        mock_rprint.assert_any_call("[bold green]Conflict analysis completed successfully.[/bold green]")
        mock_rprint.assert_any_call("[bold]Model used:[/bold] model_verbose")
        mock_rprint.assert_any_call("[bold]Total cost:[/bold] $0.999000")
