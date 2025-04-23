# tests/test_change_main.py

import pytest
import csv
import os
from pathlib import Path
from unittest.mock import MagicMock, patch, mock_open
from click import Context
from pdd.change_main import change_main

@pytest.fixture
def setup_environment(tmp_path):
    """
    Sets up the temporary environment for the test, including input files and directories.
    """
    # Create directories
    code_directory = tmp_path / "example_code_directory"
    code_directory.mkdir()
    
    output_directory = tmp_path / "example_output_directory"
    output_directory.mkdir()
    
    # Create sample code files
    script1_py = code_directory / "script1.py"
    script1_py.write_text("""
def add(a, b):
    return a + b
""")
    
    script2_py = code_directory / "script2.py"
    script2_py.write_text("""
def subtract(a, b):
    return a - b
""")
    
    # Create corresponding prompt files
    prompt1 = code_directory / "script1_python.prompt"
    prompt1.write_text("Write a function to calculate the factorial of a number.")
    
    prompt2 = code_directory / "script2_python.prompt"
    prompt2.write_text("Write a function to calculate the fibonacci sequence.")
    
    # Create batch_changes.csv
    batch_changes_csv = tmp_path / "batch_changes.csv"
    with open(batch_changes_csv, 'w', newline='') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=['prompt_name', 'change_instructions'])
        writer.writeheader()
        writer.writerow({'prompt_name': str(prompt1), 'change_instructions': "Modify the function to handle overflow errors."})
        writer.writerow({'prompt_name': str(prompt2), 'change_instructions': "Optimize the function for large numbers."})
    
    # Define the output file
    batch_output_file = tmp_path / "batch_modified_prompts.csv"
    
    return {
        "code_directory": str(code_directory),
        "batch_changes_csv": str(batch_changes_csv),
        "batch_output_file": str(batch_output_file)
    }

@patch('pdd.change_main.process_csv_change')
def test_change_main_batch_mode(mock_process_csv_change, setup_environment, caplog):
    """
    Tests the `change_main` function in CSV batch-change mode by comparing the generated
    output with the expected correct output.
    """
    caplog.set_level('DEBUG')
    env = setup_environment
    
    # Mock the Click context
    mock_ctx = MagicMock(spec=Context)
    mock_ctx.params = {
        "force": False,
        "quiet": True
    }
    mock_ctx.obj = {
        "strength": 0.9,
        "temperature": 0,
        "language": "python",
        "extension": ".py",
        "budget": 10.0
    }
    
    # Mock the process_csv_change function
    mock_process_csv_change.return_value = (True, [
        {'file_name': 'file1.py', 'modified_prompt': 'Modified content 1'},
        {'file_name': 'file2.py', 'modified_prompt': 'Modified content 2'}
    ], 0.5, 'gpt-3.5-turbo')
    
    # Verify CSV file content
    with open(env["batch_changes_csv"], 'r') as csvfile:
        reader = csv.DictReader(csvfile)
        assert 'prompt_name' in reader.fieldnames and 'change_instructions' in reader.fieldnames, "CSV file does not have the correct columns"
    
    # Run the change_main function in CSV mode
    message, total_cost, model_name = change_main(
        ctx=mock_ctx,
        change_prompt_file=env["batch_changes_csv"],
        input_code=env["code_directory"],
        input_prompt_file=None,  # Not used in CSV mode
        output=env["batch_output_file"],
        use_csv=True
    )
    
    # Assert the return values
    assert message == "Multiple prompts have been updated.", "The return message is incorrect."
    assert isinstance(total_cost, float), "Total cost should be a float."
    assert isinstance(model_name, str), "Model name should be a string."
    
    # Verify that process_csv_change was called with correct arguments
    mock_process_csv_change.assert_called_once_with(
        csv_file=env["batch_changes_csv"],
        strength=0.9,
        temperature=0,
        code_directory=env["code_directory"],
        language="python",
        extension=".py",
        budget=10.0
    )
    
    # Check if the output file was created
    assert os.path.exists(env["batch_output_file"]), "Output file was not created"
    
    # Read the generated output CSV
    with open(env["batch_output_file"], mode='r', newline='', encoding='utf-8') as csvfile:
        reader = csv.DictReader(csvfile)
        rows = list(reader)
        assert len(rows) == 2, "Output CSV should have 2 rows"
        assert 'file_name' in reader.fieldnames and 'modified_prompt' in reader.fieldnames, "Output CSV does not have the correct columns"
    
    # Check logs for debugging information
    assert "Starting change_main with use_csv=True" in caplog.text
    assert "CSV file validated" in caplog.text
    assert "process_csv_change completed. Success: True" in caplog.text
    assert "Results saved to CSV successfully" in caplog.text
    assert "Returning success message for CSV mode" in caplog.text

    print("All assertions passed successfully.")

# Helper function to create a mocked Click context
def create_mock_context(params: dict, obj: dict):
    mock_ctx = MagicMock()
    mock_ctx.params = params
    mock_ctx.obj = obj
    return mock_ctx

@pytest.fixture
def mock_construct_paths():
    with patch('pdd.change_main.construct_paths') as mock:
        yield mock

@pytest.fixture
def mock_change_func():
    with patch('pdd.change_main.change_func') as mock:
        yield mock

@pytest.fixture
def mock_process_csv_change():
    with patch('pdd.change_main.process_csv_change') as mock:
        yield mock

@pytest.fixture
def mock_rprint():
    with patch('pdd.change_main.rprint') as mock:
        yield mock

@pytest.fixture
def mock_os_path_isdir():
    with patch('pdd.change_main.os.path.isdir') as mock:
        yield mock

@pytest.fixture
def mock_csv_dictreader():
    with patch('pdd.change_main.csv.DictReader') as mock:
        yield mock

@pytest.fixture
def mock_open_function():
    with patch('pdd.change_main.open', mock_open=True) as mock:
        yield mock

# Test cases for non-CSV mode
@patch('builtins.open', new_callable=mock_open)
def test_change_main_non_csv_success(
    mock_file,
    mock_construct_paths,
    mock_change_func,
    mock_rprint,
):
    # Arrange
    ctx = create_mock_context(
        params={'force': False, 'quiet': False},
        obj={'strength': 0.8, 'temperature': 0.5, 'language': 'python', 'extension': '.py', 'budget': 10.0}
    )
    change_prompt_file = "path/to/change_prompt.txt"
    input_code = "path/to/input_code.py"
    input_prompt_file = "path/to/input_prompt.txt"
    output = "path/to/output_prompt.txt"
    use_csv = False

    # Mock construct_paths return value
    mock_construct_paths.return_value = (
        {
            "change_prompt_file": "Change Prompt Content",
            "input_code": "Input Code Content",
            "input_prompt_file": "Input Prompt Content"
        },
        {"output": output},
        "python"
    )

    # Mock change_func return value
    modified_prompt = "Modified Prompt Content"
    total_cost = 0.05
    model_name = "gpt-3.5-turbo"
    mock_change_func.return_value = (modified_prompt, total_cost, model_name)

    # Configure mock_file to handle write operations
    mock_file.return_value.write = MagicMock()

    # Act
    result = change_main(
        ctx=ctx,
        change_prompt_file=change_prompt_file,
        input_code=input_code,
        input_prompt_file=input_prompt_file,
        output=output,
        use_csv=use_csv
    )

    # Assert
    assert result == (modified_prompt, total_cost, model_name)
    mock_file.assert_called_with(output, 'w')
    mock_file.return_value.write.assert_called_with(modified_prompt)
    mock_rprint.assert_any_call("[bold green]Prompt modification completed successfully.[/bold green]")
    mock_rprint.assert_any_call(f"[bold]Model used:[/bold] {model_name}")
    mock_rprint.assert_any_call(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
    mock_rprint.assert_any_call(f"[bold]Modified prompt saved to:[/bold] {output}")

def test_change_main_non_csv_missing_input_prompt_file(mock_rprint):
    # Arrange
    ctx = create_mock_context(
        params={'force': False, 'quiet': False},
        obj={'strength': 0.8, 'temperature': 0.5}
    )
    change_prompt_file = "path/to/change_prompt.txt"
    input_code = "path/to/input_code.py"
    input_prompt_file = None
    output = "path/to/output_prompt.txt"
    use_csv = False

    # Act
    result = change_main(
        ctx=ctx,
        change_prompt_file=change_prompt_file,
        input_code=input_code,
        input_prompt_file=input_prompt_file,
        output=output,
        use_csv=use_csv
    )

    # Assert
    assert result == ("Error: 'input_prompt_file' is required when not using '--csv' mode.", 0.0, "")
    mock_rprint.assert_called_once_with("[bold red]Error: 'input_prompt_file' is required when not using '--csv' mode.[/bold red]")

def test_change_main_non_csv_construct_paths_error(
    mock_construct_paths,
    mock_rprint,
):
    # Arrange
    ctx = create_mock_context(
        params={'force': False, 'quiet': False},
        obj={'strength': 0.8, 'temperature': 0.5}
    )
    change_prompt_file = "path/to/change_prompt.txt"
    input_code = "path/to/input_code.py"
    input_prompt_file = "path/to/input_prompt.txt"
    output = "path/to/output_prompt.txt"
    use_csv = False

    # Mock construct_paths to raise an exception
    mock_construct_paths.side_effect = Exception("Construct Paths Failed")

    # Act
    result = change_main(
        ctx=ctx,
        change_prompt_file=change_prompt_file,
        input_code=input_code,
        input_prompt_file=input_prompt_file,
        output=output,
        use_csv=use_csv
    )

    # Assert
    assert result == ("An unexpected error occurred: Construct Paths Failed", 0.0, "")
    mock_rprint.assert_called_once_with("[bold red]Error: An unexpected error occurred: Construct Paths Failed[/bold red]")

def test_change_main_non_csv_change_func_error(
    mock_construct_paths,
    mock_change_func,
    mock_rprint,
):
    # Arrange
    ctx = create_mock_context(
        params={'force': False, 'quiet': False},
        obj={'strength': 0.8, 'temperature': 0.5}
    )
    change_prompt_file = "path/to/change_prompt.txt"
    input_code = "path/to/input_code.py"
    input_prompt_file = "path/to/input_prompt.txt"
    output = "path/to/output_prompt.txt"
    use_csv = False

    # Mock construct_paths return value
    mock_construct_paths.return_value = (
        {
            "change_prompt_file": "Change Prompt Content",
            "input_code": "Input Code Content",
            "input_prompt_file": "Input Prompt Content"
        },
        {"output": output},
        "python"
    )

    # Mock change_func to raise an exception
    mock_change_func.side_effect = Exception("Change Function Failed")

    # Act
    result = change_main(
        ctx=ctx,
        change_prompt_file=change_prompt_file,
        input_code=input_code,
        input_prompt_file=input_prompt_file,
        output=output,
        use_csv=use_csv
    )

    # Assert
    assert result == ("An unexpected error occurred: Change Function Failed", 0.0, "")
    mock_rprint.assert_called_once_with("[bold red]Error: An unexpected error occurred: Change Function Failed[/bold red]")

# Test cases for CSV mode
def test_change_main_csv_success(
    mock_construct_paths,
    mock_process_csv_change,
    mock_rprint,
    mock_os_path_isdir,
    mock_csv_dictreader,
    mock_open_function,
):
    # Arrange
    ctx = create_mock_context(
        params={},
        obj={'force': True, 'quiet': False, 'strength': 0.7, 'temperature': 0.3, 'language': 'python', 'extension': '.py', 'budget': 20.0}
    )
    change_prompt_file = "path/to/change_prompts.csv"
    input_code = "path/to/code_directory"
    input_prompt_file = None
    output = "path/to/output.csv"
    use_csv = True

    # Mock os.path.isdir to return True
    mock_os_path_isdir.return_value = True

    # Mock construct_paths return value
    mock_construct_paths.return_value = (
        {
            "change_prompt_file": "Change Prompt Content"
        },
        {"output": output},
        "python"
    )

    # Mock CSV file reading and validation
    mock_csv_dictreader.return_value.fieldnames = ['prompt_name', 'change_instructions']
    
    # Mock process_csv_change return value
    success = True
    modified_prompts = [
        {'file_name': 'file1.py', 'modified_prompt': 'Modified Prompt 1'},
        {'file_name': 'file2.py', 'modified_prompt': 'Modified Prompt 2'}
    ]
    total_cost = 0.10
    model_name = "gpt-4"
    mock_process_csv_change.return_value = (success, modified_prompts, total_cost, model_name)

    # Act
    result = change_main(
        ctx=ctx,
        change_prompt_file=change_prompt_file,
        input_code=input_code,
        input_prompt_file=input_prompt_file,
        output=output,
        use_csv=use_csv
    )

    # Assert
    assert result == ("Multiple prompts have been updated.", total_cost, model_name)
    mock_construct_paths.assert_called_once_with(
        input_file_paths={
            "change_prompt_file": change_prompt_file,
        },
        force=True,
        quiet=False,
        command="change",
        command_options={"output": output}
    )
    mock_os_path_isdir.assert_called_once_with(input_code)
    mock_csv_dictreader.assert_called_once()
    mock_process_csv_change.assert_called_once_with(
        csv_file=change_prompt_file,
        strength=0.7,
        temperature=0.3,
        code_directory=input_code,
        language='python',
        extension='.py',
        budget=20.0
    )
    mock_rprint.assert_any_call("[bold green]Batch change operation completed successfully.[/bold green]")
    mock_rprint.assert_any_call(f"[bold]Model used:[/bold] {model_name}")
    mock_rprint.assert_any_call(f"[bold]Total cost:[/bold] ${total_cost:.6f}")
    mock_rprint.assert_any_call(f"[bold]Results saved to CSV:[/bold] {output}")

def test_change_main_csv_input_code_not_directory(
    mock_construct_paths,
    mock_rprint,
    mock_os_path_isdir,
):
    # Arrange
    ctx = create_mock_context(
        params={'force': False, 'quiet': False},
        obj={'strength': 0.6, 'temperature': 0.4}
    )
    change_prompt_file = "path/to/change_prompts.csv"
    input_code = "path/to/input_file.py"  # Not a directory
    input_prompt_file = None
    output = "path/to/output.csv"
    use_csv = True

    # Mock os.path.isdir to return False
    mock_os_path_isdir.return_value = False

    # Act
    result = change_main(
        ctx=ctx,
        change_prompt_file=change_prompt_file,
        input_code=input_code,
        input_prompt_file=input_prompt_file,
        output=output,
        use_csv=use_csv
    )

    # Assert
    expected_error = f"In CSV mode, 'input_code' must be a directory. Got: {input_code}"
    assert result == (expected_error, 0.0, "")
    mock_rprint.assert_called_once_with("[bold red]Error: In CSV mode, 'input_code' must be a directory. Got: path/to/input_file.py[/bold red]")

def test_change_main_csv_missing_columns(
    mock_construct_paths,
    mock_csv_dictreader,
    mock_rprint,
    mock_os_path_isdir,
    mock_open_function,
):
    # Arrange
    ctx = create_mock_context(
        params={'force': False, 'quiet': False},
        obj={'strength': 0.6, 'temperature': 0.4}
    )
    change_prompt_file = "path/to/change_prompts.csv"
    input_code = "path/to/code_directory"
    input_prompt_file = None
    output = "path/to/output.csv"
    use_csv = True

    # Mock os.path.isdir to return True
    mock_os_path_isdir.return_value = True

    # Mock construct_paths return value
    mock_construct_paths.return_value = (
        {
            "change_prompt_file": "Change Prompt Content"
        },
        {"output": output},
        "python"
    )

    # Mock CSV file with missing columns
    mock_csv_dictreader.return_value.fieldnames = ['invalid_column1', 'invalid_column2']

    # Act
    result = change_main(
        ctx=ctx,
        change_prompt_file=change_prompt_file,
        input_code=input_code,
        input_prompt_file=input_prompt_file,
        output=output,
        use_csv=use_csv
    )

    # Assert
    expected_error = "CSV file must contain 'prompt_name' and 'change_instructions' columns."
    assert result == (expected_error, 0.0, "")
    mock_rprint.assert_called_once_with("[bold red]Error: CSV file must contain 'prompt_name' and 'change_instructions' columns.[/bold red]")

def test_change_main_csv_process_csv_change_error(
    mock_construct_paths,
    mock_process_csv_change,
    mock_rprint,
    mock_os_path_isdir,
    mock_csv_dictreader,
    mock_open_function,
):
    # Arrange
    ctx = create_mock_context(
        params={'force': True, 'quiet': False},
        obj={'strength': 0.7, 'temperature': 0.3}
    )
    change_prompt_file = "path/to/change_prompts.csv"
    input_code = "path/to/code_directory"
    input_prompt_file = None
    output = "path/to/output.csv"
    use_csv = True

    # Mock os.path.isdir to return True
    mock_os_path_isdir.return_value = True

    # Mock construct_paths return value
    mock_construct_paths.return_value = (
        {
            "change_prompt_file": "Change Prompt Content"
        },
        {"output": output},
        "python"
    )

    # Mock CSV file validation
    mock_csv_dictreader.return_value.fieldnames = ['prompt_name', 'change_instructions']

    # Mock process_csv_change to raise an exception
    mock_process_csv_change.side_effect = Exception("CSV Processing Failed")

    # Act
    result = change_main(
        ctx=ctx,
        change_prompt_file=change_prompt_file,
        input_code=input_code,
        input_prompt_file=input_prompt_file,
        output=output,
        use_csv=use_csv
    )

    # Assert
    expected_error = "Error during CSV processing: CSV Processing Failed"
    assert result == (expected_error, 0.0, "")
    mock_rprint.assert_called_once_with("[bold red]Error: Error during CSV processing: CSV Processing Failed[/bold red]")

# Test cases for error handling and logging
def test_change_main_unexpected_exception(
    mock_construct_paths,
    mock_change_func,
    mock_process_csv_change,
    mock_rprint,
):
    # Arrange
    ctx = create_mock_context(
        params={'force': False, 'quiet': False},
        obj={'strength': 0.8, 'temperature': 0.5}
    )
    change_prompt_file = "path/to/change_prompt.txt"
    input_code = "path/to/input_code.py"
    input_prompt_file = "path/to/input_prompt.txt"
    output = "path/to/output_prompt.txt"
    use_csv = False

    # Mock construct_paths to raise a generic exception
    mock_construct_paths.side_effect = ValueError("Invalid value")

    # Act
    result = change_main(
        ctx=ctx,
        change_prompt_file=change_prompt_file,
        input_code=input_code,
        input_prompt_file=input_prompt_file,
        output=output,
        use_csv=use_csv
    )

    # Assert
    expected_error = "An unexpected error occurred: Invalid value"
    assert result == (expected_error, 0.0, "")
    mock_rprint.assert_called_once_with("[bold red]Error: An unexpected error occurred: Invalid value[/bold red]")

# === Tests for CSV Mode Output Directory Handling ===

@patch('builtins.open', new_callable=MagicMock)
@patch('pdd.change_main.csv.DictReader')
def test_change_main_csv_output_directory_saves_individual_files(
    mock_dict_reader, # Mocked csv.DictReader
    mock_open_instance, # Patched builtins.open
    tmp_path, # pytest fixture for temporary directory
    mock_construct_paths,
    mock_process_csv_change
):
    """
    Verify change_main saves individual files to the specified directory
    when --output specifies a directory in CSV mode (CORRECT BEHAVIOR).
    """
    # Arrange
    # 1. Create the target output directory
    output_dir = tmp_path / "output_dir"
    output_dir.mkdir()
    output_dir_path_str = str(output_dir) # Path to the actual directory

    # 2. Setup context and other mocks
    mock_ctx = create_mock_context(
        params={'force': False},
        obj={'quiet': True, 'force': False}
    )
    # construct_paths mock: Still returns a default path, but it might
    # not be used directly if the output logic is fixed.
    mock_construct_paths.return_value = (
        {'change_prompt_file': 'csv content'},
        {'output': str(tmp_path / 'default_path.prompt')},
        'python'
    )
    # process_csv_change returns multiple modified prompts
    modified_prompts_data = [
        {'file_name': 'file1.prompt', 'modified_prompt': 'prompt1 content'},
        {'file_name': 'file2.prompt', 'modified_prompt': 'prompt2 content'}
    ]
    mock_process_csv_change.return_value = (
        True, # success
        modified_prompts_data,
        0.01, # cost
        'mock_model' # model_name
    )

    # Input CSV file path (doesn't need content due to DictReader mock)
    change_prompt_file = str(tmp_path / "dummy.csv")
    # Create the input code directory
    input_code_dir_path = tmp_path / "code_dir"
    input_code_dir_path.mkdir()
    input_code_dir_str = str(input_code_dir_path)

    # Mock csv.DictReader to pass validation
    mock_reader_instance = MagicMock()
    mock_reader_instance.fieldnames = ['prompt_name', 'change_instructions']
    mock_dict_reader.return_value = mock_reader_instance

    # Configure the open mock for writing individual files
    mock_file_handle = MagicMock()
    mock_open_instance.return_value.__enter__.return_value = mock_file_handle

    # Act
    # Call change_main, passing the directory path as the output
    result_tuple = change_main(
        ctx=mock_ctx,
        change_prompt_file=change_prompt_file,
        input_code=input_code_dir_str,
        input_prompt_file=None,
        output=output_dir_path_str, # <<< Critical: Pass the directory path
        use_csv=True
    )

    # Assert
    # 1. Expect the SUCCESS tuple now
    assert result_tuple == ("Multiple prompts have been updated.", 0.01, 'mock_model')

    # 2. Verify DictReader was called (validation passed)
    mock_dict_reader.assert_called_once()

    # 3. Verify process_csv_change was called
    mock_process_csv_change.assert_called_once()

    # 4. Verify 'open' was called correctly for the individual files IN THE SPECIFIED DIR
    expected_dir = output_dir_path_str # <<< Use the specified output directory
    expected_calls = [
        ((os.path.join(expected_dir, 'file1.prompt'), 'w'),),
        ((os.path.join(expected_dir, 'file2.prompt'), 'w'),)
    ]

    # Filter calls to mock_open to only get write calls
    write_calls = [call for call in mock_open_instance.call_args_list if len(call[0]) > 1 and call[0][1] == 'w']
    assert len(write_calls) == len(expected_calls)

    # Compare the arguments of the write calls
    write_call_args = [c[0] for c in write_calls]
    assert sorted(write_call_args) == sorted([c[0] for c in expected_calls])

    # 5. Verify the mock file handles were written to
    mock_file_handle.write.assert_any_call('prompt1 content')
    mock_file_handle.write.assert_any_call('prompt2 content')
    assert mock_file_handle.write.call_count == 2

@patch('builtins.open', new_callable=MagicMock)
@patch('pdd.change_main.csv.DictReader')
def test_change_main_csv_output_none_saves_individual_files(
    mock_dict_reader,
    mock_open_instance,
    tmp_path,
    mock_construct_paths,
    mock_process_csv_change
):
    """
    Verify change_main saves individual files when --output is None in CSV mode.
    """
    # Arrange
    mock_ctx = create_mock_context(
        params={'force': False},
        obj={'quiet': True, 'force': False}
    )
    default_output_path = tmp_path / "default_output.prompt"
    mock_construct_paths.return_value = (
        {'change_prompt_file': 'csv content'},
        {'output': str(default_output_path)},
        'python'
    )
    modified_prompts_data = [
        {'file_name': 'file1_python.prompt', 'modified_prompt': 'prompt1 content'},
        {'file_name': 'file2_python.prompt', 'modified_prompt': 'prompt2 content'}
    ]
    mock_process_csv_change.return_value = (True, modified_prompts_data, 0.02, 'mock_model')

    change_prompt_file = str(tmp_path / "dummy.csv")
    # Create the directory first, then get the string path
    input_code_dir_path = tmp_path / "code_dir"
    input_code_dir_path.mkdir()
    input_code_dir_str = str(input_code_dir_path)

    # Mock csv.DictReader to pass validation
    mock_reader_instance = MagicMock()
    mock_reader_instance.fieldnames = ['prompt_name', 'change_instructions']
    mock_dict_reader.return_value = mock_reader_instance

    # Configure the open mock
    mock_file_handle = MagicMock()
    mock_open_instance.return_value.__enter__.return_value = mock_file_handle

    # Act
    result_tuple = change_main(
        ctx=mock_ctx,
        change_prompt_file=change_prompt_file,
        input_code=input_code_dir_str, # Use the string path
        input_prompt_file=None,
        output=None,
        use_csv=True
    )

    # Assert
    assert result_tuple == ("Multiple prompts have been updated.", 0.02, 'mock_model')
    mock_dict_reader.assert_called_once()
    mock_process_csv_change.assert_called_once()
    # Verify 'open' was called correctly for the individual files
    expected_dir = str(tmp_path)
    expected_calls = [
        ((os.path.join(expected_dir, 'file1_python.prompt'), 'w'),),
        ((os.path.join(expected_dir, 'file2_python.prompt'), 'w'),)
    ]

    # Filter calls to mock_open: check for mode 'w' safely
    write_calls = [call for call in mock_open_instance.call_args_list if len(call[0]) > 1 and call[0][1] == 'w']
    assert len(write_calls) == len(expected_calls)
    write_call_args = [c[0] for c in write_calls]
    assert sorted(write_call_args) == sorted([c[0] for c in expected_calls])
    mock_file_handle.write.assert_any_call('prompt1 content')
    mock_file_handle.write.assert_any_call('prompt2 content')
    assert mock_file_handle.write.call_count == 2