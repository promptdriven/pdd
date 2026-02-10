"""
Tests for the change_main module in the PDD project.

Contains comprehensive tests for the CLI change command's core functionality,
testing single-file changes and batch CSV processing.
"""
import pytest
import csv
import os
import io
from pathlib import Path
from unittest.mock import MagicMock, patch, mock_open, call
from click import Context
from pdd.change_main import change_main
from pdd import DEFAULT_STRENGTH

# Helper function to create a mocked Click context
def create_mock_context(params: dict = None, obj: dict = None):
    """
    Create a mock Click context with default values for testing.
    
    Args:
        params: Optional parameters dictionary
        obj: Optional object dictionary
        
    Returns:
        A configured mock Context object
    """
    mock_ctx = MagicMock(spec=Context)
    mock_ctx.params = params if params is not None else {}
    mock_ctx.obj = obj if obj is not None else {}
    # Ensure default values are present if not provided
    mock_ctx.obj.setdefault('quiet', False)
    mock_ctx.obj.setdefault('force', False)
    mock_ctx.obj.setdefault('strength', DEFAULT_STRENGTH)
    mock_ctx.obj.setdefault('temperature', 0)
    mock_ctx.obj.setdefault('language', 'python')
    mock_ctx.obj.setdefault('extension', '.py')
    mock_ctx.obj.setdefault('budget', 10.0)
    mock_ctx.obj.setdefault('verbose', False)
    mock_ctx.obj.setdefault('time', 0.25)
    return mock_ctx

@pytest.fixture
def setup_environment(tmp_path):
    """
    Sets up the temporary environment for the test, including input files and directories.
    """
    # Create directories
    code_directory = tmp_path / "example_code_directory"
    code_directory.mkdir()

    output_directory = tmp_path / "example_output_directory"
    # Don't create output dir here, let the code create it if needed

    # Create sample code files
    script1_py_path = code_directory / "script1.py"
    script1_py_content = """
def add(a, b):
    return a + b
"""
    script1_py_path.write_text(script1_py_content)

    script2_py_path = code_directory / "script2.py"
    script2_py_content = """
def subtract(a, b):
    return a - b
"""
    script2_py_path.write_text(script2_py_content)

    # Create corresponding prompt files (relative paths for CSV)
    # Save prompts in CWD relative to tmp_path for easier resolution in test
    prompt1_relative_path = "script1_python.prompt"
    prompt1_path = tmp_path / prompt1_relative_path
    prompt1_content = "Write a function to calculate the factorial of a number."
    prompt1_path.write_text(prompt1_content)

    prompt2_relative_path = "script2_python.prompt"
    prompt2_path = tmp_path / prompt2_relative_path
    prompt2_content = "Write a function to calculate the fibonacci sequence."
    prompt2_path.write_text(prompt2_content)

    # Create batch_changes.csv
    batch_changes_csv_path = tmp_path / "batch_changes.csv"
    with open(batch_changes_csv_path, 'w', newline='', encoding='utf-8') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=['prompt_name', 'change_instructions'])
        writer.writeheader()
        # Use relative paths in CSV as they might be resolved from CWD
        writer.writerow({
            'prompt_name': prompt1_relative_path, 
            'change_instructions': "Modify the function to handle overflow errors."
        })
        writer.writerow({
            'prompt_name': prompt2_relative_path, 
            'change_instructions': "Optimize the function for large numbers."
        })

    # Define the output file (CSV mode)
    batch_output_file_path = tmp_path / "batch_modified_prompts.csv"

    return {
        "tmp_path": tmp_path,  # Pass tmp_path itself for CWD context
        "code_directory": str(code_directory),
        "script1_py_path": str(script1_py_path),
        "script1_py_content": script1_py_content,
        "script2_py_path": str(script2_py_path),
        "script2_py_content": script2_py_content,
        "prompt1_relative_path": prompt1_relative_path,
        "prompt1_path": str(prompt1_path),
        "prompt1_content": prompt1_content,
        "prompt2_relative_path": prompt2_relative_path,
        "prompt2_path": str(prompt2_path),
        "prompt2_content": prompt2_content,
        "batch_changes_csv": str(batch_changes_csv_path),
        "batch_output_file": str(batch_output_file_path)
    }

# ***** MODIFIED TEST *****
@patch('pdd.change_main.process_csv_change')  # Mock process_csv_change directly
def test_change_main_batch_mode(mock_process_csv, setup_environment, caplog, monkeypatch):
    """
    Tests the `change_main` function in CSV batch-change mode by mocking
    process_csv_change and verifying the output CSV content.
    """
    caplog.set_level('DEBUG')
    env = setup_environment
    monkeypatch.chdir(env["tmp_path"])

    # --- Mock Setup ---
    # Mocks for path checks primarily needed for argument validation and CSV read
    def os_patched_is_dir(path):
        # Check if the path being checked is the code directory
        return str(Path(path).resolve()) == str(Path(env["code_directory"]).resolve())

    input_csv_content = (
        "prompt_name,change_instructions\n"
        f"{env['prompt1_relative_path']},Modify the function to handle overflow errors.\n"
        f"{env['prompt2_relative_path']},Optimize the function for large numbers.\n"
    )
    read_mock = mock_open(read_data=input_csv_content)
    write_mock = mock_open()

    def open_side_effect(file, mode='r', *args, **kwargs):
        if file in (env["batch_changes_csv"], Path(env["batch_changes_csv"])):
            return read_mock(file, mode, *args, **kwargs)
        elif file in (env["batch_output_file"], Path(env["batch_output_file"])):
            return write_mock(file, mode, *args, **kwargs)
        return mock_open()(file, mode, *args, **kwargs)


    # Mock return value for process_csv_change
    mock_process_csv.return_value = (
        True,  # success flag
        [  # modified_prompts_list
            {'file_name': env['prompt1_relative_path'], 'modified_prompt': 'Modified content 1'},
            {'file_name': env['prompt2_relative_path'], 'modified_prompt': 'Modified content 2'}
        ],
        0.50,  # total_cost
        'gpt-3.5-turbo'  # model_name
    )

    # Apply necessary patches
    with patch('os.path.isdir', os_patched_is_dir), \
         patch('os.makedirs'), \
         patch('builtins.open', side_effect=open_side_effect) as mock_file_open:

        # Mock construct_paths (still needed for output path determination)
        with patch('pdd.change_main.construct_paths') as mock_cp:
            mock_cp.return_value = (
                {},  # resolved_config
                {'change_prompt_file': 'Dummy CSV content read by open'},  # Content doesn't matter here
                {'output_prompt_file': env["batch_output_file"]},  # construct_paths determines output file path
                'python'  # Language inferred
            )

            # Execute the function under test
            ctx_instance = create_mock_context(
                params={"force": True},
                obj={
                    "strength": DEFAULT_STRENGTH, "temperature": 0, "budget": 10.0,
                    "verbose": False, "language": "python", "extension": ".py"
                }
            )
            message, total_cost, model_name = change_main(
                ctx=ctx_instance,
                change_prompt_file=env["batch_changes_csv"],
                input_code=env["code_directory"],
                input_prompt_file=None,
                output=env["batch_output_file"],
                use_csv=True,
                budget=ctx_instance.obj['budget']
            )

    # --- Assertions ---
    assert message == "Multiple prompts have been updated."
    assert total_cost == 0.50
    assert model_name == 'gpt-3.5-turbo'

    # Verify that process_csv_change was called correctly
    mock_process_csv.assert_called_once_with(
        csv_file=env["batch_changes_csv"],
        strength=DEFAULT_STRENGTH,
        temperature=0,
        time=0.25,
        code_directory=env["code_directory"],
        language='python',
        extension='.py',
        budget=10.0
    )

    # Verify logs show correct CSV processing (header check)
    assert "Validating CSV header..." in caplog.text
    assert "CSV header validated successfully." in caplog.text
    assert f"Saving batch results to CSV: {Path(env['batch_output_file']).resolve()}" in caplog.text
    
    # Check write calls
    write_mock.assert_called_once_with(Path(env["batch_output_file"]), 'w', newline='', encoding='utf-8')
    
    # Check the content written
    handle = write_mock()
    handle.write.assert_any_call('file_name,modified_prompt\r\n')
    handle.write.assert_any_call(f"{env['prompt1_relative_path']},Modified content 1\r\n")
    handle.write.assert_any_call(f"{env['prompt2_relative_path']},Modified content 2\r\n")
    assert handle.write.call_count == 3

# --- Fixtures for Mocking Dependencies (some might be unused now but kept for context) ---
@pytest.fixture
def mock_construct_paths_fixture():
    """Mock for the construct_paths function."""
    with patch('pdd.change_main.construct_paths') as mock:
        yield mock

@pytest.fixture
def mock_change_func_fixture():
    """Mock for the change_func function."""
    with patch('pdd.change_main.change_func') as mock:
        yield mock

@pytest.fixture
def mock_process_csv_change_fixture():
    """Mock for the process_csv_change function."""
    with patch('pdd.change_main.process_csv_change') as mock:
        yield mock

@pytest.fixture
def mock_rprint_fixture():
    """Mock for the rich.print function."""
    with patch('pdd.change_main.rprint') as mock:
        yield mock

@pytest.fixture
def mock_path_is_dir_fixture():
    """Mock for Path.is_dir method."""
    with patch('pathlib.Path.is_dir') as mock:
        yield mock

@pytest.fixture
def mock_path_is_file_fixture():
    """Mock for Path.is_file method."""
    with patch('pathlib.Path.is_file') as mock:
        yield mock

@pytest.fixture
def mock_csv_dictreader_fixture():
    """Mock for csv.DictReader."""
    with patch('csv.DictReader') as mock:
        yield mock

@pytest.fixture
def mock_open_function_fixture():
    """
    This fixture patches builtins.open for test functions.
    """
    with patch('builtins.open', mock_open()) as mock:
        yield mock

# === Test cases for non-CSV mode ===

@patch('os.path.isdir')
def test_change_main_non_csv_success(
    mock_os_isdir,
    mock_open_function_fixture, # Use the fixture
    mock_construct_paths_fixture,
    mock_change_func_fixture, # Keep mocking change_func for non-CSV
    mock_rprint_fixture,
):
    # Arrange
    ctx_instance = create_mock_context(
        params={'force': False, 'quiet': False},
        obj={'strength': 0.8, 'temperature': 0.5, 'budget': 10.0}
    )
    change_prompt_file = "path/to/change_prompt.txt"
    input_code = "path/to/input_code.py"
    input_prompt_file = "path/to/input_prompt.txt"
    output = "path/to/output_prompt.txt"
    use_csv = False

    # Mock isdir to return False for the input_code directory check
    mock_os_isdir.return_value = False

    # Mock construct_paths return value
    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {
            "change_prompt_file": "Change Prompt Content",
            "input_code": "Input Code Content",
            "input_prompt_file": "Input Prompt Content"
        },
        # construct_paths provides the default output path if --output is not given
        # If --output *is* given, output_file_paths might just contain {'output': output}
        {"output_prompt_file": output}, # Simulate construct_paths returning the path
        "python"
    )

    # Mock change_func return value
    modified_prompt = "Modified Prompt Content"
    total_cost = 0.05
    model_name = "gpt-3.5-turbo"
    mock_change_func_fixture.return_value = (modified_prompt, total_cost, model_name)

    # Act
    # Use resolve() on a Path object for consistency
    output_path_obj = Path(output).resolve() # Use resolve() here for consistency

    # Patch Path object's resolve method globally for this block if needed,
    # or ensure the mock_open_function handles the Path object correctly.
    # Here, we pass the resolved path object directly to assert_called_once_with.
    with patch.object(Path, 'resolve', return_value=output_path_obj) as mock_resolve, \
         patch.object(Path, 'mkdir') as mock_mkdir, \
         patch("pdd.change_main.run_user_story_tests") as mock_story_tests: # Mock user story validation
            mock_story_tests.return_value = (True, [], 0.0, "")
            result = change_main(
                ctx=ctx_instance,
                change_prompt_file=change_prompt_file,
                input_code=input_code,
                input_prompt_file=input_prompt_file,
                output=output, # Pass the original string path
                use_csv=use_csv,
                budget=ctx_instance.obj['budget']
            )
            # Assert Path.mkdir was called correctly on the *parent* of the resolved path
            # Access the parent via the resolved path object
            mock_mkdir.assert_called_once_with(parents=True, exist_ok=True)


    # Assert
    # The result message should reflect the actual resolved path used for saving
    assert result == (f"Modified prompt saved to {output_path_obj}", total_cost, model_name)
    # Assert open was called with the resolved path
    mock_open_function_fixture.assert_called_once_with(output_path_obj, 'w', encoding='utf-8')
    file_handle_mock = mock_open_function_fixture.return_value.__enter__.return_value
    file_handle_mock.write.assert_called_once_with(modified_prompt)

    mock_rprint_fixture.assert_any_call("[bold green]Prompt modification completed successfully.[/bold green]")
    mock_rprint_fixture.assert_any_call(f"[bold]Model used:[/bold] {model_name}")
    mock_rprint_fixture.assert_any_call(f"[bold]Total cost:[/bold] ${total_cost:.6f}")


@patch('os.path.isdir')
def test_change_main_non_csv_missing_input_prompt_file(
    mock_os_isdir,
    mock_rprint_fixture
):
    ctx_instance = create_mock_context(
        params={'force': False, 'quiet': False},
        obj={'strength': 0.8, 'temperature': 0.5, 'budget': 10.0} # budget added for consistency
    )
    change_prompt_file = "path/to/change_prompt.txt"
    input_code = "path/to/input_code.py"
    input_prompt_file = None
    output = "path/to/output_prompt.txt"
    use_csv = False

    mock_os_isdir.return_value = False

    result = change_main(
        ctx=ctx_instance,
        change_prompt_file=change_prompt_file,
        input_code=input_code,
        input_prompt_file=input_prompt_file,
        output=output,
        use_csv=use_csv,
        budget=ctx_instance.obj['budget']
    )

    expected_error = "[bold red]Error:[/bold red] --input-prompt-file is required when not using --csv mode."
    assert result == (expected_error, 0.0, "")
    mock_rprint_fixture.assert_called_once_with(expected_error)

@patch('os.path.isdir')
def test_change_main_non_csv_construct_paths_error(
    mock_os_isdir,
    mock_construct_paths_fixture,
    mock_rprint_fixture,
):
    ctx_instance = create_mock_context(
        params={'force': False, 'quiet': False},
        obj={'strength': 0.8, 'temperature': 0.5, 'budget': 10.0} # budget added
    )
    change_prompt_file = "path/to/change_prompt.txt"
    input_code = "path/to/input_code.py"
    input_prompt_file = "path/to/input_prompt.txt"
    output = "path/to/output_prompt.txt"
    use_csv = False

    mock_os_isdir.return_value = False
    mock_construct_paths_fixture.side_effect = Exception("Construct Paths Failed")

    # Act
    result = change_main(
        ctx=ctx_instance,
        change_prompt_file=change_prompt_file,
        input_code=input_code,
        input_prompt_file=input_prompt_file,
        output=output,
        use_csv=use_csv,
        budget=ctx_instance.obj['budget']
    )

    # Assert - Expect the specific error message from the code
    expected_error = "Error constructing paths: Construct Paths Failed"
    assert result == (expected_error, 0.0, "")
    mock_rprint_fixture.assert_called_once_with(f"[bold red]Error: {expected_error}[/bold red]")

@patch('os.path.isdir')
def test_change_main_non_csv_change_func_error(
    mock_os_isdir,
    mock_construct_paths_fixture,
    mock_change_func_fixture,
    mock_rprint_fixture,
):
    # Arrange
    ctx_instance = create_mock_context(
        params={'force': False, 'quiet': False},
        obj={'strength': 0.8, 'temperature': 0.5, 'budget': 10.0} # budget added
    )
    change_prompt_file = "path/to/change_prompt.txt"
    input_code = "path/to/input_code.py"
    input_prompt_file = "path/to/input_prompt.txt"
    output = "path/to/output_prompt.txt"
    use_csv = False

    mock_os_isdir.return_value = False
    mock_construct_paths_fixture.return_value = (
        {},  # resolved_config
        {
            "change_prompt_file": "Change Prompt Content",
            "input_code": "Input Code Content",
            "input_prompt_file": "Input Prompt Content"
        },
        {"output_prompt_file": output}, # Use default output key
        "python"
    )

    # Mock change_func to raise an exception
    mock_change_func_fixture.side_effect = Exception("Change Function Failed")

    # Act
    result = change_main(
        ctx=ctx_instance,
        change_prompt_file=change_prompt_file,
        input_code=input_code,
        input_prompt_file=input_prompt_file,
        output=output,
        use_csv=use_csv,
        budget=ctx_instance.obj['budget']
    )

    # Assert - Expect the specific error message from the code
    expected_error = "Error during prompt modification: Change Function Failed"
    assert result == (expected_error, 0.0, "")
    mock_rprint_fixture.assert_called_once_with(f"[bold red]Error: {expected_error}[/bold red]")

# === Test cases for CSV mode ===

# ***** MODIFIED TEST *****
@patch('pdd.change_main.process_csv_change') # Mock process_csv_change
@patch('pathlib.Path.exists')  # Add Path.exists patch
@patch('pathlib.Path.is_file')
@patch('pathlib.Path.is_dir')
@patch('builtins.open', new_callable=mock_open)
@patch('pdd.change_main.os.makedirs') # Mock os.makedirs
@patch('pdd.change_main.os.path.normpath') # Keep this mock
@patch('os.path.isdir')
def test_change_main_csv_output_none_saves_individual_files(
    mock_os_isdir,
    mock_normpath,
    mock_makedirs, # Use mock for os.makedirs
    mock_open_fixture,
    mock_path_is_dir, # Renamed arg
    mock_path_is_file, # Renamed arg
    mock_path_exists,  # Add this parameter for Path.exists patch
    mock_process_csv, # Use new mock
    mock_csv_dictreader_fixture, # Keep for header validation
    tmp_path,
    caplog,
    monkeypatch
):
    """
    Verify change_main saves individual files to CWD when --output is None in CSV mode.
    """
    caplog.set_level('DEBUG')
    # Arrange
    monkeypatch.chdir(tmp_path)
    output_dir = tmp_path # Files should be saved here (CWD)
    input_csv_path = tmp_path / "dummy.csv"
    csv_content = "prompt_name,change_instructions\nfile1_python.prompt,Change 1\nfile2_python.prompt,Change 2"
    input_csv_path.write_text(csv_content)
    code_dir = tmp_path / "code_dir"
    code_dir.mkdir()

    # Dummy files (names only)
    prompt1_name = "file1_python.prompt"
    prompt2_name = "file2_python.prompt"

    # 2. Setup context - Set force=True as per fix report analysis
    ctx_instance = create_mock_context(
        params={'force': True}, # <<< Set force=True
        obj={'quiet': True, 'language': 'python', 'extension': '.py', 'budget': 10.0} # budget added
    )

    # 3. Mock Path validation
    all_files = {str(input_csv_path.resolve())}
    all_dirs = {str(code_dir.resolve()), str(tmp_path.resolve())} # CWD is a dir
    mock_path_is_file.side_effect = lambda self: str(self.resolve()) in all_files
    mock_path_is_dir.side_effect = lambda self: str(self.resolve()) in all_dirs
    mock_os_isdir.side_effect = lambda path: str(Path(path).resolve()) == str(code_dir.resolve())
    
    # Fix the mock_path_exists with a proper side_effect function
    def path_exists_side_effect(self):
        # For individual output files, return False to allow creation (or bypass due to force=True)
        if self.parent == output_dir:
            return False
        return str(self.resolve()) in all_files

    mock_path_exists.side_effect = path_exists_side_effect

    # 4. Mock CSV header validation
    mock_csv_dictreader_fixture.return_value.fieldnames = ['prompt_name', 'change_instructions']

    # 5. Mock process_csv_change returns
    modified_prompts_list = [
        {'file_name': prompt1_name, 'modified_prompt': 'prompt1 content'},
        {'file_name': prompt2_name, 'modified_prompt': 'prompt2 content'}
    ]
    mock_process_csv.return_value = (True, modified_prompts_list, 0.04, 'mock_model')

    # Mock file opens
    mock_read_handles = {
        str(input_csv_path.resolve()): mock_open(read_data=csv_content).return_value,
    }
    def flexible_open(file, mode='r', *args, **kwargs):
        resolved_path_str = str(Path(file).resolve())
        if mode.startswith('r'):
            if file == input_csv_path:
                return mock_open(read_data=csv_content)(file, mode, *args, **kwargs)
            handle = mock_read_handles.get(resolved_path_str)
            if handle:
                m_open = mock_open(read_data=handle.read())
                handle.seek(0)
                return m_open(file, mode, *args, **kwargs)
            else: return mock_open()(file, mode, *args, **kwargs)
        elif mode.startswith('w'):
             # Use the fixture's mock for writes
             return mock_open_fixture(file, mode, *args, **kwargs)
        return mock_open_fixture(file, mode, *args, **kwargs)

    # Act
    with patch('pdd.change_main.construct_paths') as mock_construct_paths, \
         patch('builtins.open', flexible_open), \
         patch('pathlib.Path.is_file', mock_path_is_file.side_effect), \
         patch('pathlib.Path.is_dir', mock_path_is_dir.side_effect), \
         patch('os.path.isdir', mock_os_isdir.side_effect), \
         patch('pathlib.Path.exists', mock_path_exists.side_effect):

        # Mock construct_paths return value (output should be None here)
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {'change_prompt_file': 'dummy content'},
            {}, # output_file_paths reflects no --output given
            'python'
        )
        result_tuple = change_main(
            ctx=ctx_instance,
            change_prompt_file=str(input_csv_path),
            input_code=str(code_dir),
            input_prompt_file=None,
            output=None, # <<< Output is None
            use_csv=True,
            budget=ctx_instance.obj['budget']
        )

    # Assert
    assert result_tuple == ("Multiple prompts have been updated.", 0.04, 'mock_model')

    # Verify directory creation was attempted for CWD using os.makedirs
    mock_makedirs.assert_called_once_with(Path.cwd(), exist_ok=True) # Assert os.makedirs call

    # Verify 'open' was called correctly for the individual files in CWD (tmp_path)
    expected_calls = [
        call(output_dir / prompt1_name, 'w', encoding='utf-8'),
        call(output_dir / prompt2_name, 'w', encoding='utf-8'),
    ]
    # Filter out read calls before asserting write calls
    write_calls = [c for c in mock_open_fixture.call_args_list if len(c.args) > 1 and c.args[1].startswith('w')]
    assert len(write_calls) == len(expected_calls)
    # Use assert_has_calls for more robust checking of write calls
    mock_open_fixture.assert_has_calls(expected_calls, any_order=True)

    # Verify writes
    handle = mock_open_fixture()
    handle.write.assert_any_call('prompt1 content')
    handle.write.assert_any_call('prompt2 content')
    assert handle.write.call_count == 2


# ***** MODIFIED TEST *****
@patch('pdd.change_main.rprint')
@patch('os.path.isdir')
@patch('pathlib.Path.is_dir')
@patch('pathlib.Path.is_file')
def test_change_main_csv_input_code_not_directory(
    mock_is_file,
    mock_is_dir,
    mock_os_isdir,
    mock_rprint,
    tmp_path
):
    ctx_instance = create_mock_context(
        params={'force': False, 'quiet': False},
        obj={'strength': 0.6, 'temperature': 0.4, 'budget': 10.0} # budget added
    )
    change_prompt_file = tmp_path / "change_prompts.csv"
    change_prompt_file.touch()
    input_code_file = tmp_path / "input_file.py"
    input_code_file.touch()
    output = tmp_path / "output.csv"
    use_csv = True

    mock_is_file.return_value = True # Mock file checks
    mock_is_dir.return_value = False # Mock dir checks
    mock_os_isdir.return_value = False # Input code is NOT a dir

    result = change_main(
        ctx=ctx_instance,
        change_prompt_file=str(change_prompt_file),
        input_code=str(input_code_file),
        input_prompt_file=None,
        output=str(output),
        use_csv=use_csv,
        budget=ctx_instance.obj['budget']
    )

    expected_error = f"[bold red]Error:[/bold red] In CSV mode, --input-code ('{input_code_file}') must be a valid directory."
    assert result == (expected_error, 0.0, "")
    mock_rprint.assert_called_once_with(expected_error)

# ***** MODIFIED TEST *****
@patch('pdd.change_main.construct_paths')
@patch('builtins.open')
@patch('csv.DictReader')
@patch('pdd.change_main.rprint')
@patch('os.path.isdir')
@patch('pathlib.Path.is_dir')
@patch('pathlib.Path.is_file')
def test_change_main_csv_missing_columns(
    mock_is_file,
    mock_is_dir,
    mock_os_isdir,
    mock_rprint,
    mock_csv_dictreader, # Mock DictReader for header check
    mock_open, # Needs to return bad CSV for header check
    mock_construct_paths,
    tmp_path
):
    ctx_instance = create_mock_context(
        params={'force': False, 'quiet': False},
        obj={'strength': 0.6, 'temperature': 0.4, 'budget': 10.0} # budget added
    )
    change_prompt_file = tmp_path / "change_prompts.csv"
    bad_csv_content = "invalid_column1,invalid_column2\nval1,val2"
    change_prompt_file.write_text(bad_csv_content)
    code_directory = tmp_path / "code_directory"
    code_directory.mkdir()
    output = tmp_path / "output.csv"
    use_csv = True

    # Mock path checks
    mock_os_isdir.return_value = True # Input code is a dir
    mock_is_dir.return_value = True # Mocks for Path.is_dir
    mock_is_file.return_value = True # Mocks for Path.is_file

    def open_side_effect(file, mode='r', **kwargs):
        if str(Path(file).resolve()) == str(change_prompt_file.resolve()):
            return io.StringIO(bad_csv_content)
        return mock_open()()

    # Set up the mock open to return the bad CSV content when reading the input CSV
    mock_open.side_effect = open_side_effect

    # Configure the mock DictReader to reflect the bad header
    mock_csv_dictreader.return_value.fieldnames = ["invalid_column1", "invalid_column2"]
    # The header validation should fail now *before* construct_paths is called
    result = change_main(
        ctx=ctx_instance,
        change_prompt_file=str(change_prompt_file),
        input_code=str(code_directory),
        input_prompt_file=None,
        output=str(output),
        use_csv=use_csv,
        budget=ctx_instance.obj['budget']
    )

    # Assert the specific error message from the header validation
    expected_error = "CSV file must contain 'prompt_name' and 'change_instructions' columns. Missing: {'prompt_name', 'change_instructions'}"
    # The exact order in the set string might vary, so check components
    assert result[0].startswith("CSV file must contain 'prompt_name' and 'change_instructions' columns.")
    assert "'prompt_name'" in result[0]
    assert "'change_instructions'" in result[0]
    assert result[1] == 0.0
    assert result[2] == ""
    mock_rprint.assert_called_once_with(f"[bold red]Error: {result[0]}[/bold red]") # Check the printed error
    mock_construct_paths.assert_not_called() # Ensure construct_paths was NOT called


# ***** MODIFIED TEST *****
@patch('pdd.change_main.process_csv_change') # Mock process_csv_change
@patch('pdd.change_main.os.path.normpath')
@patch('pdd.change_main.os.makedirs')
@patch('builtins.open', new_callable=mock_open)
@patch('pathlib.Path.is_dir')
@patch('pathlib.Path.is_file')
@patch('os.path.isdir')
@patch('csv.DictReader')
def test_change_main_csv_output_dir_slash_saves_individual_files(
    mock_csv_dictreader,
    mock_os_isdir,
    mock_path_is_file,
    mock_path_is_dir,
    mock_open_fixture,
    mock_makedirs,
    mock_normpath,
    mock_process_csv,
    tmp_path,
    caplog,
    monkeypatch
):
    """
    Test that change_main correctly handles a directory path ending with a slash
    provided via --output in CSV mode, saving individual files.
    """
    caplog.set_level('DEBUG')
    # Arrange
    monkeypatch.chdir(tmp_path)
    output_dir_with_slash_str = str(tmp_path / "output") + "/" # Path with slash
    output_dir_normalized = Path(str(tmp_path / "output")) # Normalized path
    input_csv_path = tmp_path / "changes.csv"
    csv_content = "prompt_name,change_instructions\nfile1.prompt,Change 1"
    input_csv_path.write_text(csv_content)
    code_dir = tmp_path / "code"
    code_dir.mkdir()

    # Dummy files (names only)
    prompt1_name = "file1.prompt"
    # Code file not needed for mock

    # 2. Setup context
    ctx_instance = create_mock_context(
        params={'force': False},
        obj={'quiet': True, 'language': 'python', 'extension': '.py', 'budget': 10.0} # budget added
    )

    # 3. Mock Path validation and os checks
    all_files = {str(input_csv_path.resolve())}
    # Assume output dir will exist after mkdir call
    all_dirs = {str(code_dir.resolve()), str(output_dir_normalized.resolve()), str(tmp_path.resolve())}

    mock_path_is_file.side_effect = lambda self: str(self.resolve()) in all_files
    mock_path_is_dir.return_value = True
    mock_os_isdir.return_value = True
    
    # This mock needs to be active when change_main calls it
    mock_normpath.return_value = str(output_dir_normalized)


    # 4. Mock CSV header validation
    mock_csv_dictreader.return_value.fieldnames = ['prompt_name', 'change_instructions']

    # 5. Mock process_csv_change returns
    modified_prompts_list = [{'file_name': prompt1_name, 'modified_prompt': 'Modified 1'}]
    mock_process_csv.return_value = (True, modified_prompts_list, 0.01, "model-x")

    # Mock file opens - input CSV read, output file write
    mock_read_handles = {
        str(input_csv_path): mock_open(read_data=csv_content).return_value,
    }

    def flexible_open(file, mode='r', *args, **kwargs):
        if mode.startswith('r'):
            if str(file) == str(input_csv_path):
                return mock_open(read_data=csv_content)(file, mode, *args, **kwargs)
            else: return mock_open()(file, mode, *args, **kwargs)
        elif mode.startswith('w'):
             # Use the fixture's mock for writes
             return mock_open_fixture(file, mode, *args, **kwargs)
        return mock_open_fixture(file, mode, *args, **kwargs)

    # Act
    with patch('pdd.change_main.construct_paths') as mock_construct_paths, \
         patch('builtins.open', flexible_open):

        # Mock construct_paths return (output path here should be the *normalized* one)
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {'change_prompt_file': 'dummy content'},
            {'output': str(output_dir_normalized)}, # construct_paths receives normalized path
            'python'
        )

        result_message, result_cost, result_model = change_main(
            ctx=ctx_instance,
            change_prompt_file=str(input_csv_path),
            input_code=str(code_dir),
            input_prompt_file=None,
            output=output_dir_with_slash_str, # Pass original path with slash
            use_csv=True,
            budget=ctx_instance.obj['budget']
        )

    # Assert Correct Behavior
    # 1. Check os.path.normpath was called with the original path ending in slash
    mock_normpath.assert_any_call(output_dir_with_slash_str) # <--- Changed to assert_any_call

    # 2. Check that os.makedirs was called for the *normalized* directory path
    mock_makedirs.assert_called_once_with(output_dir_normalized, exist_ok=True) # Assert os.makedirs call

    # 3. Check that open was called for the file *inside* the normalized directory
    expected_file_path = output_dir_normalized / prompt1_name
    # Filter write calls
    write_calls = [c for c in mock_open_fixture.call_args_list if len(c.args) > 1 and c.args[1].startswith('w')]
    assert len(write_calls) == 1
    # Use assert_has_calls which is more robust for checking calls on mocks used as context managers
    mock_open_fixture.assert_has_calls([call(expected_file_path, 'w', encoding='utf-8')], any_order=False)


    # 4. Check that CSV writing was NOT attempted on the directory itself
    # (This check might be less relevant now as we're saving individual files)
    directory_write_attempted = any(
         c.args[0] == output_dir_normalized and c.args[1].startswith('w')
         for c in mock_open_fixture.call_args_list if len(c.args) > 1
    )

    assert not directory_write_attempted, f"Attempted to open directory {output_dir_normalized} for writing."


    # 5. Check return values for success
    assert result_message == "Multiple prompts have been updated."
    assert result_cost == 0.01
    assert result_model == "model-x"

    # 6. Check logs indicate saving individual files in directory
    assert f"Saving individual modified prompts to directory: {output_dir_normalized}" in caplog.text
    assert f"Attempting to save file to: {expected_file_path}" in caplog.text
    assert "Results saved as individual files in directory successfully" in caplog.text


# --- Tests for empty modified_prompt in CSV individual file saving ---

@patch('pdd.change_main.process_csv_change')
@patch('pdd.change_main.construct_paths')
def test_change_csv_skips_empty_modified_content(mock_construct_paths, mock_process_csv, tmp_path, caplog):
    """
    When process_csv_change returns a result with an empty string for
    modified_prompt, no file should be written for that entry.
    Regression test for: empty string passes 'is None' check and writes 0-byte file.
    """
    import logging
    caplog.set_level(logging.DEBUG)

    # Setup real files
    output_dir = tmp_path / "output"
    output_dir.mkdir()
    csv_file = tmp_path / "changes.csv"
    csv_file.write_text("prompt_name,change_instructions\nempty.prompt,Make it better\n")
    code_dir = tmp_path / "code"
    code_dir.mkdir()
    (code_dir / "empty.py").write_text("def placeholder(): pass\n")

    # Mock construct_paths
    mock_construct_paths.return_value = (
        {"strength": 0.5, "temperature": 0.0, "time": 0.25},  # resolved_config
        {"change_prompt_file": "prompt_name,change_instructions\nempty.prompt,Make it better\n"},
        {"output_prompt_file": str(output_dir)},
        "python"
    )

    # Mock process_csv_change to return empty modified_prompt
    mock_process_csv.return_value = (
        True,
        [{"file_name": "empty.prompt", "modified_prompt": ""}],  # Empty string!
        0.01,
        "test-model"
    )

    ctx = create_mock_context(
        params={"force": True},
        obj={
            "strength": 0.5,
            "temperature": 0.0,
            "budget": 10.0,
            "verbose": False,
            "language": "python",
            "extension": ".py",
            "quiet": False,
            "force": True,
            "time": 0.25,
        }
    )

    result_message, cost, model = change_main(
        ctx=ctx,
        change_prompt_file=str(csv_file),
        input_code=str(code_dir),
        input_prompt_file=None,
        output=str(output_dir),
        use_csv=True,
        budget=10.0,
    )

    # The empty.prompt file should NOT be created
    empty_file = output_dir / "empty.prompt"
    assert not empty_file.exists(), \
        f"File {empty_file} should not be written when modified_prompt is empty string"


def test_change_main_user_story_validation_failure(tmp_path):
    change_file = tmp_path / "change.prompt"
    code_file = tmp_path / "code.py"
    prompt_file = tmp_path / "input.prompt"
    output_file = tmp_path / "modified.prompt"
    change_file.write_text("Change request", encoding="utf-8")
    code_file.write_text("print('hi')", encoding="utf-8")
    prompt_file.write_text("Original prompt", encoding="utf-8")

    ctx_instance = create_mock_context(
        obj={
            "quiet": True,
            "force": True,
            "strength": DEFAULT_STRENGTH,
            "temperature": 0,
            "language": "python",
            "extension": ".py",
            "time": 0.25,
        }
    )

    with patch("pdd.change_main.construct_paths") as mock_construct, \
         patch("pdd.change_main.change_func") as mock_change, \
         patch("pdd.change_main.run_user_story_tests") as mock_story_tests:
        mock_construct.return_value = (
            {"prompts_dir": str(tmp_path / "prompts")},
            {
                "change_prompt_file": "Change request",
                "input_code": "print('hi')",
                "input_prompt_file": "Original prompt",
            },
            {"output_prompt_file": str(output_file)},
            "python",
        )
        mock_change.return_value = ("Modified prompt", 0.2, "model-a")
        mock_story_tests.return_value = (False, [{"story": "s", "passed": False}], 0.3, "model-b")

        message, total_cost, model_name = change_main(
            ctx=ctx_instance,
            change_prompt_file=str(change_file),
            input_code=str(code_file),
            input_prompt_file=str(prompt_file),
            output=str(output_file),
            use_csv=False,
            budget=5.0,
        )

    assert message == "User story validation failed. Review detect results for details."
    assert total_cost == pytest.approx(0.5)
    assert model_name == "model-a"


def test_change_main_skip_user_story_validation(tmp_path):
    change_file = tmp_path / "change.prompt"
    code_file = tmp_path / "code.py"
    prompt_file = tmp_path / "input.prompt"
    output_file = tmp_path / "modified.prompt"
    change_file.write_text("Change request", encoding="utf-8")
    code_file.write_text("print('hi')", encoding="utf-8")
    prompt_file.write_text("Original prompt", encoding="utf-8")

    ctx_instance = create_mock_context(
        obj={
            "quiet": True,
            "force": True,
            "skip_user_stories": True,
            "strength": DEFAULT_STRENGTH,
            "temperature": 0,
            "language": "python",
            "extension": ".py",
            "time": 0.25,
        }
    )

    with patch("pdd.change_main.construct_paths") as mock_construct, \
         patch("pdd.change_main.change_func") as mock_change, \
         patch("pdd.change_main.run_user_story_tests") as mock_story_tests:
        mock_construct.return_value = (
            {"prompts_dir": str(tmp_path / "prompts")},
            {
                "change_prompt_file": "Change request",
                "input_code": "print('hi')",
                "input_prompt_file": "Original prompt",
            },
            {"output_prompt_file": str(output_file)},
            "python",
        )
        mock_change.return_value = ("Modified prompt", 0.2, "model-a")
        mock_story_tests.side_effect = AssertionError("run_user_story_tests should not be called")

        message, total_cost, model_name = change_main(
            ctx=ctx_instance,
            change_prompt_file=str(change_file),
            input_code=str(code_file),
            input_prompt_file=str(prompt_file),
            output=str(output_file),
            use_csv=False,
            budget=5.0,
        )

    assert "Modified prompt saved to" in message
    assert total_cost == pytest.approx(0.2)
    assert model_name == "model-a"


def test_change_main_user_story_validation_uses_output_dir(tmp_path):
    csv_file = tmp_path / "changes.csv"
    csv_file.write_text("prompt_name,change_instructions\nfoo.prompt,Do it\n", encoding="utf-8")
    code_dir = tmp_path / "code"
    code_dir.mkdir()
    (code_dir / "foo.py").write_text("pass", encoding="utf-8")
    output_dir = tmp_path / "modified_prompts"

    ctx_instance = create_mock_context(
        obj={
            "quiet": True,
            "force": True,
            "strength": DEFAULT_STRENGTH,
            "temperature": 0,
            "language": "python",
            "extension": ".py",
            "time": 0.25,
        }
    )

    out_prompt = output_dir / "foo.prompt"
    base_prompt = tmp_path / "prompts" / "foo.prompt"
    base_other = tmp_path / "prompts" / "bar.prompt"

    with patch("pdd.change_main.construct_paths") as mock_construct, \
         patch("pdd.change_main.process_csv_change") as mock_process, \
         patch("pdd.change_main.discover_prompt_files") as mock_discover, \
         patch("pdd.change_main.run_user_story_tests") as mock_story_tests:
        mock_construct.return_value = (
            {"prompts_dir": str(tmp_path / "prompts")},
            {"change_prompt_file": csv_file.read_text(encoding="utf-8")},
            {"output_prompt_file": str(output_dir)},
            "python",
        )
        mock_process.return_value = (
            True,
            [{"file_name": "foo.prompt", "modified_prompt": "updated"}],
            0.1,
            "model-a",
        )
        mock_discover.side_effect = [[out_prompt], [base_prompt, base_other]]
        mock_story_tests.return_value = (True, [], 0.0, "")

        change_main(
            ctx=ctx_instance,
            change_prompt_file=str(csv_file),
            input_code=str(code_dir),
            input_prompt_file=None,
            output=str(output_dir),
            use_csv=True,
            budget=5.0,
        )

    _, kwargs = mock_story_tests.call_args
    assert kwargs["prompt_files"] == [out_prompt, base_other]


def test_change_main_skips_user_story_validation_for_csv_output(tmp_path):
    csv_file = tmp_path / "changes.csv"
    csv_file.write_text("prompt_name,change_instructions\nfoo.prompt,Do it\n", encoding="utf-8")
    code_dir = tmp_path / "code"
    code_dir.mkdir()
    (code_dir / "foo.py").write_text("pass", encoding="utf-8")
    output_csv = tmp_path / "modified_prompts.csv"

    ctx_instance = create_mock_context(
        obj={
            "quiet": True,
            "force": True,
            "strength": DEFAULT_STRENGTH,
            "temperature": 0,
            "language": "python",
            "extension": ".py",
            "time": 0.25,
        }
    )

    with patch("pdd.change_main.construct_paths") as mock_construct, \
         patch("pdd.change_main.process_csv_change") as mock_process, \
         patch("pdd.change_main.run_user_story_tests") as mock_story_tests:
        mock_construct.return_value = (
            {"prompts_dir": str(tmp_path / "prompts")},
            {"change_prompt_file": csv_file.read_text(encoding="utf-8")},
            {"output_prompt_file": str(output_csv)},
            "python",
        )
        mock_process.return_value = (
            True,
            [{"file_name": "foo.prompt", "modified_prompt": "updated"}],
            0.1,
            "model-a",
        )
        mock_story_tests.side_effect = AssertionError("run_user_story_tests should not be called for CSV output")

        message, total_cost, model_name = change_main(
            ctx=ctx_instance,
            change_prompt_file=str(csv_file),
            input_code=str(code_dir),
            input_prompt_file=None,
            output=str(output_csv),
            use_csv=True,
            budget=5.0,
        )

    assert message == "Multiple prompts have been updated."
    assert total_cost == pytest.approx(0.1)
    assert model_name == "model-a"
