import pytest
import os
import csv
from pathlib import Path
from unittest.mock import patch, mock_open, MagicMock, call

# Assuming the package is named 'pdd' and the module is 'process_csv_change.py'
from pdd.process_csv_change import process_csv_change, resolve_prompt_path

# Helper to create mock file system checks
def create_mock_fs(existing_files=None, existing_dirs=None):
    existing_files = existing_files or set()
    existing_dirs = existing_dirs or set()

    # Normalize paths for consistent checking
    abs_files = {os.path.abspath(f) for f in existing_files}
    abs_dirs = {os.path.abspath(d) for d in existing_dirs}

    def mock_exists(path):
        abs_path = os.path.abspath(str(path))
        return abs_path in abs_files or abs_path in abs_dirs

    def mock_isfile(path):
        return os.path.abspath(str(path)) in abs_files

    def mock_isdir(path):
        return os.path.abspath(str(path)) in abs_dirs

    return mock_exists, mock_isfile, mock_isdir

@pytest.fixture
def mock_change_fixture():
    """
    Fixture to mock the 'change' function used within 'process_csv_change'.
    """
    with patch("pdd.process_csv_change.change") as mock:
        yield mock

# --- Test Input Validations ---

def test_missing_csv_file(mock_change_fixture, capsys):
    """
    Test that the function handles the case when the CSV file does not exist.
    """
    csv_file = "non_existent.csv"
    code_directory = "/path/to/code" # Assume exists for this test

    mock_exists, mock_isfile, mock_isdir = create_mock_fs(existing_dirs={code_directory})

    with patch("os.path.exists", mock_exists), \
         patch("os.path.isfile", mock_isfile), \
         patch("os.path.isdir", mock_isdir):
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, 0.5, 0.5, code_directory, "python", ".py", 10.0
        )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name is None # Expect None on early validation error
    captured = capsys.readouterr()
    assert f"Error: CSV file not found or is not a file: '{csv_file}'" in captured.out

def test_invalid_strength(mock_change_fixture, capsys):
    """
    Test that the function handles invalid strength values.
    """
    csv_file = "valid.csv"
    strength = 1.5  # Invalid
    code_directory = "/path/to/code"

    mock_exists, mock_isfile, mock_isdir = create_mock_fs(existing_files={csv_file}, existing_dirs={code_directory})

    with patch("os.path.exists", mock_exists), \
         patch("os.path.isfile", mock_isfile), \
         patch("os.path.isdir", mock_isdir):
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, strength, 0.5, code_directory, "python", ".py", 10.0
        )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name is None # Expect None on early validation error
    captured = capsys.readouterr()
    assert f"Error: 'strength' must be between 0.0 and 1.0. Given: {strength}" in captured.out

def test_invalid_temperature(mock_change_fixture, capsys):
    """
    Test that the function handles invalid temperature values.
    """
    csv_file = "valid.csv"
    temperature = -0.1  # Invalid
    code_directory = "/path/to/code"

    mock_exists, mock_isfile, mock_isdir = create_mock_fs(existing_files={csv_file}, existing_dirs={code_directory})

    with patch("os.path.exists", mock_exists), \
         patch("os.path.isfile", mock_isfile), \
         patch("os.path.isdir", mock_isdir):
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, 0.5, temperature, code_directory, "python", ".py", 10.0
        )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name is None # Expect None on early validation error
    captured = capsys.readouterr()
    # Assuming range 0-1 based on implementation fix
    assert f"Error: 'temperature' must be between 0.0 and 1.0. Given: {temperature}" in captured.out

def test_invalid_code_directory(mock_change_fixture, capsys):
    """
    Test that the function handles invalid code directory paths.
    """
    csv_file = "valid.csv"
    code_directory = "/invalid/code/directory"

    # Simulate only CSV exists, code_directory does not
    mock_exists, mock_isfile, mock_isdir = create_mock_fs(existing_files={csv_file})

    # Patch console.print to check the specific error message format
    with patch("pdd.process_csv_change.console.print") as mock_print, \
         patch("os.path.exists", mock_exists), \
         patch("os.path.isfile", mock_isfile), \
         patch("os.path.isdir", mock_isdir):
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, 0.5, 0.5, code_directory, "python", ".py", 10.0
        )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name is None # Expect None on early validation error
    mock_print.assert_any_call(f"[bold red]Error:[/bold red] Code directory not found or is not a directory: '{code_directory}'")

def test_invalid_budget(mock_change_fixture, capsys):
    """ Test invalid negative budget """
    csv_file = "valid.csv"
    code_directory = "/path/to/code"
    budget = -1.0 # Invalid

    mock_exists, mock_isfile, mock_isdir = create_mock_fs(existing_files={csv_file}, existing_dirs={code_directory})

    with patch("os.path.exists", mock_exists), \
         patch("os.path.isfile", mock_isfile), \
         patch("os.path.isdir", mock_isdir):
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, 0.5, 0.5, code_directory, "python", ".py", budget
        )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name is None
    captured = capsys.readouterr()
    assert f"Error: 'budget' must be non-negative. Given: {budget}" in captured.out


# --- Test CSV Content Issues ---

def test_missing_columns_in_csv(mock_change_fixture, capsys):
    """
    Test that the function handles CSV files missing required columns.
    """
    csv_file = "valid_missing_cols.csv"
    code_directory = "/path/to/code"
    csv_content = "wrong_column1,wrong_column2\nvalue1,value2"

    mock_exists, mock_isfile, mock_isdir = create_mock_fs(existing_files={csv_file}, existing_dirs={code_directory})

    with patch("os.path.exists", mock_exists), \
         patch("os.path.isfile", mock_isfile), \
         patch("os.path.isdir", mock_isdir), \
         patch("builtins.open", mock_open(read_data=csv_content)):
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, 0.5, 0.5, code_directory, "python", ".py", 10.0
        )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name is None # Expect None on early validation error
    captured = capsys.readouterr()
    # Check for the specific error message about missing columns
    assert "Error: CSV file must contain 'prompt_name' and 'change_instructions' columns." in captured.out
    assert "Missing:" in captured.out
    assert "'prompt_name'" in captured.out
    assert "'change_instructions'" in captured.out

def test_empty_csv_file(mock_change_fixture, capsys):
    """ Test processing an empty CSV file """
    csv_file = "empty.csv"
    code_directory = "/path/to/code"
    csv_content = "" # Empty file

    mock_exists, mock_isfile, mock_isdir = create_mock_fs(existing_files={csv_file}, existing_dirs={code_directory})

    with patch("os.path.exists", mock_exists), \
         patch("os.path.isfile", mock_isfile), \
         patch("os.path.isdir", mock_isdir), \
         patch("builtins.open", mock_open(read_data=csv_content)):
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, 0.5, 0.5, code_directory, "python", ".py", 10.0
        )

    assert success # Should be considered success as no processing failed
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == "N/A" # No successful changes
    captured = capsys.readouterr()
    assert "Warning: CSV file is empty." in captured.out
    assert "Overall Success Status: True" in captured.out # Check summary

def test_csv_header_only(mock_change_fixture, capsys):
    """ Test processing a CSV with only a header row """
    csv_file = "header_only.csv"
    code_directory = "/path/to/code"
    csv_content = "prompt_name,change_instructions\n" # Header only

    mock_exists, mock_isfile, mock_isdir = create_mock_fs(existing_files={csv_file}, existing_dirs={code_directory})

    with patch("os.path.exists", mock_exists), \
         patch("os.path.isfile", mock_isfile), \
         patch("os.path.isdir", mock_isdir), \
         patch("builtins.open", mock_open(read_data=csv_content)):
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, 0.5, 0.5, code_directory, "python", ".py", 10.0
        )

    assert success # Should be success as no rows failed
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == "N/A" # No successful changes
    captured = capsys.readouterr()
    assert "CSV processing finished successfully (no data rows found)." in captured.out # Check summary message
    assert "Total Rows Processed: 0" in captured.out
    assert "Successful Changes: 0" in captured.out
    assert "Overall Success Status: True" in captured.out

# --- Test Row Processing Issues ---

@pytest.mark.parametrize("missing_col", ["prompt_name", "change_instructions"])
def test_missing_data_in_row(mock_change_fixture, capsys, missing_col):
    """
    Test that the function handles rows with missing 'prompt_name' or 'change_instructions'.
    It should skip the bad row, process the good row, and return success=False.
    """
    csv_file = "mixed_rows.csv"
    code_directory = "/path/to/code"
    prompt1_name = "prompt1_python.prompt"
    prompt1_path = os.path.abspath(os.path.join(code_directory, prompt1_name))
    code1_path = os.path.abspath(os.path.join(code_directory, "prompt1.py"))

    # Row 1: Missing data, Row 2: Valid
    csv_rows = [
        {"prompt_name": "bad_prompt.prompt", "change_instructions": "Bad Change"},
        {"prompt_name": prompt1_name, "change_instructions": "Good Change"}
    ]
    # Make one column empty in the first row
    csv_rows[0][missing_col] = ""

    csv_content = f"prompt_name,change_instructions\n" + \
                  f"{csv_rows[0]['prompt_name']},{csv_rows[0]['change_instructions']}\n" + \
                  f"{csv_rows[1]['prompt_name']},{csv_rows[1]['change_instructions']}\n"

    # Mock FS: CSV, code_dir, prompt1, code1 exist
    mock_exists, mock_isfile, mock_isdir = create_mock_fs(
        existing_files={csv_file, prompt1_path, code1_path},
        existing_dirs={code_directory}
    )
    # Mock change to return success for the second row
    mock_change_fixture.return_value = ("modified prompt 1", 1.0, "model_v1")

    # Mock resolve_prompt_path to find prompt1, but maybe not bad_prompt (though it won't be read)
    def mock_resolve(p_name, csv_f, code_dir):
        if p_name == prompt1_name:
            return prompt1_path
        return None # Or return a path for bad_prompt, it shouldn't matter

    with patch("os.path.exists", mock_exists), \
         patch("os.path.isfile", mock_isfile), \
         patch("os.path.isdir", mock_isdir), \
         patch("builtins.open", mock_open(read_data=csv_content)), \
         patch("pdd.process_csv_change.resolve_prompt_path", mock_resolve), \
         patch("pdd.process_csv_change.get_extension", return_value=".py"): # Mock get_extension

        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, 0.5, 0.5, code_directory, "python", ".py", 10.0
        )

    assert not success # Overall success is False because a row was skipped
    assert list_of_jsons == [{"file_name": prompt1_name, "modified_prompt": "modified prompt 1"}]
    assert total_cost == 1.0
    assert model_name == "model_v1"
    captured = capsys.readouterr()
    assert f"Warning: Missing '{missing_col}' in row 1. Skipping." in captured.out
    assert f"Successfully processed change for: {prompt1_name}" in captured.out
    assert "Overall Success Status: False" in captured.out # Check summary

def test_nonexistent_prompt_file_in_row(mock_change_fixture, capsys):
    """
    Test that the function handles rows where the prompt file cannot be resolved.
    """
    csv_file = "missing_prompt.csv"
    code_directory = "/path/to/code"
    prompt_name_csv = "non_existent_language.prompt" # This won't be found by resolve_prompt_path
    csv_content = f"prompt_name,change_instructions\n{prompt_name_csv},Modify the function"

    # Mock FS: Only CSV and code_dir exist
    mock_exists, mock_isfile, mock_isdir = create_mock_fs(
        existing_files={csv_file},
        existing_dirs={code_directory}
    )

    # Mock resolve_prompt_path to explicitly return None for the given name
    with patch("os.path.exists", mock_exists), \
         patch("os.path.isfile", mock_isfile), \
         patch("os.path.isdir", mock_isdir), \
         patch("builtins.open", mock_open(read_data=csv_content)), \
         patch("pdd.process_csv_change.resolve_prompt_path", return_value=None), \
         patch("pdd.process_csv_change.console.print") as mock_print: # Mock print to check error

        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, 0.5, 0.5, code_directory, "python", ".py", 10.0
        )

    assert not success # Failed because row couldn't be processed
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == "N/A" # No successful changes
    # Check for the specific error message from the code
    expected_error = f"[bold red]Error:[/bold red] Prompt file for '{prompt_name_csv}' not found in any location (row 1)."
    mock_print.assert_any_call(expected_error)
    # Check summary output via mock_print
    mock_print.assert_any_call("[bold]Overall Success Status:[/bold] False")

def test_nonexistent_code_file_in_row(mock_change_fixture, capsys):
    """
    Test that the function handles rows where the derived code file does not exist.
    """
    csv_file = "missing_code.csv"
    code_directory = "/path/to/code"
    prompt_name_csv = "valid_prompt_python.prompt"
    resolved_prompt_path = os.path.abspath(os.path.join(code_directory, prompt_name_csv))
    # Derived code path that *won't* exist in mock FS
    derived_code_path = os.path.abspath(os.path.join(code_directory, "valid_prompt.py"))

    csv_content = f"prompt_name,change_instructions\n{prompt_name_csv},Modify the function"

    # Mock FS: CSV, code_dir, and prompt file exist, but derived code file does NOT
    mock_exists, mock_isfile, mock_isdir = create_mock_fs(
        existing_files={csv_file, resolved_prompt_path},
        existing_dirs={code_directory}
    )

    # Mock resolve_prompt_path to return the existing prompt path
    with patch("os.path.exists", mock_exists), \
         patch("os.path.isfile", mock_isfile), \
         patch("os.path.isdir", mock_isdir), \
         patch("builtins.open", mock_open(read_data=csv_content)), \
         patch("pdd.process_csv_change.resolve_prompt_path", return_value=resolved_prompt_path), \
         patch("pdd.process_csv_change.get_extension", return_value=".py"), \
         patch("pdd.process_csv_change.console.print") as mock_print: # Mock print

        # Need to mock reading the prompt file since it "exists"
        m_open = mock_open(read_data="prompt content")
        with patch("builtins.open", m_open):
             # Rerun process_csv_change within the prompt file open mock
             success, list_of_jsons, total_cost, model_name = process_csv_change(
                 csv_file, 0.5, 0.5, code_directory, "python", ".py", 10.0
             )
             # Check that the prompt file was opened among potentially other calls (like the CSV)
             expected_prompt_open_call = call(resolved_prompt_path, 'r', encoding='utf-8')
             assert expected_prompt_open_call in m_open.call_args_list


    assert not success # Failed because row couldn't be processed
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == "N/A" # No successful changes
    # Check for the specific error message
    expected_error = f"[bold red]Error:[/bold red] Derived code file not found or is not a file: '{derived_code_path}' (row 1)"
    mock_print.assert_any_call(expected_error)
    # Check summary output via capsys
    captured = capsys.readouterr()
    assert "Overall Success Status: False" in captured.out

# --- Test Budget Handling ---

def test_budget_exceeded(mock_change_fixture, capsys):
    """
    Test that the function stops processing when the budget is exceeded.
    The row causing the exceedance should NOT be added to results.
    """
    csv_file = "budget_test.csv"
    code_directory = "/path/to/code"
    budget = 2.0

    prompt1_name = "prompt1_python.prompt"
    prompt2_name = "prompt2_python.prompt"
    prompt3_name = "prompt3_python.prompt"
    prompt1_path = os.path.abspath(os.path.join(code_directory, prompt1_name))
    prompt2_path = os.path.abspath(os.path.join(code_directory, prompt2_name))
    prompt3_path = os.path.abspath(os.path.join(code_directory, prompt3_name))
    code1_path = os.path.abspath(os.path.join(code_directory, "prompt1.py"))
    code2_path = os.path.abspath(os.path.join(code_directory, "prompt2.py"))
    code3_path = os.path.abspath(os.path.join(code_directory, "prompt3.py"))

    csv_content = f"prompt_name,change_instructions\n{prompt1_name},Change 1\n{prompt2_name},Change 2\n{prompt3_name},Change 3"

    # Mock FS: All files exist
    mock_exists, mock_isfile, mock_isdir = create_mock_fs(
        existing_files={csv_file, prompt1_path, prompt2_path, prompt3_path, code1_path, code2_path, code3_path},
        existing_dirs={code_directory}
    )

    # Mock change side effect: row 1 costs 1.0, row 2 costs 1.5 (exceeds budget 2.0)
    mock_change_fixture.side_effect = [
        ("modified prompt 1", 1.0, "model_v1"),
        ("modified prompt 2", 1.5, "model_v1"),
        ("modified prompt 3", 1.0, "model_v1") # This should not be called
    ]

    # Mock resolve_prompt_path
    def mock_resolve(p_name, csv_f, code_dir):
        map = {prompt1_name: prompt1_path, prompt2_name: prompt2_path, prompt3_name: prompt3_path}
        return map.get(p_name)

    # Mock file reads
    m_open = mock_open(read_data="file content")

    with patch("os.path.exists", mock_exists), \
         patch("os.path.isfile", mock_isfile), \
         patch("os.path.isdir", mock_isdir), \
         patch("builtins.open", m_open), \
         patch("pdd.process_csv_change.resolve_prompt_path", mock_resolve), \
         patch("pdd.process_csv_change.get_extension", return_value=".py"), \
         patch("pdd.process_csv_change.console.print") as mock_print:

        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, 0.5, 0.5, code_directory, "python", ".py", budget
        )

    assert not success # Failed due to budget
    # Only the first prompt should be in the results
    assert list_of_jsons == [
        {"file_name": prompt1_name, "modified_prompt": "modified prompt 1"}
    ]
    # Total cost includes the cost that exceeded the budget
    assert total_cost == 2.5 # 1.0 + 1.5
    assert model_name == "model_v1" # From the first successful call

    # Check that the budget exceeded warning was printed for row 2
    expected_budget_message = f"[bold yellow]Warning:[/bold yellow] Budget exceeded (£{budget:.2f}) after processing row 2. Change from this row NOT saved. Stopping."
    mock_print.assert_any_call(expected_budget_message)

    # Check that change was called only twice
    assert mock_change_fixture.call_count == 2

    # Check summary output via capsys
    captured = capsys.readouterr()
    assert "Overall Success Status: False" in captured.out
    assert "Successful Changes: 1" in captured.out

# --- Test Successful Scenarios ---

def test_successful_processing(mock_change_fixture, capsys):
    """
    Test that the function processes the CSV successfully within the budget.
    """
    csv_file = "success.csv"
    code_directory = "/path/to/code"
    budget = 5.0

    prompt1_name = "prompt1_python.prompt"
    prompt2_name = "prompt2_python.prompt"
    prompt1_path = os.path.abspath(os.path.join(code_directory, prompt1_name))
    prompt2_path = os.path.abspath(os.path.join(code_directory, prompt2_name))
    code1_path = os.path.abspath(os.path.join(code_directory, "prompt1.py"))
    code2_path = os.path.abspath(os.path.join(code_directory, "prompt2.py"))

    csv_content = f"prompt_name,change_instructions\n{prompt1_name},Change 1\n{prompt2_name},Change 2"

    mock_exists, mock_isfile, mock_isdir = create_mock_fs(
        existing_files={csv_file, prompt1_path, prompt2_path, code1_path, code2_path},
        existing_dirs={code_directory}
    )
    mock_change_fixture.side_effect = [
        ("modified prompt 1", 1.0, "model_v1"),
        ("modified prompt 2", 1.5, "model_v1")
    ]
    def mock_resolve(p_name, csv_f, code_dir):
        map = {prompt1_name: prompt1_path, prompt2_name: prompt2_path}
        return map.get(p_name)
    m_open = mock_open(read_data="file content")

    with patch("os.path.exists", mock_exists), \
         patch("os.path.isfile", mock_isfile), \
         patch("os.path.isdir", mock_isdir), \
         patch("builtins.open", m_open), \
         patch("pdd.process_csv_change.resolve_prompt_path", mock_resolve), \
         patch("pdd.process_csv_change.get_extension", return_value=".py"):

        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, 0.7, 0.3, code_directory, "python", ".py", budget
        )

    assert success # Should be True
    assert list_of_jsons == [
        {"file_name": prompt1_name, "modified_prompt": "modified prompt 1"},
        {"file_name": prompt2_name, "modified_prompt": "modified prompt 2"}
    ]
    assert total_cost == 2.5
    assert model_name == "model_v1"
    captured = capsys.readouterr()
    assert f"Successfully processed change for: {prompt1_name}" in captured.out
    assert f"Successfully processed change for: {prompt2_name}" in captured.out
    assert "CSV processing finished successfully." in captured.out
    assert "Overall Success Status: True" in captured.out
    assert "Total Cost: $2.500000" in captured.out
    assert "Model Used (first success): model_v1" in captured.out
    assert "Successful Changes: 2" in captured.out

def test_model_name_change_warning(mock_change_fixture, capsys):
    """
    Test that the function warns when the model name changes between change function calls,
    but still returns success and the first model name.
    """
    csv_file = "model_change.csv"
    code_directory = "/path/to/code"
    budget = 10.0

    prompt1_name = "prompt1_python.prompt"
    prompt2_name = "prompt2_python.prompt"
    prompt1_path = os.path.abspath(os.path.join(code_directory, prompt1_name))
    prompt2_path = os.path.abspath(os.path.join(code_directory, prompt2_name))
    code1_path = os.path.abspath(os.path.join(code_directory, "prompt1.py"))
    code2_path = os.path.abspath(os.path.join(code_directory, "prompt2.py"))

    csv_content = f"prompt_name,change_instructions\n{prompt1_name},Change 1\n{prompt2_name},Change 2"

    mock_exists, mock_isfile, mock_isdir = create_mock_fs(
        existing_files={csv_file, prompt1_path, prompt2_path, code1_path, code2_path},
        existing_dirs={code_directory}
    )
    mock_change_fixture.side_effect = [
        ("modified prompt 1", 1.0, "model_v1"),
        ("modified prompt 2", 1.5, "model_v2")  # Different model
    ]
    def mock_resolve(p_name, csv_f, code_dir):
        map = {prompt1_name: prompt1_path, prompt2_name: prompt2_path}
        return map.get(p_name)
    m_open = mock_open(read_data="file content")

    with patch("os.path.exists", mock_exists), \
         patch("os.path.isfile", mock_isfile), \
         patch("os.path.isdir", mock_isdir), \
         patch("builtins.open", m_open), \
         patch("pdd.process_csv_change.resolve_prompt_path", mock_resolve), \
         patch("pdd.process_csv_change.get_extension", return_value=".py"):

        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, 0.6, 0.4, code_directory, "python", ".py", budget
        )

    assert success # Still overall success
    assert list_of_jsons == [
        {"file_name": prompt1_name, "modified_prompt": "modified prompt 1"},
        {"file_name": prompt2_name, "modified_prompt": "modified prompt 2"}
    ]
    assert total_cost == 2.5
    assert model_name == "model_v1"  # Should retain the first model
    captured = capsys.readouterr()
    assert "Warning: Model name changed from 'model_v1' to 'model_v2' in row 2." in captured.out
    assert f"Successfully processed change for: {prompt1_name}" in captured.out
    assert f"Successfully processed change for: {prompt2_name}" in captured.out
    assert "Overall Success Status: True" in captured.out

# --- Test Exception Handling ---

def test_change_function_exception(mock_change_fixture, capsys):
    """
    Test that the function handles exceptions raised by the 'change' function gracefully.
    It should process other rows, return success=False, and report partial results.
    """
    csv_file = "change_fail.csv"
    code_directory = "/path/to/code"
    budget = 10.0

    prompt1_name = "prompt1_python.prompt"
    prompt2_name = "prompt2_python.prompt" # This one will cause 'change' to fail
    prompt1_path = os.path.abspath(os.path.join(code_directory, prompt1_name))
    prompt2_path = os.path.abspath(os.path.join(code_directory, prompt2_name))
    code1_path = os.path.abspath(os.path.join(code_directory, "prompt1.py"))
    code2_path = os.path.abspath(os.path.join(code_directory, "prompt2.py"))

    csv_content = f"prompt_name,change_instructions\n{prompt1_name},Change 1\n{prompt2_name},Change 2"

    mock_exists, mock_isfile, mock_isdir = create_mock_fs(
        existing_files={csv_file, prompt1_path, prompt2_path, code1_path, code2_path},
        existing_dirs={code_directory}
    )
    # Mock change: success for row 1, exception for row 2
    change_exception = Exception("Change function failed")
    mock_change_fixture.side_effect = [
        ("modified prompt 1", 1.0, "model_v1"),
        change_exception
    ]
    def mock_resolve(p_name, csv_f, code_dir):
        map = {prompt1_name: prompt1_path, prompt2_name: prompt2_path}
        return map.get(p_name)
    m_open = mock_open(read_data="file content")

    with patch("os.path.exists", mock_exists), \
         patch("os.path.isfile", mock_isfile), \
         patch("os.path.isdir", mock_isdir), \
         patch("builtins.open", m_open), \
         patch("pdd.process_csv_change.resolve_prompt_path", mock_resolve), \
         patch("pdd.process_csv_change.get_extension", return_value=".py"):

        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, 0.5, 0.5, code_directory, "python", ".py", budget
        )

    assert not success # Overall success is False due to the exception
    assert list_of_jsons == [{"file_name": prompt1_name, "modified_prompt": "modified prompt 1"}] # Only row 1 result
    assert total_cost == 1.0 # Only cost from row 1
    assert model_name == "model_v1" # From row 1
    captured = capsys.readouterr()
    # Check for the error message logged for row 2
    assert f"Error: Failed during 'change' call for '{prompt2_name}' (row 2): {change_exception}" in captured.out
    assert f"Successfully processed change for: {prompt1_name}" in captured.out
    assert "Overall Success Status: False" in captured.out

# --- Test Path Resolution Helper ---
# Use tmp_path for more realistic file system interactions

def test_resolve_prompt_path_found_in_code_dir(tmp_path):
    csv_path = tmp_path / "input.csv"
    code_dir = tmp_path / "code"
    code_dir.mkdir()
    prompt_name = "my_prompt.prompt"
    prompt_path_in_code_dir = code_dir / prompt_name
    prompt_path_in_code_dir.touch() # Create the file

    csv_path.touch() # Create dummy csv

    resolved = resolve_prompt_path(prompt_name, str(csv_path), str(code_dir))
    assert resolved == str(prompt_path_in_code_dir)

def test_resolve_prompt_path_found_relative_to_csv(tmp_path):
    csv_dir = tmp_path / "csv_files"
    csv_dir.mkdir()
    csv_path = csv_dir / "input.csv"
    code_dir = tmp_path / "code" # Doesn't need to exist for this test case
    prompt_name = "my_prompt.prompt"
    prompt_path_rel_to_csv = csv_dir / prompt_name
    prompt_path_rel_to_csv.touch()

    csv_path.touch()

    resolved = resolve_prompt_path(prompt_name, str(csv_path), str(code_dir))
    assert resolved == str(prompt_path_rel_to_csv)

def test_resolve_prompt_path_found_absolute(tmp_path):
    csv_path = tmp_path / "input.csv"
    code_dir = tmp_path / "code"
    prompt_dir = tmp_path / "prompts"
    prompt_dir.mkdir()
    prompt_name = "my_prompt.prompt"
    absolute_prompt_path = prompt_dir / prompt_name
    absolute_prompt_path.touch()

    csv_path.touch()

    # Pass the absolute path in prompt_name
    resolved = resolve_prompt_path(str(absolute_prompt_path), str(csv_path), str(code_dir))
    assert resolved == str(absolute_prompt_path)

def test_resolve_prompt_path_found_in_cwd(tmp_path, monkeypatch):
    # Change CWD for the test
    original_cwd = os.getcwd()
    monkeypatch.chdir(tmp_path)

    csv_path = tmp_path / "input.csv" # In new CWD
    code_dir = tmp_path / "code"      # In new CWD
    prompt_name = "my_prompt.prompt"
    prompt_path_in_cwd = tmp_path / prompt_name
    prompt_path_in_cwd.touch()

    csv_path.touch()

    resolved = resolve_prompt_path(prompt_name, str(csv_path), str(code_dir))
    assert resolved == str(prompt_path_in_cwd)

    # Restore CWD
    monkeypatch.chdir(original_cwd)


def test_resolve_prompt_path_not_found(tmp_path):
    csv_path = tmp_path / "input.csv"
    code_dir = tmp_path / "code"
    code_dir.mkdir()
    csv_path.touch()
    prompt_name = "non_existent.prompt"

    resolved = resolve_prompt_path(prompt_name, str(csv_path), str(code_dir))
    assert resolved is None

# --- Test Integration with Real Files (using tmp_path) ---

def test_correct_prompt_path_resolution_integration(mock_change_fixture, tmp_path, capsys):
    """
    Test that prompt_path is correctly resolved using code_directory
    and the rest of the processing works with real files via tmp_path.
    """
    # Arrange
    code_dir = tmp_path / "code_files"
    code_dir.mkdir()

    # Create dummy prompt and code files inside code_dir
    # Use a name that requires language inference
    prompt_filename_base = "my_prompt"
    prompt_filename = f"{prompt_filename_base}_python.prompt"
    code_filename = f"{prompt_filename_base}.py" # Derived name
    prompt_file_path = code_dir / prompt_filename
    code_file_path = code_dir / code_filename

    prompt_file_path.write_text("Original prompt content")
    code_file_path.write_text("def my_func(): pass")

    # Create CSV file mentioning only the prompt filename (basename)
    csv_filename = tmp_path / "changes.csv"
    # Use just the basename in the CSV, relying on resolve_prompt_path
    csv_content = f"prompt_name,change_instructions\n{prompt_filename},Do the change\n"
    csv_filename.write_text(csv_content)

    # Mock the change function
    mock_change_fixture.return_value = ("Modified prompt", 0.01, "test_model")
    # Mock get_extension as it's an internal import
    with patch("pdd.process_csv_change.get_extension", return_value=".py"):

        # Act
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file=str(csv_filename),
            strength=0.5,
            temperature=0.5,
            code_directory=str(code_dir),
            language="javascript", # Default language (should be overridden by filename)
            extension=".js",     # Default extension
            budget=1.0
        )

    # Assert
    assert success, "Processing should succeed when paths are resolved correctly."
    assert len(list_of_jsons) == 1, "One row should have been processed."
    # Check that the original name from the CSV is used as the key
    assert list_of_jsons[0]["file_name"] == prompt_filename
    assert list_of_jsons[0]["modified_prompt"] == "Modified prompt"
    assert total_cost == 0.01
    assert model_name == "test_model"

    # Check that no warnings/errors about missing files were printed
    captured = capsys.readouterr()
    print(captured.out) # Print output for debugging if needed
    assert f"Prompt file for '{prompt_filename}' not found" not in captured.out
    assert f"Derived code file not found or is not a file: '{code_file_path}'" not in captured.out
    # Check for the correct success message
    assert f"Successfully processed change for: {prompt_filename}" in captured.out
    # Check that language was inferred correctly
    assert "Inferred language from filename: Python" in captured.out
    assert "Overall Success Status: True" in captured.out