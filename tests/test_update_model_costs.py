# Detailed Test Plan for update_model_costs.py

# The script update_model_costs.py is designed to read a CSV file containing LLM model
# information, update missing input/output token costs and structured output support
# flags using the LiteLLM library, and save the changes back to the CSV.

# Test Approach: Unit Tests using pytest, mocking external dependencies (pandas, litellm, os, sys).
# Z3 formal verification is not suitable for this script due to its heavy reliance on
# external libraries, file I/O, and network interactions (simulated via mocking).

# Test Setup:
# - Use pytest fixtures for temporary directories and files.
# - Use pytest-mock to mock:
#   - pandas.read_csv to control the input DataFrame for various scenarios.
#   - pandas.DataFrame.to_csv to verify saving behavior and output data.
#   - litellm.model_cost to simulate LiteLLM's cost data dictionary.
#   - litellm.supports_response_schema to simulate the structured output check result.
#   - os.makedirs for directory creation tests.
#   - sys.argv for testing command-line argument parsing in the main function.
# - Capture stdout/stderr using pytest's capsys or capfd fixture to verify Rich output messages.

# Test Cases:

# 1. File Handling:
#    - test_file_not_found: Script handles non-existent CSV path gracefully.
#    - test_file_read_error: Script handles generic errors during CSV reading.
#    - test_directory_creation: Script creates parent directory if it doesn't exist for a custom path.
#    - test_directory_creation_permission_error: Script handles permission errors during directory creation.
#    - test_file_write_error: Script handles errors when saving the updated CSV.

# 2. CSV Loading and Schema Handling:
#    - test_load_empty_csv: Script loads an empty CSV (headers only) and adds missing columns with NA.
#    - test_load_csv_missing_columns: Script loads a CSV missing some expected columns and adds them with NA.
#    - test_load_csv_with_placeholders: Script correctly identifies -1 placeholders in cost columns as missing.
#    - test_load_csv_with_existing_data: Script does not overwrite existing valid cost/structured_output data.
#    - test_load_csv_with_invalid_cost_data: Script handles non-numeric data in cost columns (coerces to NA).
#    - test_load_csv_with_invalid_structured_output_data: Script handles non-boolean/non-NA data in structured_output (coerces to NA).

# 3. LiteLLM Interaction (Mocked):
#    - test_update_missing_costs: Script fetches and updates missing input/output costs from mocked litellm.model_cost. Verifies $/Million conversion.
#    - test_update_missing_structured_output: Script fetches and updates missing structured_output flag from mocked litellm.supports_response_schema.
#    - test_update_both_missing: Script updates both costs and structured output when both are missing.
#    - test_litellm_cost_fetch_failure: Script handles exceptions when fetching litellm.model_cost (e.g., network error). Costs are not updated, warning printed.
#    - test_litellm_cost_model_not_found: Script handles case where model is not in mocked litellm.model_cost data. Costs not updated, warning printed.
#    - test_litellm_cost_missing_keys: Script handles case where model cost data is missing 'input_cost_per_token' or 'output_cost_per_token'. Updates only available costs, warning printed.
#    - test_litellm_structured_output_check_failure: Script handles exceptions (e.g., ValueError, generic Exception) from litellm.supports_response_schema. structured_output not updated (remains NA), warning/error printed.
#    - test_csv_with_unknown_model_for_litellm: Script handles models present in CSV but unknown to LiteLLM for checks (simulated via mock return values/exceptions).

# 4. Mixed Scenarios:
#    - test_csv_mix_of_missing_and_present_data: Script correctly updates only the necessary fields in a CSV with mixed data states.
#    - test_csv_with_missing_model_identifier: Script skips rows with missing/NA model identifiers and prints a warning.

# 5. Output and Saving:
#    - test_output_messages: Script prints expected messages (loading, processing, updates, warnings, errors, saving) using Rich.
#    - test_save_no_updates: Script does not save the file if no data updates were made to the DataFrame.
#    - test_save_with_updates: Script saves the file with index=False and na_rep='' when updates occur.

# 6. Main Function / Argument Parsing:
#    - test_main_default_path: main function uses the default CSV path when no argument is provided.
#    - test_main_custom_path: main function uses the provided --csv-path argument.

# Note: The 'max_reasoning_tokens' column is explicitly stated as manually maintained and not updated by the script. Tests should ensure it is present if expected, but not verify automated updates for it.

import pytest
import pandas as pd
import os
import io
from unittest.mock import patch, MagicMock, call
from pathlib import Path # Import Path

# Need to adjust import based on package structure
# Assuming the code is in pdd/update_model_costs.py and tests are in tests/
import sys
# Add the parent directory of 'pdd' to sys.path
# This is a common pattern in pytest for testing packages
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from pdd.update_model_costs import update_model_data, main, EXPECTED_COLUMNS # Removed MISSING_VALUE_PLACEHOLDER as it's unused

# Fixture for creating a temporary CSV file
@pytest.fixture
def temp_csv_path(tmp_path):
    """Provides a path for a temporary CSV file."""
    return tmp_path / "llm_model.csv"

# Fixture to capture Rich console output
@pytest.fixture
def capsys_rich(capsys):
    """Captures stdout and stderr, including Rich output."""
    return capsys

# Helper function to create a basic DataFrame matching expected columns
def create_base_df(data=None, columns=None):
    """Creates a pandas DataFrame, ensuring EXPECTED_COLUMNS are present if columns=None."""
    if data is None:
        data = []
    if columns is None:
        columns_to_use = EXPECTED_COLUMNS
    else:
        columns_to_use = columns

    # Create DataFrame with specified or default columns
    df = pd.DataFrame(data, columns=columns_to_use)

    # Ensure all expected columns are present if default columns were used initially
    if columns is None:
        for col in EXPECTED_COLUMNS:
            if col not in df.columns:
                df[col] = pd.NA # Use pandas NA as default missing
        # Reorder columns to match EXPECTED_COLUMNS
        df = df[EXPECTED_COLUMNS]

    # Apply initial type conversions similar to the script's loading phase
    # (before explicit enforcement) - helps simulate read_csv behavior
    if 'input' in df.columns:
        df['input'] = pd.to_numeric(df['input'], errors='coerce')
    if 'output' in df.columns:
        df['output'] = pd.to_numeric(df['output'], errors='coerce')
    # structured_output is often read as object initially, script handles conversion later
    if 'structured_output' in df.columns:
         df['structured_output'] = df['structured_output'].astype('object')
    # Integer columns are read as float if NA exists, script handles conversion later
    for col in ['coding_arena_elo', 'max_reasoning_tokens']:
         if col in df.columns:
             df[col] = pd.to_numeric(df[col], errors='coerce') # Read as float initially if NAs

    return df


# --- Test Cases ---

# 1. File Handling
def test_file_not_found(mocker, capsys_rich):
    mocker.patch("pandas.read_csv", side_effect=FileNotFoundError)
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data("non_existent_path/llm_model.csv")

    mock_console.print.assert_any_call("[bold red]Error:[/bold red] CSV file not found at non_existent_path/llm_model.csv")

def test_file_read_error(mocker, capsys_rich):
    mocker.patch("pandas.read_csv", side_effect=Exception("Permission denied"))
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data("path/to/file.csv")

    mock_console.print.assert_any_call("[bold red]Error:[/bold red] Failed to load CSV file: Permission denied")

def test_directory_creation(mocker, tmp_path, capsys_rich):
    # Test main function as it handles directory creation
    # Mock read_csv to simulate file not found initially, then succeed after dir creation
    # This requires more complex mocking or focusing the test on update_model_data
    # Let's test main's directory creation logic directly
    mock_read_csv = mocker.patch("pdd.update_model_costs.pd.read_csv", return_value=create_base_df()) # Assume read succeeds after dir creation
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_litellm_cost = mocker.patch("litellm.model_cost", {})
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", return_value=False)
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_makedirs = mocker.patch("os.makedirs") # Mock makedirs

    non_existent_dir = tmp_path / "new_dir"
    csv_path = non_existent_dir / "llm_model.csv"
    resolved_csv_path = csv_path.resolve() # main uses resolve()

    # Mock path checks within main
    mocker.patch("pathlib.Path.is_file", return_value=False) # Assume no user file, no existing default file
    mocker.patch("pathlib.Path.exists", return_value=False) # Assume directory doesn't exist

    # Mock sys.argv to simulate command line argument
    mocker.patch('sys.argv', ['update_model_costs.py', '--csv-path', str(csv_path)])

    main()

    # Check if directory creation was attempted with the correct path
    mock_makedirs.assert_called_once_with(resolved_csv_path.parent, exist_ok=True)
    mock_console.print.assert_any_call(f"[cyan]Created directory:[/cyan] {resolved_csv_path.parent}")
    # Check if update_model_data was called with the resolved path
    # We mocked update_model_data itself, so we can't check read_csv/to_csv calls within it here.
    # Instead, let's test update_model_data's save behavior separately.

    # Test that update_model_data doesn't save if no updates
    mock_to_csv.reset_mock() # Reset mock before calling update_model_data directly
    update_model_data(str(resolved_csv_path))
    mock_read_csv.assert_called_with(str(resolved_csv_path)) # Check read_csv call
    mock_to_csv.assert_not_called() # Should NOT save if no schema/data updates
    mock_console.print.assert_any_call("\n[bold blue]No schema changes or data updates needed. CSV file not saved.[/bold blue]")


def test_directory_creation_permission_error(mocker, tmp_path, capsys_rich):
    # Test main function's handling of makedirs error
    mock_update_model_data = mocker.patch("pdd.update_model_costs.update_model_data") # Don't run update if dir fails
    mock_makedirs = mocker.patch("os.makedirs", side_effect=OSError("Permission denied"))
    mock_console = mocker.patch("pdd.update_model_costs.console")

    non_existent_dir = tmp_path / "new_dir"
    csv_path = non_existent_dir / "llm_model.csv"
    resolved_csv_path = csv_path.resolve()

    # Mock path checks
    mocker.patch("pathlib.Path.is_file", return_value=False)
    mocker.patch("pathlib.Path.exists", return_value=False) # Dir doesn't exist

    mocker.patch('sys.argv', ['update_model_costs.py', '--csv-path', str(csv_path)])

    main()

    # Check makedirs was called and error was printed
    mock_makedirs.assert_called_once_with(resolved_csv_path.parent, exist_ok=True)
    mock_console.print.assert_any_call(f"[bold red]Error:[/bold red] Could not create directory {resolved_csv_path.parent}: Permission denied")
    mock_update_model_data.assert_not_called() # Should exit before calling update

def test_file_write_error(mocker, temp_csv_path, capsys_rich):
    # Create a dummy CSV file that will trigger an update
    initial_csv_content = "provider,model,input,output\nOpenAI,gpt-test,,"
    temp_csv_path.write_text(initial_csv_content)

    # Simulate reading this CSV (it's missing columns)
    mock_df_initial = pd.read_csv(io.StringIO(initial_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df_initial)

    # Mock LiteLLM to provide data so an update is attempted
    mock_litellm_cost = mocker.patch("litellm.model_cost", {'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002}})
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", return_value=True)

    # Mock to_csv to raise error
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", side_effect=Exception("Disk full"))
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check save was attempted and error was printed
    mock_to_csv.assert_called_once_with(str(temp_csv_path), index=False, na_rep='')
    mock_console.print.assert_any_call(f"[bold red]Error:[/bold red] Failed to save updated CSV file: Disk full")


# 2. CSV Loading and Schema Handling
def test_load_csv_missing_columns(mocker, temp_csv_path, capsys_rich):
    # Test the scenario where the *initial* CSV is missing columns.
    initial_csv_missing_cols = "provider,model,input,output\nOpenAI,gpt-test,1.0,2.0\n" # Missing many columns
    temp_csv_path.write_text(initial_csv_missing_cols)
    mock_df_initial = pd.read_csv(io.StringIO(initial_csv_missing_cols))

    mocker.patch("pandas.read_csv", return_value=mock_df_initial)
    # Mock litellm calls to avoid errors, assume no data updates needed beyond schema
    mocker.patch("litellm.model_cost", {})
    mocker.patch("litellm.supports_response_schema", return_value=False)
    mock_df_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check that warnings were printed for missing columns
    mock_console.print.assert_any_call("[yellow]Warning:[/yellow] Column 'coding_arena_elo' missing. Adding it.")
    mock_console.print.assert_any_call("[yellow]Warning:[/yellow] Column 'base_url' missing. Adding it.")
    # ... check others if needed ...
    mock_console.print.assert_any_call("[yellow]Warning:[/yellow] Column 'structured_output' missing. Adding it.")
    mock_console.print.assert_any_call("[cyan]CSV schema updated with missing columns.[/cyan]")

    # Check if to_csv was called (because schema was updated)
    mock_df_to_csv.assert_called_once()
    # Check if the DataFrame passed to to_csv has all expected columns
    called_df = mock_df_to_csv.call_args.args[0] # Access DataFrame instance
    assert isinstance(called_df, pd.DataFrame)
    assert all(col in called_df.columns for col in EXPECTED_COLUMNS)
    # Check if columns are in the correct order
    assert list(called_df.columns) == EXPECTED_COLUMNS


def test_load_csv_with_placeholders_as_na(mocker, temp_csv_path, capsys_rich):
    # Test that empty strings or explicit NA markers are treated as missing
    # Note: The code now uses pd.isna(), not MISSING_VALUE_PLACEHOLDER = -1.0
    initial_csv_content = "provider,model,input,output,structured_output\nOpenAI,gpt-test,,,False\nAnthropic,claude-test,1.0,2.0,\nGoogle,gemini-test,NA,NA,NA"
    temp_csv_path.write_text(initial_csv_content)

    # Simulate read_csv behavior (reads empty strings as '', NA as nan/None)
    # Use create_base_df to mimic initial load state more accurately
    mock_df = create_base_df([
        {'provider': 'OpenAI', 'model': 'gpt-test', 'input': pd.NA, 'output': pd.NA, 'structured_output': 'False'},
        {'provider': 'Anthropic', 'model': 'claude-test', 'input': 1.0, 'output': 2.0, 'structured_output': pd.NA},
        {'provider': 'Google', 'model': 'gemini-test', 'input': pd.NA, 'output': pd.NA, 'structured_output': pd.NA},
    ])
    mocker.patch("pandas.read_csv", return_value=mock_df.copy()) # Pass a copy

    # Mock LiteLLM to provide data
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'claude-test': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004}, # Costs exist in CSV, won't update
        'gemini-test': {'input_cost_per_token': 0.000005, 'output_cost_per_token': 0.000006},
    })
    # Mock supports_response_schema: gpt=False(already), claude=True(missing), gemini=True(missing)
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=lambda model: model in ['claude-test', 'gemini-test'])

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)

    # gpt-test: costs updated from NA, struct remains False
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert gpt_row['output'] == 2.0
    assert gpt_row['structured_output'] is False # Was False, remains False

    # claude-test: costs remain, struct updated from NA to True
    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['input'] == 1.0
    assert claude_row['output'] == 2.0
    assert claude_row['structured_output'] is True # Updated from NA

    # gemini-test: costs updated from NA, struct updated from NA to True
    gemini_row = called_df[called_df['model'] == 'gemini-test'].iloc[0]
    assert gemini_row['input'] == 5.0
    assert gemini_row['output'] == 6.0
    assert gemini_row['structured_output'] is True # Updated from NA

    # Check console output for updates
    mock_console.print.assert_any_call("[green]Updated (Input: 1.0000, Output: 2.0000)[/green]") # gpt costs
    mock_console.print.assert_any_call("[green]Updated (True)[/green]") # claude struct
    mock_console.print.assert_any_call("[green]Updated (Input: 5.0000, Output: 6.0000)[/green]") # gemini costs
    mock_console.print.assert_any_call("[green]Updated (True)[/green]") # gemini struct


def test_load_csv_with_existing_data(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output,structured_output\nOpenAI,gpt-test,0.5,0.7,True\nAnthropic,claude-test,1.0,2.0,False"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = create_base_df(pd.read_csv(io.StringIO(initial_csv_content)).to_dict('records'))
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())

    # Mock LiteLLM to provide different data
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002}, # 1.0, 2.0 -> Mismatch
        'claude-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002} # 1.0, 2.0 -> Match
    })
    # Mock supports_response_schema: gpt=False (mismatch), claude=True (mismatch)
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=lambda model: model == 'claude-test')

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_to_csv.reset_mock() # Ensure mock is clean before call

    update_model_data(str(temp_csv_path))

    # Check that to_csv was NOT called (no schema update, no data update despite mismatch)
    mock_to_csv.assert_not_called()
    mock_console.print.assert_any_call("\n[bold blue]No schema changes or data updates needed. CSV file not saved.[/bold blue]")

    # Check console output for mismatch reporting
    mock_console.print.assert_any_call("[bold red]Mismatch! (Input (CSV: 0.5000, LLM: 1.0000), Output (CSV: 0.7000, LLM: 2.0000))[/bold red]") # gpt-test cost mismatch
    mock_console.print.assert_any_call("[green]Match (Input, Output)[/green]") # claude-test cost match
    # Note: Structured output isn't compared, only updated if missing. Here it exists.
    mock_console.print.assert_any_call("Checked (Exists)") # For structured output


def test_load_csv_with_invalid_cost_data(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output\nOpenAI,gpt-test,abc,1.0\nAnthropic,claude-test,2.0,xyz"
    temp_csv_path.write_text(initial_csv_content)

    # Simulate read_csv reading invalid data
    mock_df_read = pd.read_csv(io.StringIO(initial_csv_content))
    # create_base_df will coerce 'abc'/'xyz' to NaN during its initial numeric conversion
    mock_df = create_base_df(mock_df_read.to_dict('records'))
    assert pd.isna(mock_df.loc[0, 'input']) # Verify initial coercion
    assert pd.isna(mock_df.loc[1, 'output']) # Verify initial coercion
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())

    # Mock LiteLLM to provide data
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002}, # Provide 1.0, 2.0
        'claude-test': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004} # Provide 3.0, 4.0
    })
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", return_value=False)

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)

    # Invalid data coerced to NA, then updated by LiteLLM
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0 # Updated from NA
    assert gpt_row['output'] == 1.0 # Was valid 1.0, not updated (LiteLLM provided 2.0 - mismatch reported)

    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['input'] == 2.0 # Was valid 2.0, not updated (LiteLLM provided 3.0 - mismatch reported)
    assert claude_row['output'] == 4.0 # Updated from NA

    # Check console output
    mock_console.print.assert_any_call("[green]Updated (Input: 1.0000)[/green]") # gpt input updated
    mock_console.print.assert_any_call("[bold red]Mismatch! (Output (CSV: 1.0000, LLM: 2.0000))[/bold red]") # gpt output mismatch
    mock_console.print.assert_any_call("[bold red]Mismatch! (Input (CSV: 2.0000, LLM: 3.0000))[/bold red]") # claude input mismatch
    mock_console.print.assert_any_call("[green]Updated (Output: 4.0000)[/green]") # claude output updated


def test_load_csv_with_invalid_structured_output_data(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,structured_output\nOpenAI,gpt-test,yes\nAnthropic,claude-test,no\nGoogle,gemini-test,maybe"
    temp_csv_path.write_text(initial_csv_content)

    # Simulate read_csv reading invalid data
    mock_df_read = pd.read_csv(io.StringIO(initial_csv_content))
    # create_base_df doesn't do the bool conversion, the script does
    mocker.patch("pandas.read_csv", return_value=mock_df_read.copy())

    # Mock LiteLLM structured output support
    mocker.patch("litellm.model_cost", {}) # No costs needed
    # Mock supports_response_schema: gpt=False, claude=True, gemini=False (unknown)
    def supports_schema_side_effect(model):
        if model == 'claude-test': return True
        if model == 'gemini-test': raise ValueError("Unknown model") # Simulate unknown
        return False # Default for gpt-test
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=supports_schema_side_effect)

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)

    # Invalid data ('yes', 'no', 'maybe') coerced to NA by script's apply function
    # Then updated by LiteLLM if possible
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['structured_output'] is False # Updated from NA to False (mock return)

    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['structured_output'] is True # Updated from NA to True (mock return)

    gemini_row = called_df[called_df['model'] == 'gemini-test'].iloc[0]
    assert pd.isna(gemini_row['structured_output']) # Remains NA as validation failed

    # Check console output
    mock_console.print.assert_any_call("[green]Updated (False)[/green]") # gpt struct updated
    mock_console.print.assert_any_call("[green]Updated (True)[/green]") # claude struct updated
    mock_console.print.assert_any_call("[red]Validation Failed: Unknown model[/red]") # gemini validation


# 3. LiteLLM Interaction (Mocked)
def test_update_missing_costs(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output\nOpenAI,gpt-test,,\nAnthropic,claude-test,," # Use empty strings for missing
    temp_csv_path.write_text(initial_csv_content)

    mock_df = create_base_df(pd.read_csv(io.StringIO(initial_csv_content)).to_dict('records'))
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())

    # Mock LiteLLM cost data
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'claude-test': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004}
    })
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", return_value=False) # Not testing struct output here

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)

    # gpt-test should have both costs updated from NA
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert gpt_row['output'] == 2.0

    # claude-test should have both costs updated from NA
    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['input'] == 3.0
    assert claude_row['output'] == 4.0

    mock_console.print.assert_any_call("[green]Updated (Input: 1.0000, Output: 2.0000)[/green]")
    mock_console.print.assert_any_call("[green]Updated (Input: 3.0000, Output: 4.0000)[/green]")


def test_update_missing_structured_output(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,structured_output\nOpenAI,gpt-test,\nAnthropic,claude-test,False\nGoogle,gemini-test,"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = create_base_df(pd.read_csv(io.StringIO(initial_csv_content)).to_dict('records'))
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())

    # Mock LiteLLM structured output support
    mocker.patch("litellm.model_cost", {}) # Not testing costs here
    # Mock supports_response_schema: gpt=True (missing), claude=False(exists), gemini=unknown
    def supports_schema_side_effect(model):
        if model == 'gpt-test': return True
        if model == 'claude-test': return False # Doesn't matter, value exists
        if model == 'gemini-test': raise ValueError("Unknown model")
        return False # Default
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=supports_schema_side_effect)

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)

    # gpt-test should be updated to True
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['structured_output'] is True

    # claude-test should remain False (was already set)
    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['structured_output'] is False

    # gemini-test should remain NA (missing and validation failed)
    gemini_row = called_df[called_df['model'] == 'gemini-test'].iloc[0]
    assert pd.isna(gemini_row['structured_output'])

    mock_console.print.assert_any_call("[green]Updated (True)[/green]") # gpt-test
    mock_console.print.assert_any_call("Checked (Exists)") # claude-test
    mock_console.print.assert_any_call("[red]Validation Failed: Unknown model[/red]") # gemini-test


def test_update_both_missing(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output,structured_output\nOpenAI,gpt-test,,,,\nAnthropic,claude-test,1.0,2.0,"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = create_base_df(pd.read_csv(io.StringIO(initial_csv_content)).to_dict('records'))
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())

    # Mock LiteLLM
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'claude-test': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004} # Mismatch
    })
    # Mock supports_response_schema: gpt=True (missing), claude=False (missing)
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=lambda model: model == 'gpt-test')

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)

    # gpt-test should have costs and structured_output updated
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert gpt_row['output'] == 2.0
    assert gpt_row['structured_output'] is True

    # claude-test should have costs remain (mismatch reported), structured_output updated to False
    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['input'] == 1.0 # Original value
    assert claude_row['output'] == 2.0 # Original value
    assert claude_row['structured_output'] is False # Updated from NA

    # Check console output
    mock_console.print.assert_any_call("[green]Updated (Input: 1.0000, Output: 2.0000)[/green]") # gpt cost
    mock_console.print.assert_any_call("[green]Updated (True)[/green]") # gpt struct
    mock_console.print.assert_any_call("[bold red]Mismatch! (Input (CSV: 1.0000, LLM: 3.0000), Output (CSV: 2.0000, LLM: 4.0000))[/bold red]") # claude cost mismatch
    mock_console.print.assert_any_call("[green]Updated (False)[/green]") # claude struct


def test_litellm_cost_fetch_failure(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output\nOpenAI,gpt-test,,"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = create_base_df(pd.read_csv(io.StringIO(initial_csv_content)).to_dict('records'))
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())

    # Mock LiteLLM cost fetch to raise an exception when accessed
    mock_litellm = mocker.patch("pdd.update_model_costs.litellm")
    mock_litellm.model_cost = property(fget=MagicMock(side_effect=Exception("Network Error"))) # Mock property access
    # Mock supports_response_schema separately
    mock_litellm.supports_response_schema.return_value = False

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_to_csv.reset_mock() # Ensure clean mock

    update_model_data(str(temp_csv_path))

    # Check console output for error
    mock_console.print.assert_any_call(f"[bold red]Error:[/bold red] Could not fetch LiteLLM model cost data: Network Error")
    # Check that processing continued but reported errors/skipped steps
    mock_console.print.assert_any_call("[yellow]Cost data not found in LiteLLM[/yellow]") # Because all_model_costs is {}
    mock_console.print.assert_any_call("[red]Fail (Cost Error)[/red]") # Row status due to fetch error

    # Check that save was NOT called (no updates possible)
    mock_to_csv.assert_not_called()
    mock_console.print.assert_any_call("\n[bold blue]No schema changes or data updates needed. CSV file not saved.[/bold blue]")

    # Optional: Check DataFrame state if needed (it shouldn't have changed)
    # df_state = mock_df # The original df state after read_csv mock


def test_litellm_cost_model_not_found(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output\nOpenAI,gpt-test,,"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = create_base_df(pd.read_csv(io.StringIO(initial_csv_content)).to_dict('records'))
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())

    # Mock LiteLLM cost data, but exclude 'gpt-test'
    mock_litellm_cost = mocker.patch("litellm.model_cost", {'other-model': {'input_cost_per_token': 0.1, 'output_cost_per_token': 0.2}})
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", return_value=False) # Assume valid model for schema check

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_to_csv.reset_mock() # Ensure clean mock

    update_model_data(str(temp_csv_path))

    # Check console output
    mock_console.print.assert_any_call("[yellow]Cost data not found in LiteLLM[/yellow]")
    mock_console.print.assert_any_call("[yellow]Info (No Cost Data)[/yellow]") # Row status

    # Check that save was NOT called (no updates made)
    mock_to_csv.assert_not_called()
    mock_console.print.assert_any_call("\n[bold blue]No schema changes or data updates needed. CSV file not saved.[/bold blue]")


def test_litellm_cost_missing_keys(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output\nOpenAI,gpt-test,,\nAnthropic,claude-test,,"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = create_base_df(pd.read_csv(io.StringIO(initial_csv_content)).to_dict('records'))
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())

    # Mock LiteLLM cost data with missing keys for different models
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001}, # Missing output
        'claude-test': {'output_cost_per_token': 0.000004} # Missing input
    })
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", return_value=False)

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)

    # gpt-test should have input updated, output remain NA
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert pd.isna(gpt_row['output'])

    # claude-test should have output updated, input remain NA
    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert pd.isna(claude_row['input'])
    assert claude_row['output'] == 4.0

    # Check console output
    mock_console.print.assert_any_call("[green]Updated (Input: 1.0000)[/green]")
    mock_console.print.assert_any_call("[green]Updated (Output: 4.0000)[/green]")


def test_litellm_structured_output_check_failure(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,structured_output\nOpenAI,gpt-test,\nAnthropic,claude-test,"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = create_base_df(pd.read_csv(io.StringIO(initial_csv_content)).to_dict('records'))
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())

    mocker.patch("litellm.model_cost", {})
    # Mock LiteLLM structured output check to raise an exception for models
    def supports_schema_side_effect(model):
        if model == 'gpt-test':
            raise ValueError("Unknown model for schema check")
        elif model == 'claude-test':
             raise Exception("API error")
        return False # Default for others
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=supports_schema_side_effect)

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_to_csv.reset_mock() # Ensure clean mock

    update_model_data(str(temp_csv_path))

    # Check console output for validation errors
    mock_console.print.assert_any_call("[red]Validation Failed: Unknown model for schema check[/red]")
    mock_console.print.assert_any_call("[red]Check Error: API error[/red]")
    mock_console.print.assert_any_call("[red]Fail (Invalid/Unknown Model?)[/red]") # Row status for gpt-test
    mock_console.print.assert_any_call("[red]Fail (Schema Check Error)[/red]") # Row status for claude-test

    # Check that save was NOT called (no updates made)
    mock_to_csv.assert_not_called()
    mock_console.print.assert_any_call("\n[bold blue]No schema changes or data updates needed. CSV file not saved.[/bold blue]")


# 4. Mixed Scenarios
def test_csv_mix_of_missing_and_present_data(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = """provider,model,input,output,structured_output
OpenAI,gpt-needs-all,,,
Anthropic,claude-needs-cost,,1.0,True
Google,gemini-needs-struct,2.0,3.0,
Mistral,mistral-complete,4.0,5.0,False
Unknown,unknown-model,,,
"""
    temp_csv_path.write_text(initial_csv_content)

    mock_df = create_base_df(pd.read_csv(io.StringIO(initial_csv_content)).to_dict('records'))
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())

    # Mock LiteLLM
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-needs-all': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'claude-needs-cost': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004}, # Output mismatch
        'gemini-needs-struct': {'input_cost_per_token': 0.000002, 'output_cost_per_token': 0.000003}, # Match
        'mistral-complete': {'input_cost_per_token': 0.000004, 'output_cost_per_token': 0.000005}, # Match
    })
    def supports_schema_side_effect(model):
        if model == 'gpt-needs-all': return True # Missing -> Update
        if model == 'claude-needs-cost': return False # Exists (True) -> No Update
        if model == 'gemini-needs-struct': return True # Missing -> Update
        if model == 'mistral-complete': return False # Exists (False) -> No Update
        if model == 'unknown-model': raise ValueError("Unknown model") # Validation fail
        return False # Default

    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=supports_schema_side_effect)

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)

    # gpt-needs-all: costs and struct updated
    gpt_row = called_df[called_df['model'] == 'gpt-needs-all'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert gpt_row['output'] == 2.0
    assert gpt_row['structured_output'] is True

    # claude-needs-cost: input cost updated, output mismatch, struct remains
    claude_row = called_df[called_df['model'] == 'claude-needs-cost'].iloc[0]
    assert claude_row['input'] == 3.0 # Updated from NA
    assert claude_row['output'] == 1.0 # Original value (mismatch reported)
    assert claude_row['structured_output'] is True # Original value

    # gemini-needs-struct: costs remain (match), structured_output updated
    gemini_row = called_df[called_df['model'] == 'gemini-needs-struct'].iloc[0]
    assert gemini_row['input'] == 2.0 # Original value
    assert gemini_row['output'] == 3.0 # Original value
    assert gemini_row['structured_output'] is True # Updated from NA

    # mistral-complete: nothing updated (costs match, struct exists)
    mistral_row = called_df[called_df['model'] == 'mistral-complete'].iloc[0]
    assert mistral_row['input'] == 4.0
    assert mistral_row['output'] == 5.0
    assert mistral_row['structured_output'] is False

    # unknown-model: nothing updated, validation failed
    unknown_row = called_df[called_df['model'] == 'unknown-model'].iloc[0]
    assert pd.isna(unknown_row['input'])
    assert pd.isna(unknown_row['output'])
    assert pd.isna(unknown_row['structured_output'])

    # Check console output for updates and warnings
    mock_console.print.assert_any_call("[green]Updated (Input: 1.0000, Output: 2.0000)[/green]") # gpt cost
    mock_console.print.assert_any_call("[green]Updated (True)[/green]") # gpt struct
    mock_console.print.assert_any_call("[green]Updated (Input: 3.0000)[/green]") # claude input cost
    mock_console.print.assert_any_call("[bold red]Mismatch! (Output (CSV: 1.0000, LLM: 4.0000))[/bold red]") # claude output cost mismatch
    mock_console.print.assert_any_call("Checked (Exists)") # claude struct
    mock_console.print.assert_any_call("[green]Match (Input, Output)[/green]") # gemini costs
    mock_console.print.assert_any_call("[green]Updated (True)[/green]") # gemini struct
    mock_console.print.assert_any_call("[green]Match (Input, Output)[/green]") # mistral costs
    mock_console.print.assert_any_call("Checked (Exists)") # mistral struct
    mock_console.print.assert_any_call("[red]Validation Failed: Unknown model[/red]") # unknown-model validation


def test_csv_with_missing_model_identifier(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = """provider,model,input,output,structured_output
OpenAI,gpt-test,,,
Anthropic,,1.0,2.0,True
Google,gemini-test,3.0,4.0,
"""
    temp_csv_path.write_text(initial_csv_content)

    mock_df = create_base_df(pd.read_csv(io.StringIO(initial_csv_content)).to_dict('records'))
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())

    # Mock LiteLLM
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'gemini-test': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004}, # Match
    })
    # Mock supports_response_schema: gpt=True (missing), gemini=False (missing)
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=lambda model: model == 'gpt-test')

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)

    # gpt-test should be updated
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert gpt_row['output'] == 2.0
    assert gpt_row['structured_output'] is True

    # Row with missing model should be skipped and remain unchanged
    # Need to handle potential index difference after NA drop or processing
    anthropic_row = called_df[called_df['provider'] == 'Anthropic'].iloc[0]
    assert pd.isna(anthropic_row['model'])
    assert anthropic_row['input'] == 1.0
    assert anthropic_row['output'] == 2.0
    assert anthropic_row['structured_output'] is True

    # gemini-test should have costs match, structured_output updated to False
    gemini_row = called_df[called_df['model'] == 'gemini-test'].iloc[0]
    assert gemini_row['input'] == 3.0
    assert gemini_row['output'] == 4.0
    assert gemini_row['structured_output'] is False # Updated from NA

    # Check console output for the warning about skipping the row
    # The index might change depending on pandas version, check for provider/content
    mock_console.print.assert_any_call(f"[yellow]Warning:[/yellow] Skipping row {anthropic_row.name} due to missing model identifier.")
    mock_console.print.assert_any_call("[green]Updated (Input: 1.0000, Output: 2.0000)[/green]") # gpt cost
    mock_console.print.assert_any_call("[green]Updated (True)[/green]") # gpt struct
    mock_console.print.assert_any_call("[green]Match (Input, Output)[/green]") # gemini costs
    mock_console.print.assert_any_call("[green]Updated (False)[/green]") # gemini struct


# 5. Output and Saving
def test_output_messages(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output,structured_output\nOpenAI,gpt-test,,,,\nAnthropic,claude-test,1.0,2.0,True"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = create_base_df(pd.read_csv(io.StringIO(initial_csv_content)).to_dict('records'))
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())

    # Mock LiteLLM to cause updates
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'claude-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002}, # Match
    })
    # Mock supports_response_schema: gpt=True (missing), claude=True (exists)
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", return_value=True)

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check for key messages using assert_any_call
    mock_console.print.assert_any_call(f"[bold blue]Starting model data update for:[/bold blue] {temp_csv_path}")
    mock_console.print.assert_any_call(f"[green]Successfully loaded:[/green] {temp_csv_path}")
    mock_console.print.assert_any_call("[green]Successfully fetched LiteLLM model cost data.[/green]")
    mock_console.print.assert_any_call("\n[bold blue]Processing models...[/bold blue]")
    # Check table content via calls to table.add_row made through console.print(table)
    # This is complex, let's check specific update messages instead
    mock_console.print.assert_any_call("[green]Updated (Input: 1.0000, Output: 2.0000)[/green]") # gpt cost update
    mock_console.print.assert_any_call("[green]Updated (True)[/green]") # gpt struct update
    mock_console.print.assert_any_call("[green]Match (Input, Output)[/green]") # claude cost checked
    mock_console.print.assert_any_call("Checked (Exists)") # claude struct checked
    # Check summary - numbers depend on exact execution
    mock_console.print.assert_any_call("- Models processed: 2")
    mock_console.print.assert_any_call("- Rows potentially updated (data changed): 1") # Only gpt-test changed
    mock_console.print.assert_any_call("- Models with fetch/check errors: 0")
    mock_console.print.assert_any_call("- Models with cost mismatches: 0")
    mock_console.print.assert_any_call(f"[bold green]Successfully saved updated data to:[/bold green] {temp_csv_path}")
    mock_console.print.assert_any_call(f"\n[bold yellow]Reminder:[/bold yellow] The '{'max_reasoning_tokens'}' column is not automatically updated by this script and requires manual maintenance.")
    mock_console.print.assert_any_call(f"[bold blue]Model data update process finished.[/bold blue]")


def test_save_no_updates(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output,structured_output\nOpenAI,gpt-test,1.0,2.0,True"
    temp_csv_path.write_text(initial_csv_content)

    # Use create_base_df to ensure types match what script expects after load/enforce
    mock_df = create_base_df(pd.read_csv(io.StringIO(initial_csv_content)).to_dict('records'))
    # Ensure structured_output is boolean after potential read as string
    mock_df['structured_output'] = mock_df['structured_output'].astype(bool)
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())

    # Mock LiteLLM to return data that matches existing data
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002}, # Matches 1.0, 2.0
    })
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", return_value=True) # Matches True

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_to_csv.reset_mock() # Reset mock before the call

    update_model_data(str(temp_csv_path))

    # to_csv should NOT be called because no schema changes or data updates occurred
    mock_to_csv.assert_not_called()
    mock_console.print.assert_any_call("\n[bold blue]No schema changes or data updates needed. CSV file not saved.[/bold blue]")


def test_save_with_updates(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output,structured_output\nOpenAI,gpt-test,,,,"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = create_base_df(pd.read_csv(io.StringIO(initial_csv_content)).to_dict('records'))
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())

    # Mock LiteLLM to cause updates
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
    })
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", return_value=True)

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # to_csv should be called with correct arguments
    mock_to_csv.assert_called_once_with(str(temp_csv_path), index=False, na_rep='')
    # Check the success message was printed
    mock_console.print.assert_any_call(f"[bold green]Successfully saved updated data to:[/bold green] {temp_csv_path}")

    # Verify the content of the DataFrame passed to to_csv
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert gpt_row['output'] == 2.0
    assert gpt_row['structured_output'] is True


# 6. Main Function / Argument Parsing
def test_main_default_path(mocker, capsys_rich):
    # Mock update_model_data to check if it's called with the default path
    mock_update = mocker.patch("pdd.update_model_costs.update_model_data")
    # Mock sys.argv to simulate no command line arguments
    mocker.patch('sys.argv', ['update_model_costs.py'])

    # Mock Path operations used in main
    mock_home_path = Path.home() / ".pdd" / "llm_model.csv"
    mock_default_path = Path("data/llm_model.csv").resolve()
    mock_path_instance = MagicMock()
    mock_path_instance.resolve.return_value = mock_default_path
    mock_path_instance.parent.exists.return_value = True # Assume default dir exists
    mock_path_instance.is_file.return_value = True # Assume default file exists

    mocker.patch("pdd.update_model_costs.Path", return_value=mock_path_instance)
    mocker.patch("pathlib.Path.home", return_value=Path.home()) # Keep home correct
    # Mock the specific user path check
    mocker.patch.object(mock_home_path, 'is_file', return_value=False)

    mock_makedirs = mocker.patch('os.makedirs') # Should not be called if dir exists

    main()

    # Assert update_model_data called with the resolved default path string
    mock_update.assert_called_once_with(str(mock_default_path))
    mock_makedirs.assert_not_called()


def test_main_custom_path(mocker, capsys_rich):
    # Mock update_model_data to check if it's called with the custom path
    mock_update = mocker.patch("pdd.update_model_costs.update_model_data")
    custom_path_str = "custom/data/my_models.csv"
    custom_path_obj = Path(custom_path_str)
    resolved_custom_path = custom_path_obj.resolve()

    # Mock sys.argv to simulate command line argument
    mocker.patch('sys.argv', ['update_model_costs.py', '--csv-path', custom_path_str])

    # Mock Path operations
    mock_home_path = Path.home() / ".pdd" / "llm_model.csv"
    mock_arg_path_instance = MagicMock()
    mock_arg_path_instance.resolve.return_value = resolved_custom_path
    mock_arg_path_instance.parent.exists.return_value = False # Simulate custom dir NOT existing
    mock_arg_path_instance.is_file.return_value = False # Simulate custom file NOT existing

    mocker.patch("pdd.update_model_costs.Path", return_value=mock_arg_path_instance)
    mocker.patch("pathlib.Path.home", return_value=Path.home())
    mocker.patch.object(mock_home_path, 'is_file', return_value=False) # No user file

    mock_makedirs = mocker.patch('os.makedirs')
    mock_console = mocker.patch("pdd.update_model_costs.console") # Mock console for checking output

    main()

    # Assert update_model_data called with the resolved custom path string
    mock_update.assert_called_once_with(str(resolved_custom_path))
    # Assert directory creation was called for the custom path's parent
    mock_makedirs.assert_called_once_with(resolved_custom_path.parent, exist_ok=True)
    mock_console.print.assert_any_call(f"[cyan]Created directory:[/cyan] {resolved_custom_path.parent}")

def test_main_user_path_precedence(mocker, capsys_rich):
    # Mock update_model_data to check if it's called with the user path
    mock_update = mocker.patch("pdd.update_model_costs.update_model_data")
    custom_path_str = "custom/data/my_models.csv" # Arg path (should be ignored)
    user_path = Path.home() / ".pdd" / "llm_model.csv"

    # Mock sys.argv to simulate command line argument
    mocker.patch('sys.argv', ['update_model_costs.py', '--csv-path', custom_path_str])

    # Mock Path operations
    mock_default_path_instance = MagicMock() # Mock for the Path(args.csv_path) call
    mock_default_path_instance.resolve.return_value = Path(custom_path_str).resolve()

    # Mock Path() constructor to return different mocks based on input
    def path_side_effect(path_arg):
        if str(path_arg) == custom_path_str:
            return mock_default_path_instance
        # Add other specific paths if needed, otherwise default mock
        return MagicMock()

    mocker.patch("pdd.update_model_costs.Path", side_effect=path_side_effect)
    mocker.patch("pathlib.Path.home", return_value=Path.home()) # Keep home correct
    # Mock the specific user path check to return True
    mocker.patch.object(user_path, 'is_file', return_value=True)

    mock_makedirs = mocker.patch('os.makedirs') # Should not be called

    main()

    # Assert update_model_data called with the user path string
    mock_update.assert_called_once_with(str(user_path))
    mock_makedirs.assert_not_called() # Directory creation should be skipped
