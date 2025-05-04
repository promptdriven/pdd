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
from unittest.mock import patch, MagicMock

# Need to adjust import based on package structure
# Assuming the code is in pdd/update_model_costs.py and tests are in tests/
import sys
# Add the parent directory of 'pdd' to sys.path
# This is a common pattern in pytest for testing packages
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from pdd.update_model_costs import update_model_data, main, EXPECTED_COLUMNS, MISSING_VALUE_PLACEHOLDER

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
def create_base_df(data=None):
    """Creates a pandas DataFrame with EXPECTED_COLUMNS."""
    if data is None:
        data = []
    # Ensure all expected columns are present, even if data is sparse
    df = pd.DataFrame(data)
    for col in EXPECTED_COLUMNS:
        if col not in df.columns:
            df[col] = pd.NA # Use pandas NA as default missing
    # Reorder columns to match EXPECTED_COLUMNS
    df = df[EXPECTED_COLUMNS]

    # Apply initial type conversions as done in the script
    if 'input' in df.columns:
        df['input'] = pd.to_numeric(df['input'], errors='coerce')
    if 'output' in df.columns:
        df['output'] = pd.to_numeric(df['output'], errors='coerce')
    if 'structured_output' in df.columns:
        df['structured_output'] = df['structured_output'].apply(
           lambda x: pd.NA if pd.isna(x) else (
               True if str(x).strip().lower() == 'true' else (
                   False if str(x).strip().lower() == 'false' else pd.NA
               )
           )
       ).astype('object')

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
    mock_read_csv = mocker.patch("pandas.read_csv", return_value=create_base_df())
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_litellm_cost = mocker.patch("litellm.model_cost", {})
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", return_value=False)
    mock_console = mocker.patch("pdd.update_model_costs.console")

    non_existent_dir = tmp_path / "new_dir"
    csv_path = non_existent_dir / "llm_model.csv"

    # Mock sys.argv to simulate command line argument
    mocker.patch('sys.argv', ['update_model_costs.py', '--csv-path', str(csv_path)])

    main()

    # Check if directory was created
    assert non_existent_dir.exists()
    mock_console.print.assert_any_call(f"[cyan]Created directory:[/cyan] {non_existent_dir}")
    mock_read_csv.assert_called_once_with(str(csv_path))
    mock_to_csv.assert_called_once() # Should attempt to save even if no updates

def test_directory_creation_permission_error(mocker, tmp_path, capsys_rich):
    mock_read_csv = mocker.patch("pandas.read_csv") # Won't be called if dir creation fails
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_makedirs = mocker.patch("os.makedirs", side_effect=OSError("Permission denied"))
    mock_console = mocker.patch("pdd.update_model_costs.console")

    non_existent_dir = tmp_path / "new_dir"
    csv_path = non_existent_dir / "llm_model.csv"

    mocker.patch('sys.argv', ['update_model_costs.py', '--csv-path', str(csv_path)])

    main()

    mock_makedirs.assert_called_once_with(non_existent_dir)
    mock_console.print.assert_any_call(f"[bold red]Error:[/bold red] Could not create directory {non_existent_dir}: Permission denied")
    mock_read_csv.assert_not_called()
    mock_to_csv.assert_not_called()

def test_file_write_error(mocker, temp_csv_path, capsys_rich):
    # Create a dummy CSV file
    initial_csv_content = "provider,model,input,output\nOpenAI,gpt-test,,"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = create_base_df([{'provider': 'OpenAI', 'model': 'gpt-test', 'input': pd.NA, 'output': pd.NA}])
    mocker.patch("pandas.read_csv", return_value=mock_df)

    # Mock LiteLLM to provide data so an update is attempted
    mock_litellm_cost = mocker.patch("litellm.model_cost", {'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002}})
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", return_value=True)

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", side_effect=Exception("Disk full"))
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    mock_to_csv.assert_called_once_with(str(temp_csv_path), index=False, na_rep='')
    mock_console.print.assert_any_call(f"[bold red]Error:[/bold red] Failed to save updated CSV file: Disk full")


# 2. CSV Loading and Schema Handling
def test_load_empty_csv(mocker, temp_csv_path, capsys_rich):
    # Create an empty CSV file with only headers
    empty_csv_content = ",".join(EXPECTED_COLUMNS) + "\n"
    temp_csv_path.write_text(empty_csv_content)

    mock_litellm_cost = mocker.patch("litellm.model_cost", {})
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", return_value=False)
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Read the DataFrame that was loaded (or mocked)
    # Since we are testing loading, let's mock read_csv to return an empty DF with headers
    mock_df_loaded = create_base_df([]) # Empty DF with all columns
    mocker.patch("pandas.read_csv", return_value=mock_df_loaded)

    update_model_data(str(temp_csv_path))

    # Check if missing columns were handled (they should be present in mock_df_loaded)
    # The script adds columns if missing from the loaded DF.
    # Let's test the scenario where the *initial* CSV is missing columns.
    initial_csv_missing_cols = "provider,model,input,output\n"
    temp_csv_path.write_text(initial_csv_missing_cols)
    mock_df_initial = pd.read_csv(io.StringIO(initial_csv_missing_cols)) # Simulate initial load

    mocker.patch("pandas.read_csv", return_value=mock_df_initial)
    mock_df_to_csv = mocker.patch("pandas.DataFrame.to_csv")

    update_model_data(str(temp_csv_path))

    # Check if to_csv was called with a DataFrame that has all expected columns
    called_df = mock_df_to_csv.call_args[0][0]
    assert all(col in called_df.columns for col in EXPECTED_COLUMNS)
    mock_console.print.assert_any_call("[yellow]Warning:[/yellow] Column 'coding_arena_elo' missing. Adding it.")
    mock_console.print.assert_any_call("[cyan]CSV schema updated with missing columns.[/cyan]")


def test_load_csv_with_placeholders(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = f"provider,model,input,output,structured_output\nOpenAI,gpt-test,{MISSING_VALUE_PLACEHOLDER},{MISSING_VALUE_PLACEHOLDER},False\nAnthropic,claude-test,1.0,2.0,{MISSING_VALUE_PLACEHOLDER}"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = pd.read_csv(io.StringIO(initial_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df)

    # Mock LiteLLM to provide data
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'claude-test': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004}
    })
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=lambda model: model == 'claude-test') # claude-test supports, gpt-test doesn't

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    called_df = mock_to_csv.call_args[0][0]

    # gpt-test should have costs updated from placeholder
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0 # 0.000001 * 1M
    assert gpt_row['output'] == 2.0 # 0.000002 * 1M
    assert gpt_row['structured_output'] is False # Was already False

    # claude-test should have structured_output updated from placeholder
    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['input'] == 1.0 # Was already 1.0
    assert claude_row['output'] == 2.0 # Was already 2.0
    assert claude_row['structured_output'] is True # Updated from placeholder

    mock_console.print.assert_any_call("[green]Updated (Input: 1.0000, Output: 2.0000)[/green]")
    mock_console.print.assert_any_call("[green]Updated (True)[/green]")


def test_load_csv_with_existing_data(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output,structured_output\nOpenAI,gpt-test,0.5,0.7,True\nAnthropic,claude-test,1.0,2.0,False"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = pd.read_csv(io.StringIO(initial_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df)

    # Mock LiteLLM to provide different data
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002}, # 1.0, 2.0
        'claude-test': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004} # 3.0, 4.0
    })
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=lambda model: model == 'claude-test') # claude-test supports, gpt-test doesn't

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    called_df = mock_to_csv.call_args[0][0]

    # Existing data should NOT be overwritten
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 0.5
    assert gpt_row['output'] == 0.7
    assert gpt_row['structured_output'] is True

    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['input'] == 1.0
    assert claude_row['output'] == 2.0
    assert claude_row['structured_output'] is False

    # Check console output - should indicate checked, not updated
    assert "Updated" not in capsys_rich.readouterr().stdout
    mock_console.print.assert_any_call("[yellow]No missing costs found/updated[/yellow]")
    mock_console.print.assert_any_call("Checked", style="yellow") # For structured output
    mock_console.print.assert_any_call("[green]OK[/green]") # Row status

def test_load_csv_with_invalid_cost_data(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output\nOpenAI,gpt-test,abc,1.0\nAnthropic,claude-test,2.0,xyz"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = pd.read_csv(io.StringIO(initial_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df)

    # Mock LiteLLM to provide data
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'claude-test': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004}
    })
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", return_value=False)

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    called_df = mock_to_csv.call_args[0][0]

    # Invalid data should be coerced to NA and then updated by LiteLLM
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert pd.isna(mock_df.loc[0, 'input']) # Check initial coercion
    assert gpt_row['input'] == 1.0 # Updated from LiteLLM
    assert gpt_row['output'] == 1.0 # Was valid, not updated

    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['input'] == 2.0 # Was valid, not updated
    assert pd.isna(mock_df.loc[1, 'output']) # Check initial coercion
    assert claude_row['output'] == 4.0 # Updated from LiteLLM

    mock_console.print.assert_any_call("[green]Updated (Input: 1.0000)[/green]")
    mock_console.print.assert_any_call("[green]Updated (Output: 4.0000)[/green]")


def test_load_csv_with_invalid_structured_output_data(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,structured_output\nOpenAI,gpt-test,yes\nAnthropic,claude-test,no\nGoogle,gemini-test,maybe"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = pd.read_csv(io.StringIO(initial_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df)

    # Mock LiteLLM structured output support
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=lambda model: model == 'claude-test') # Only claude-test supports

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    called_df = mock_to_csv.call_args[0][0]

    # Invalid data should be coerced to NA and then updated by LiteLLM if supported
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert pd.isna(mock_df.loc[0, 'structured_output']) # Check initial coercion
    assert pd.isna(gpt_row['structured_output']) # Remains NA as LiteLLM mock returns False (or doesn't support)

    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert pd.isna(mock_df.loc[1, 'structured_output']) # Check initial coercion
    assert claude_row['structured_output'] is True # Updated from LiteLLM

    gemini_row = called_df[called_df['model'] == 'gemini-test'].iloc[0]
    assert pd.isna(mock_df.loc[2, 'structured_output']) # Check initial coercion
    assert pd.isna(gemini_row['structured_output']) # Remains NA as LiteLLM mock returns False (or doesn't support)

    mock_console.print.assert_any_call("[green]Updated (True)[/green]")
    mock_console.print.assert_any_call("[yellow]Check failed (Unknown Model?): supports_response_schema mock[/yellow]") # Assuming mock raises ValueError for unknown


# 3. LiteLLM Interaction (Mocked)
def test_update_missing_costs(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output\nOpenAI,gpt-test,,\nAnthropic,claude-test,-1.0,"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = pd.read_csv(io.StringIO(initial_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df)

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
    called_df = mock_to_csv.call_args[0][0]

    # gpt-test should have both costs updated from NA
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert gpt_row['output'] == 2.0

    # claude-test should have input updated from -1.0 and output from NA
    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['input'] == 3.0
    assert claude_row['output'] == 4.0

    mock_console.print.assert_any_call("[green]Updated (Input: 1.0000, Output: 2.0000)[/green]")
    mock_console.print.assert_any_call("[green]Updated (Input: 3.0000, Output: 4.0000)[/green]")


def test_update_missing_structured_output(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,structured_output\nOpenAI,gpt-test,\nAnthropic,claude-test,False\nGoogle,gemini-test,"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = pd.read_csv(io.StringIO(initial_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df)

    # Mock LiteLLM structured output support
    mock_litellm_cost = mocker.patch("litellm.model_cost", {}) # Not testing costs here
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=lambda model: model == 'gpt-test') # Only gpt-test supports

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    called_df = mock_to_csv.call_args[0][0]

    # gpt-test should be updated to True
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['structured_output'] is True

    # claude-test should remain False (was already set)
    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['structured_output'] is False

    # gemini-test should remain NA (missing and LiteLLM mock returns False/doesn't support)
    gemini_row = called_df[called_df['model'] == 'gemini-test'].iloc[0]
    assert pd.isna(gemini_row['structured_output'])

    mock_console.print.assert_any_call("[green]Updated (True)[/green]")
    mock_console.print.assert_any_call("Checked", style="yellow") # For claude-test (already False)
    mock_console.print.assert_any_call("[yellow]Check failed (Unknown Model?): supports_response_schema mock[/yellow]") # For gemini-test


def test_update_both_missing(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output,structured_output\nOpenAI,gpt-test,,,,\nAnthropic,claude-test,1.0,2.0,"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = pd.read_csv(io.StringIO(initial_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df)

    # Mock LiteLLM
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'claude-test': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004}
    })
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=lambda model: model == 'gpt-test') # Only gpt-test supports

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    called_df = mock_to_csv.call_args[0][0]

    # gpt-test should have costs and structured_output updated
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert gpt_row['output'] == 2.0
    assert gpt_row['structured_output'] is True

    # claude-test should only have structured_output updated (costs were present)
    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['input'] == 1.0
    assert claude_row['output'] == 2.0
    assert pd.isna(claude_row['structured_output']) # Remains NA as LiteLLM mock returns False/doesn't support

    mock_console.print.assert_any_call("[green]Updated (Input: 1.0000, Output: 2.0000)[/green]")
    mock_console.print.assert_any_call("[green]Updated (True)[/green]")
    mock_console.print.assert_any_call("[yellow]No missing costs found/updated[/yellow]")
    mock_console.print.assert_any_call("[yellow]Check failed (Unknown Model?): supports_response_schema mock[/yellow]")


def test_litellm_cost_fetch_failure(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output\nOpenAI,gpt-test,,"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = pd.read_csv(io.StringIO(initial_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df)

    # Mock LiteLLM cost fetch to raise an exception
    mocker.patch("litellm.model_cost", side_effect=Exception("Network Error"))
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", return_value=False)

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    called_df = mock_to_csv.call_args[0][0]

    # Costs should remain NA
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert pd.isna(gpt_row['input'])
    assert pd.isna(gpt_row['output'])

    mock_console.print.assert_any_call("[bold red]Error:[/bold red] Could not fetch LiteLLM model cost data: Network Error")
    mock_console.print.assert_any_call("[yellow]Cost data not found in LiteLLM[/yellow]") # This message is printed if all_model_costs is empty {}
    mock_console.print.assert_any_call("[red]Fail (Cost Error)[/red]") # Row status


def test_litellm_cost_model_not_found(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output\nOpenAI,gpt-test,,"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = pd.read_csv(io.StringIO(initial_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df)

    # Mock LiteLLM cost data, but exclude 'gpt-test'
    mock_litellm_cost = mocker.patch("litellm.model_cost", {'other-model': {'input_cost_per_token': 0.1, 'output_cost_per_token': 0.2}})
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", return_value=False)

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    called_df = mock_to_csv.call_args[0][0]

    # Costs should remain NA
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert pd.isna(gpt_row['input'])
    assert pd.isna(gpt_row['output'])

    mock_console.print.assert_any_call("[yellow]Cost data not found in LiteLLM[/yellow]")
    mock_console.print.assert_any_call("[yellow]Partial Fail (Cost)[/yellow]") # Row status


def test_litellm_cost_missing_keys(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output\nOpenAI,gpt-test,,\nAnthropic,claude-test,,"
    temp_csv_content = initial_csv_content
    temp_csv_path.write_text(temp_csv_content)

    mock_df = pd.read_csv(io.StringIO(temp_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df)

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
    called_df = mock_to_csv.call_args[0][0]

    # gpt-test should have input updated, output remain NA
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert pd.isna(gpt_row['output'])

    # claude-test should have output updated, input remain NA
    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert pd.isna(claude_row['input'])
    assert claude_row['output'] == 4.0

    mock_console.print.assert_any_call("[green]Updated (Input: 1.0000)[/green]")
    mock_console.print.assert_any_call("[green]Updated (Output: 4.0000)[/green]")


def test_litellm_structured_output_check_failure(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,structured_output\nOpenAI,gpt-test,\nAnthropic,claude-test,"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = pd.read_csv(io.StringIO(initial_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df)

    mock_litellm_cost = mocker.patch("litellm.model_cost", {})
    # Mock LiteLLM structured output check to raise an exception for one model
    def supports_schema_side_effect(model):
        if model == 'gpt-test':
            raise ValueError("Unknown model for schema check")
        elif model == 'claude-test':
             raise Exception("API error")
        return False # Default for others

    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=supports_schema_side_effect)

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    called_df = mock_to_csv.call_args[0][0]

    # structured_output should remain NA for both models
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert pd.isna(gpt_row['structured_output'])

    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert pd.isna(claude_row['structured_output'])

    mock_console.print.assert_any_call("[yellow]Check failed (Unknown Model?): Unknown model for schema check[/yellow]")
    mock_console.print.assert_any_call("[red]Error checking support: API error[/red]")
    mock_console.print.assert_any_call("[yellow]Partial Fail (Struct)[/yellow]") # For gpt-test
    mock_console.print.assert_any_call("[red]Fail (Struct Error)[/red]") # For claude-test


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

    mock_df = pd.read_csv(io.StringIO(initial_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df)

    # Mock LiteLLM
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-needs-all': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'claude-needs-cost': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004},
        'gemini-needs-struct': {'input_cost_per_token': 0.000005, 'output_cost_per_token': 0.000006},
        'mistral-complete': {'input_cost_per_token': 0.000007, 'output_cost_per_token': 0.000008},
    })
    def supports_schema_side_effect(model):
        if model == 'gpt-needs-all': return True
        if model == 'claude-needs-cost': return False # Already True in CSV, shouldn't change
        if model == 'gemini-needs-struct': return True
        if model == 'mistral-complete': return False # Already False in CSV, shouldn't change
        raise ValueError("Unknown model for schema check") # For unknown-model

    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=supports_schema_side_effect)

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    called_df = mock_to_csv.call_args[0][0]

    # gpt-needs-all: costs and struct updated
    gpt_row = called_df[called_df['model'] == 'gpt-needs-all'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert gpt_row['output'] == 2.0
    assert gpt_row['structured_output'] is True

    # claude-needs-cost: only input cost updated, output and struct remain
    claude_row = called_df[called_df['model'] == 'claude-needs-cost'].iloc[0]
    assert claude_row['input'] == 3.0
    assert claude_row['output'] == 1.0 # Original value
    assert claude_row['structured_output'] is True # Original value

    # gemini-needs-struct: only structured_output updated, costs remain
    gemini_row = called_df[called_df['model'] == 'gemini-needs-struct'].iloc[0]
    assert gemini_row['input'] == 2.0 # Original value
    assert gemini_row['output'] == 3.0 # Original value
    assert gemini_row['structured_output'] is True

    # mistral-complete: nothing updated
    mistral_row = called_df[called_df['model'] == 'mistral-complete'].iloc[0]
    assert mistral_row['input'] == 4.0
    assert mistral_row['output'] == 5.0
    assert mistral_row['structured_output'] is False

    # unknown-model: nothing updated, warnings printed
    unknown_row = called_df[called_df['model'] == 'unknown-model'].iloc[0]
    assert pd.isna(unknown_row['input'])
    assert pd.isna(unknown_row['output'])
    assert pd.isna(unknown_row['structured_output'])

    # Check console output for updates and warnings
    output = capsys_rich.readouterr().stdout
    assert "[green]Updated (Input: 1.0000, Output: 2.0000)[/green]" in output # gpt
    assert "[green]Updated (True)[/green]" in output # gpt struct
    assert "[green]Updated (Input: 3.0000)[/green]" in output # claude cost
    assert "[yellow]No missing costs found/updated[/yellow]" in output # claude output, gemini costs, mistral costs
    assert "[green]Updated (True)[/green]" in output # gemini struct
    assert "Checked" in output # claude struct, mistral struct
    assert "[yellow]Cost data not found in LiteLLM[/yellow]" in output # unknown-model cost
    assert "[yellow]Check failed (Unknown Model?): Unknown model for schema check[/yellow]" in output # unknown-model struct


def test_csv_with_missing_model_identifier(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = """provider,model,input,output,structured_output
OpenAI,gpt-test,,,
Anthropic,,1.0,2.0,True
Google,gemini-test,3.0,4.0,
"""
    temp_csv_path.write_text(initial_csv_content)

    mock_df = pd.read_csv(io.StringIO(initial_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df)

    # Mock LiteLLM
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'gemini-test': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004},
    })
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=lambda model: model == 'gpt-test')

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check the DataFrame passed to to_csv
    called_df = mock_to_csv.call_args[0][0]

    # gpt-test should be updated
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert gpt_row['output'] == 2.0
    assert gpt_row['structured_output'] is True

    # Row with missing model should be skipped and remain unchanged
    anthropic_row = called_df[called_df['provider'] == 'Anthropic'].iloc[0]
    assert pd.isna(anthropic_row['model'])
    assert anthropic_row['input'] == 1.0
    assert anthropic_row['output'] == 2.0
    assert anthropic_row['structured_output'] is True

    # gemini-test should be updated for structured_output
    gemini_row = called_df[called_df['model'] == 'gemini-test'].iloc[0]
    assert gemini_row['input'] == 3.0
    assert gemini_row['output'] == 4.0
    assert pd.isna(gemini_row['structured_output']) # Remains NA as LiteLLM mock returns False/doesn't support

    # Check console output for the warning about skipping the row
    mock_console.print.assert_any_call("[yellow]Warning:[/yellow] Skipping row 1 due to missing model identifier.")
    mock_console.print.assert_any_call("[green]Updated (Input: 1.0000, Output: 2.0000)[/green]") # gpt
    mock_console.print.assert_any_call("[green]Updated (True)[/green]") # gpt struct
    mock_console.print.assert_any_call("[yellow]No missing costs found/updated[/yellow]") # gemini costs
    mock_console.print.assert_any_call("[yellow]Check failed (Unknown Model?): supports_response_schema mock[/yellow]") # gemini struct


# 5. Output and Saving
def test_output_messages(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output,structured_output\nOpenAI,gpt-test,,,,\nAnthropic,claude-test,1.0,2.0,True"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = pd.read_csv(io.StringIO(initial_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df)

    # Mock LiteLLM to cause updates
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
    })
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", side_effect=lambda model: model == 'gpt-test')

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # Check for key messages in the captured output
    output = capsys_rich.readouterr().stdout
    assert "Starting model data update for:" in output
    assert "Successfully loaded:" in output
    assert "Successfully fetched LiteLLM model cost data." in output
    assert "Processing models..." in output
    assert "Model Update Status" in output # Check for table title
    assert "gpt-test" in output
    assert "claude-test" in output
    assert "[green]Updated (Input: 1.0000, Output: 2.0000)[/green]" in output # gpt cost update
    assert "[green]Updated (True)[/green]" in output # gpt struct update
    assert "[yellow]No missing costs found/updated[/yellow]" in output # claude cost checked
    assert "Checked" in output # claude struct checked
    assert "[blue]Updated[/blue]" in output # gpt row status
    assert "[green]OK[/green]" in output # claude row status
    assert "Summary:" in output
    assert "Models processed: 2" in output
    assert "Rows potentially updated: 1" in output
    assert "Successfully saved updated data to:" in output
    assert "Reminder: The 'max_reasoning_tokens' column is not automatically updated" in output
    assert "Model data update process finished." in output


def test_save_no_updates(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output,structured_output\nOpenAI,gpt-test,1.0,2.0,True"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = pd.read_csv(io.StringIO(initial_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df)

    # Mock LiteLLM to return data that matches existing data, so no updates occur
    mock_litellm_cost = mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002}, # Matches 1.0, 2.0
    })
    mock_supports_schema = mocker.patch("litellm.supports_response_schema", return_value=True) # Matches True

    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv")
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    # to_csv should NOT be called because no updates were made
    mock_to_csv.assert_not_called()
    mock_console.print.assert_any_call("[bold blue]No updates needed or made to the CSV file.[/bold blue]")


def test_save_with_updates(mocker, temp_csv_path, capsys_rich):
    initial_csv_content = "provider,model,input,output,structured_output\nOpenAI,gpt-test,,,,"
    temp_csv_path.write_text(initial_csv_content)

    mock_df = pd.read_csv(io.StringIO(initial_csv_content))
    mocker.patch("pandas.read_csv", return_value=mock_df)

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
    mock_console.print.assert_any_call(f"[bold green]Successfully saved updated data to:[/bold green] {temp_csv_path}")

    # Optional: Verify the content of the DataFrame passed to to_csv
    called_df = mock_to_csv.call_args[0][0]
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
    # Mock os.path.exists and os.makedirs to prevent actual file/dir ops
    mocker.patch('os.path.exists', return_value=True)
    mocker.patch('os.makedirs')

    main()

    mock_update.assert_called_once_with("data/llm_model.csv")


def test_main_custom_path(mocker, capsys_rich):
    # Mock update_model_data to check if it's called with the custom path
    mock_update = mocker.patch("pdd.update_model_costs.update_model_data")
    custom_path = "custom/data/my_models.csv"
    # Mock sys.argv to simulate command line argument
    mocker.patch('sys.argv', ['update_model_costs.py', '--csv-path', custom_path])
    # Mock os.path.exists and os.makedirs for the custom path
    mocker.patch('os.path.exists', return_value=False) # Simulate directory not existing
    mock_makedirs = mocker.patch('os.makedirs')

    main()

    mock_update.assert_called_once_with(custom_path)
    mock_makedirs.assert_called_once_with(os.path.dirname(custom_path))
