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
from unittest.mock import patch, MagicMock, call, ANY, PropertyMock
from pathlib import Path # Import Path
from rich.table import Table # Import Table for mocking

# Package is installed in editable mode, direct imports work

from pdd.update_model_costs import update_model_data, main, EXPECTED_COLUMNS

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
def create_base_df(data=None, columns_override=None):
    """
    Creates a pandas DataFrame.
    If data is provided, it's a list of dicts. All EXPECTED_COLUMNS will be present.
    If columns_override is provided, it's used instead of EXPECTED_COLUMNS for DataFrame creation.
    """
    if data is None:
        data = []

    # Determine the columns to use for the DataFrame
    df_cols = columns_override if columns_override else EXPECTED_COLUMNS

    processed_data = []
    if data:
        for row_dict in data:
            new_row = {col: pd.NA for col in df_cols} # Initialize with NAs for all target columns
            new_row.update(row_dict) # Populate with data from the current row_dict
            processed_data.append(new_row)
        df = pd.DataFrame(processed_data, columns=df_cols)
    else: # No data, create empty DF with specified or expected columns
        df = pd.DataFrame(columns=df_cols)

    # Ensure all EXPECTED_COLUMNS are present if not overridden, and in correct order
    # This step is crucial if columns_override was used and might not contain all EXPECTED_COLUMNS,
    # or if we want to standardize after initial creation.
    # However, if columns_override was intentional, we might not want to force EXPECTED_COLUMNS.
    # For this helper's purpose in tests, we usually want to align with EXPECTED_COLUMNS.
    if columns_override is None: # Only enforce EXPECTED_COLUMNS if no override was given
        for col in EXPECTED_COLUMNS:
            if col not in df.columns:
                df[col] = pd.NA
        df = df[EXPECTED_COLUMNS]


    # Apply initial type coercions similar to what read_csv might do or to set up for script's expectations
    if 'input' in df.columns:
        df['input'] = pd.to_numeric(df['input'], errors='coerce')
    if 'output' in df.columns:
        df['output'] = pd.to_numeric(df['output'], errors='coerce')
    if 'structured_output' in df.columns:
        # Keep as object to hold True, False, pd.NA. Script handles 'True'/'False' string conversion.
        df['structured_output'] = df['structured_output'].astype('object')
    for col in ['coding_arena_elo', 'max_reasoning_tokens']:
         if col in df.columns:
             df[col] = pd.to_numeric(df[col], errors='coerce')

    # Ensure 'model' column is object/string type if it exists and isn't all NA
    # This is critical to prevent 'model' identifiers from becoming NaN if they were, e.g., all numbers
    if 'model' in df.columns:
        # Convert to string, but handle pd.NA correctly to avoid creating "<NA>" strings
        df['model'] = df['model'].apply(lambda x: str(x) if not pd.isna(x) else pd.NA)

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
    mock_read_csv = mocker.patch("pdd.update_model_costs.pd.read_csv", return_value=create_base_df())
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mocker.patch("litellm.model_cost", {})
    mocker.patch("litellm.supports_response_schema", return_value=False)
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_os_makedirs = mocker.patch("pdd.update_model_costs.os.makedirs")

    non_existent_dir_path = tmp_path / "new_dir"
    csv_file_path = non_existent_dir_path / "llm_model.csv"

    # Mock for Path.home() chain
    mock_home_dir_obj = MagicMock(spec=Path, name="mock_home_dir_obj")
    mock_home_pdd_dir_obj = MagicMock(spec=Path, name="mock_home_pdd_dir_obj")
    mock_user_config_file_obj = MagicMock(spec=Path, name="mock_user_config_file_obj")
    mock_home_dir_obj.__truediv__.return_value = mock_home_pdd_dir_obj
    mock_home_pdd_dir_obj.__truediv__.return_value = mock_user_config_file_obj
    mock_user_config_file_obj.is_file.return_value = False # User config does not exist

    # Mock for Path(args.csv_path) chain
    mock_arg_path_resolved_obj = MagicMock(spec=Path, name="mock_arg_path_resolved_obj")
    mock_arg_parent_dir_obj = MagicMock(spec=Path, name="mock_arg_parent_dir_obj")
    mock_arg_parent_dir_obj.exists.return_value = False # Parent dir of arg path does not exist
    mock_arg_parent_dir_obj.__str__.return_value = str(non_existent_dir_path)
    mock_arg_path_resolved_obj.parent = mock_arg_parent_dir_obj
    mock_arg_path_resolved_obj.__str__.return_value = str(csv_file_path)

    mock_arg_path_unresolved_obj = MagicMock(spec=Path, name="mock_arg_path_unresolved_obj")
    mock_arg_path_unresolved_obj.resolve.return_value = mock_arg_path_resolved_obj

    # Mock Path class itself
    mock_path_class = mocker.patch("pdd.update_model_costs.Path", autospec=True)
    mock_path_class.home.return_value = mock_home_dir_obj # Path.home() behavior
    mock_path_class.return_value = mock_arg_path_unresolved_obj # Path(...) constructor behavior

    mocker.patch('sys.argv', ['update_model_costs.py', '--csv-path', str(csv_file_path)])
    main()

    mock_os_makedirs.assert_called_once_with(mock_arg_parent_dir_obj, exist_ok=True)
    mock_console.print.assert_any_call(f"[cyan]Created directory:[/cyan] {mock_arg_parent_dir_obj}")
    mock_read_csv.assert_called_with(str(csv_file_path)) # update_model_data called with this
    # No updates to data or schema, so to_csv not called
    mock_to_csv.assert_not_called()
    mock_console.print.assert_any_call("\n[bold blue]No schema changes or data updates needed. CSV file not saved.[/bold blue]")


def test_directory_creation_permission_error(mocker, tmp_path, capsys_rich):
    mock_update_model_data = mocker.patch("pdd.update_model_costs.update_model_data")
    mock_os_makedirs = mocker.patch("pdd.update_model_costs.os.makedirs", side_effect=OSError("Permission denied"))
    mock_console = mocker.patch("pdd.update_model_costs.console")

    non_existent_dir_path = tmp_path / "new_dir"
    csv_file_path_str = str(non_existent_dir_path / "llm_model.csv")

    # Mock for Path.home() chain
    mock_home_dir_obj = MagicMock(spec=Path, name="mock_home_dir_obj")
    mock_home_pdd_dir_obj = MagicMock(spec=Path, name="mock_home_pdd_dir_obj")
    mock_user_config_file_obj = MagicMock(spec=Path, name="mock_user_config_file_obj")
    mock_home_dir_obj.__truediv__.return_value = mock_home_pdd_dir_obj
    mock_home_pdd_dir_obj.__truediv__.return_value = mock_user_config_file_obj
    mock_user_config_file_obj.is_file.return_value = False # User config does not exist

    # Mock for Path(args.csv_path) chain
    mock_arg_path_resolved_obj = MagicMock(spec=Path, name="mock_arg_path_resolved_obj")
    mock_arg_parent_dir_obj = MagicMock(spec=Path, name="mock_arg_parent_dir_obj")
    mock_arg_parent_dir_obj.exists.return_value = False # Parent dir of arg path does not exist
    mock_arg_parent_dir_obj.__str__.return_value = str(non_existent_dir_path)
    mock_arg_path_resolved_obj.parent = mock_arg_parent_dir_obj
    # __str__ for resolved path not strictly needed here as update_model_data is mocked

    mock_arg_path_unresolved_obj = MagicMock(spec=Path, name="mock_arg_path_unresolved_obj")
    mock_arg_path_unresolved_obj.resolve.return_value = mock_arg_path_resolved_obj

    # Mock Path class itself
    mock_path_class = mocker.patch("pdd.update_model_costs.Path", autospec=True)
    mock_path_class.home.return_value = mock_home_dir_obj
    mock_path_class.return_value = mock_arg_path_unresolved_obj
    
    mocker.patch('sys.argv', ['update_model_costs.py', '--csv-path', csv_file_path_str])
    main()

    mock_os_makedirs.assert_called_once_with(mock_arg_parent_dir_obj, exist_ok=True)
    mock_console.print.assert_any_call(f"[bold red]Error:[/bold red] Could not create directory {mock_arg_parent_dir_obj}: Permission denied")
    mock_update_model_data.assert_not_called()


def test_file_write_error(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [{'provider': 'OpenAI', 'model': 'gpt-test', 'input': pd.NA, 'output': pd.NA, 'structured_output': pd.NA}]
    mock_df_initial = create_base_df(mock_df_data)
    assert mock_df_initial.loc[0, 'model'] == 'gpt-test'


    mocker.patch("pandas.read_csv", return_value=mock_df_initial.copy())
    mocker.patch("litellm.model_cost", {'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002}})
    mocker.patch("litellm.supports_response_schema", return_value=True) # Causes update
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", side_effect=Exception("Disk full"), autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    assert mock_to_csv.call_count >= 1
    if mock_to_csv.call_args:
        assert mock_to_csv.call_args.args[1] == str(temp_csv_path)
        assert mock_to_csv.call_args.kwargs['index'] is False
        assert mock_to_csv.call_args.kwargs['na_rep'] == ''
    mock_console.print.assert_any_call(f"[bold red]Error:[/bold red] Failed to save updated CSV file: Disk full")

# 2. CSV Loading and Schema Handling
def test_load_csv_missing_columns(mocker, temp_csv_path, capsys_rich):
    initial_csv_missing_cols = "provider,model,input,output\nOpenAI,gpt-test,1.0,2.0\n"
    temp_csv_path.write_text(initial_csv_missing_cols)
    df_from_csv = pd.read_csv(io.StringIO(initial_csv_missing_cols))
    
    mocker.patch("pandas.read_csv", return_value=df_from_csv)
    mocker.patch("litellm.model_cost", {})
    mocker.patch("litellm.supports_response_schema", return_value=False)
    mock_df_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    mock_console.print.assert_any_call("[yellow]Warning:[/yellow] Column 'coding_arena_elo' missing. Adding it.")
    mock_console.print.assert_any_call("[yellow]Warning:[/yellow] Column 'base_url' missing. Adding it.")
    mock_console.print.assert_any_call("[yellow]Warning:[/yellow] Column 'structured_output' missing. Adding it.")
    mock_console.print.assert_any_call("[cyan]CSV schema updated with missing columns.[/cyan]")
    mock_df_to_csv.assert_called_once()
    called_df = mock_df_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)
    assert all(col in called_df.columns for col in EXPECTED_COLUMNS)
    assert list(called_df.columns) == EXPECTED_COLUMNS

def test_load_csv_with_placeholders_as_na(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [
        {'provider': 'OpenAI', 'model': 'gpt-test', 'input': pd.NA, 'output': pd.NA, 'structured_output': 'False'},
        {'provider': 'Anthropic', 'model': 'claude-test', 'input': 1.0, 'output': 2.0, 'structured_output': pd.NA},
        {'provider': 'Google', 'model': 'gemini-test', 'input': pd.NA, 'output': pd.NA, 'structured_output': pd.NA},
    ]
    mock_df = create_base_df(mock_df_data)
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())
    mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'claude-test': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004},
        'gemini-test': {'input_cost_per_token': 0.000005, 'output_cost_per_token': 0.000006},
    })
    mocker.patch("litellm.supports_response_schema", side_effect=lambda model: model in ['claude-test', 'gemini-test'])
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_table_instance = MagicMock(spec=Table)
    mocker.patch("pdd.update_model_costs.Table", return_value=mock_table_instance)

    update_model_data(str(temp_csv_path))

    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert gpt_row['output'] == 2.0
    assert gpt_row['structured_output'] is False 
    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['input'] == 1.0 
    assert claude_row['output'] == 2.0 
    assert claude_row['structured_output'] is True 
    gemini_row = called_df[called_df['model'] == 'gemini-test'].iloc[0]
    assert gemini_row['input'] == 5.0
    assert gemini_row['output'] == 6.0
    assert gemini_row['structured_output'] is True 
    mock_table_instance.add_row.assert_any_call("gpt-test", "[green]Updated (Input: 1.0000, Output: 2.0000)[/green]", "Checked (Exists)", ANY, ANY)
    mock_table_instance.add_row.assert_any_call("claude-test", ANY, "[green]Updated (True)[/green]", "[bold red]Mismatch! (Input (CSV: 1.0000, LLM: 3.0000), Output (CSV: 2.0000, LLM: 4.0000))[/bold red]", ANY)
    mock_table_instance.add_row.assert_any_call("gemini-test", "[green]Updated (Input: 5.0000, Output: 6.0000)[/green]", "[green]Updated (True)[/green]", ANY, ANY)

def test_load_csv_with_existing_data(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [
        {'provider': 'OpenAI', 'model': 'gpt-test', 'input': 0.5, 'output': 0.7, 'structured_output': 'True'},
        {'provider': 'Anthropic', 'model': 'claude-test', 'input': 1.0, 'output': 2.0, 'structured_output': 'False'}
    ]
    mock_df = create_base_df(mock_df_data)
    # Script converts 'True'/'False' strings to bool, so align mock_df for comparison
    mock_df.loc[mock_df['model'] == 'gpt-test', 'structured_output'] = True
    mock_df.loc[mock_df['model'] == 'claude-test', 'structured_output'] = False

    mocker.patch("pandas.read_csv", return_value=mock_df.copy())
    mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002}, 
        'claude-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002}
    })
    mocker.patch("litellm.supports_response_schema", side_effect=lambda model: model == 'claude-test')
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    mock_to_csv.assert_not_called()
    mock_console.print.assert_any_call("\n[bold blue]No schema changes or data updates needed. CSV file not saved.[/bold blue]")
    mock_console.print.assert_any_call("- Models with cost mismatches: 1")
    mock_console.print.assert_any_call("  [bold red](Note: Mismatched costs were NOT automatically updated. Check CSV vs LiteLLM.)[/bold red]")

def test_load_csv_with_invalid_cost_data(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [
        {'provider': 'OpenAI', 'model': 'gpt-test', 'input': 'abc', 'output': 1.0},
        {'provider': 'Anthropic', 'model': 'claude-test', 'input': 2.0, 'output': 'xyz'}
    ]
    mock_df = create_base_df(mock_df_data)
    assert pd.isna(mock_df.loc[mock_df['model']=='gpt-test', 'input'].iloc[0])
    assert pd.isna(mock_df.loc[mock_df['model']=='claude-test', 'output'].iloc[0])
    
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())
    mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'claude-test': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004}
    })
    mocker.patch("litellm.supports_response_schema", return_value=False)
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_table_instance = MagicMock(spec=Table)
    mocker.patch("pdd.update_model_costs.Table", return_value=mock_table_instance)

    update_model_data(str(temp_csv_path))

    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert gpt_row['output'] == 1.0
    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['input'] == 2.0
    assert claude_row['output'] == 4.0
    mock_table_instance.add_row.assert_any_call("gpt-test", "[green]Updated (Input: 1.0000)[/green]", ANY, "[bold red]Mismatch! (Output (CSV: 1.0000, LLM: 2.0000))[/bold red]", ANY)
    mock_table_instance.add_row.assert_any_call("claude-test", "[green]Updated (Output: 4.0000)[/green]", ANY, "[bold red]Mismatch! (Input (CSV: 2.0000, LLM: 3.0000))[/bold red]", ANY)
    mock_console.print.assert_any_call("- Models with cost mismatches: 2")

def test_load_csv_with_invalid_structured_output_data(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [
        {'provider': 'OpenAI', 'model': 'gpt-test', 'structured_output': 'yes'},
        {'provider': 'Anthropic', 'model': 'claude-test', 'structured_output': 'no'},
        {'provider': 'Google', 'model': 'gemini-test', 'structured_output': 'maybe'}
    ]
    mock_df = create_base_df(mock_df_data)
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())
    mocker.patch("litellm.model_cost", {})
    def supports_schema_side_effect(model):
        if model == 'claude-test': return True
        if model == 'gemini-test': raise ValueError("Unknown model")
        return False
    mocker.patch("litellm.supports_response_schema", side_effect=supports_schema_side_effect)
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_table_instance = MagicMock(spec=Table)
    mocker.patch("pdd.update_model_costs.Table", return_value=mock_table_instance)

    update_model_data(str(temp_csv_path))

    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['structured_output'] is False
    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['structured_output'] is True
    gemini_row = called_df[called_df['model'] == 'gemini-test'].iloc[0]
    assert pd.isna(gemini_row['structured_output'])
    mock_table_instance.add_row.assert_any_call("gpt-test", ANY, "[green]Updated (False)[/green]", ANY, ANY)
    mock_table_instance.add_row.assert_any_call("claude-test", ANY, "[green]Updated (True)[/green]", ANY, ANY)
    mock_table_instance.add_row.assert_any_call("gemini-test", ANY, "[red]Validation Failed: Unknown model[/red]", ANY, ANY)
    mock_console.print.assert_any_call("- Models with fetch/check errors: 1")

# 3. LiteLLM Interaction (Mocked)
def test_update_missing_costs(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [
        {'provider': 'OpenAI', 'model': 'gpt-test', 'input': pd.NA, 'output': pd.NA},
        {'provider': 'Anthropic', 'model': 'claude-test', 'input': pd.NA, 'output': pd.NA}
    ]
    mock_df = create_base_df(mock_df_data)
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())
    mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'claude-test': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004}
    })
    mocker.patch("litellm.supports_response_schema", return_value=False)
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_table_instance = MagicMock(spec=Table)
    mocker.patch("pdd.update_model_costs.Table", return_value=mock_table_instance)

    update_model_data(str(temp_csv_path))

    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert gpt_row['output'] == 2.0
    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['input'] == 3.0
    assert claude_row['output'] == 4.0
    mock_table_instance.add_row.assert_any_call("gpt-test", "[green]Updated (Input: 1.0000, Output: 2.0000)[/green]", ANY, ANY, ANY)
    mock_table_instance.add_row.assert_any_call("claude-test", "[green]Updated (Input: 3.0000, Output: 4.0000)[/green]", ANY, ANY, ANY)

def test_update_missing_structured_output(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [
        {'provider': 'OpenAI', 'model': 'gpt-test', 'structured_output': pd.NA},
        {'provider': 'Anthropic', 'model': 'claude-test', 'structured_output': 'False'},
        {'provider': 'Google', 'model': 'gemini-test', 'structured_output': pd.NA}
    ]
    mock_df = create_base_df(mock_df_data)
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())
    mocker.patch("litellm.model_cost", {})
    def supports_schema_side_effect(model):
        if model == 'gpt-test': return True
        if model == 'claude-test': return False 
        if model == 'gemini-test': raise ValueError("Unknown model")
        return False
    mocker.patch("litellm.supports_response_schema", side_effect=supports_schema_side_effect)
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_table_instance = MagicMock(spec=Table)
    mocker.patch("pdd.update_model_costs.Table", return_value=mock_table_instance)

    update_model_data(str(temp_csv_path))

    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['structured_output'] is True
    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert claude_row['structured_output'] is False
    gemini_row = called_df[called_df['model'] == 'gemini-test'].iloc[0]
    assert pd.isna(gemini_row['structured_output'])
    mock_table_instance.add_row.assert_any_call("gpt-test", ANY, "[green]Updated (True)[/green]", ANY, ANY)
    mock_table_instance.add_row.assert_any_call("claude-test", ANY, "Checked (Exists)", ANY, ANY)
    mock_table_instance.add_row.assert_any_call("gemini-test", ANY, "[red]Validation Failed: Unknown model[/red]", ANY, ANY)

def test_update_both_missing(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [
        {'provider': 'OpenAI', 'model': 'gpt-test', 'input': pd.NA, 'output': pd.NA, 'structured_output': pd.NA},
        {'provider': 'Anthropic', 'model': 'claude-test', 'input': 1.0, 'output': 2.0, 'structured_output': pd.NA}
    ]
    mock_df = create_base_df(mock_df_data)
    assert mock_df.loc[mock_df['model'] == 'gpt-test', 'model'].iloc[0] == 'gpt-test' 
    assert not pd.isna(mock_df.loc[mock_df['model'] == 'gpt-test', 'model'].iloc[0])

    mocker.patch("pandas.read_csv", return_value=mock_df.copy())
    mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'claude-test': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004}
    })
    mocker.patch("litellm.supports_response_schema", side_effect=lambda model: model == 'gpt-test')
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_table_instance = MagicMock(spec=Table)
    mocker.patch("pdd.update_model_costs.Table", return_value=mock_table_instance)

    update_model_data(str(temp_csv_path))

    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)
    
    gpt_rows = called_df[called_df['model'] == 'gpt-test']
    assert not gpt_rows.empty, "Row for 'gpt-test' not found in the output DataFrame"
    gpt_row = gpt_rows.iloc[0]
    assert gpt_row['input'] == 1.0
    assert gpt_row['output'] == 2.0
    assert gpt_row['structured_output'] is True
    
    claude_rows = called_df[called_df['model'] == 'claude-test']
    assert not claude_rows.empty, "Row for 'claude-test' not found in the output DataFrame"
    claude_row = claude_rows.iloc[0]
    assert claude_row['input'] == 1.0 
    assert claude_row['output'] == 2.0
    assert claude_row['structured_output'] is False
    mock_table_instance.add_row.assert_any_call("gpt-test", "[green]Updated (Input: 1.0000, Output: 2.0000)[/green]", "[green]Updated (True)[/green]", ANY, ANY)
    mock_table_instance.add_row.assert_any_call("claude-test", ANY, "[green]Updated (False)[/green]", "[bold red]Mismatch! (Input (CSV: 1.0000, LLM: 3.0000), Output (CSV: 2.0000, LLM: 4.0000))[/bold red]", ANY)

def test_litellm_cost_fetch_failure(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [{'provider': 'OpenAI', 'model': 'gpt-test', 'input': pd.NA, 'output': pd.NA, 'structured_output': pd.NA}]
    mock_df = create_base_df(mock_df_data)
    assert mock_df.loc[0, 'model'] == 'gpt-test'

    mocker.patch("pandas.read_csv", return_value=mock_df.copy())
    mock_litellm_module = mocker.patch("pdd.update_model_costs.litellm")
    type(mock_litellm_module).model_cost = PropertyMock(side_effect=Exception("Network Error"))
    mock_litellm_module.supports_response_schema.return_value = False
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_table_instance = MagicMock(spec=Table)
    mocker.patch("pdd.update_model_costs.Table", return_value=mock_table_instance)

    update_model_data(str(temp_csv_path))

    mock_console.print.assert_any_call("[bold red]Error:[/bold red] Could not fetch LiteLLM model cost data: Network Error")
    mock_table_instance.add_row.assert_any_call(
        "gpt-test", 
        "[yellow]Cost data not found in LiteLLM[/yellow]",
        "[green]Updated (False)[/green]",
        "[grey]N/A (No LLM Data)[/grey]",
        "[blue]Updated (Info)[/blue]"
    )
    mock_to_csv.assert_called_once() 

def test_litellm_cost_model_not_found(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [{'provider': 'OpenAI', 'model': 'gpt-test', 'input': pd.NA, 'output': pd.NA, 'structured_output': pd.NA}]
    mock_df = create_base_df(mock_df_data)
    assert mock_df.loc[0, 'model'] == 'gpt-test'

    mocker.patch("pandas.read_csv", return_value=mock_df.copy())
    mocker.patch("litellm.model_cost", {'other-model': {'input_cost_per_token': 0.1, 'output_cost_per_token': 0.2}})
    mocker.patch("litellm.supports_response_schema", return_value=False)
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_table_instance = MagicMock(spec=Table)
    mocker.patch("pdd.update_model_costs.Table", return_value=mock_table_instance)

    update_model_data(str(temp_csv_path))
    
    mock_table_instance.add_row.assert_any_call(
        "gpt-test", 
        "[yellow]Cost data not found in LiteLLM[/yellow]", 
        "[green]Updated (False)[/green]", 
        "[grey]N/A (No LLM Data)[/grey]", 
        "[blue]Updated (Info)[/blue]"
    )
    mock_to_csv.assert_called_once()

def test_litellm_cost_missing_keys(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [
        {'provider': 'OpenAI', 'model': 'gpt-test', 'input': pd.NA, 'output': pd.NA},
        {'provider': 'Anthropic', 'model': 'claude-test', 'input': pd.NA, 'output': pd.NA}
    ]
    mock_df = create_base_df(mock_df_data)
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())
    mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001},
        'claude-test': {'output_cost_per_token': 0.000004}
    })
    mocker.patch("litellm.supports_response_schema", return_value=False)
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_table_instance = MagicMock(spec=Table)
    mocker.patch("pdd.update_model_costs.Table", return_value=mock_table_instance)

    update_model_data(str(temp_csv_path))

    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert pd.isna(gpt_row['output'])
    claude_row = called_df[called_df['model'] == 'claude-test'].iloc[0]
    assert pd.isna(claude_row['input'])
    assert claude_row['output'] == 4.0
    mock_table_instance.add_row.assert_any_call("gpt-test", "[green]Updated (Input: 1.0000)[/green]", ANY, ANY, ANY)
    mock_table_instance.add_row.assert_any_call("claude-test", "[green]Updated (Output: 4.0000)[/green]", ANY, ANY, ANY)

def test_litellm_structured_output_check_failure(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [
        {'provider': 'OpenAI', 'model': 'gpt-test', 'structured_output': pd.NA},
        {'provider': 'Anthropic', 'model': 'claude-test', 'structured_output': pd.NA}
    ]
    mock_df = create_base_df(mock_df_data)
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())
    mocker.patch("litellm.model_cost", {})
    def supports_schema_side_effect(model):
        if model == 'gpt-test': raise ValueError("Unknown model for schema check")
        elif model == 'claude-test': raise Exception("API error")
        return False
    mocker.patch("litellm.supports_response_schema", side_effect=supports_schema_side_effect)
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_table_instance = MagicMock(spec=Table)
    mocker.patch("pdd.update_model_costs.Table", return_value=mock_table_instance)

    update_model_data(str(temp_csv_path))
    mock_table_instance.add_row.assert_any_call("gpt-test", "[red]Skipped[/red]", "[red]Validation Failed: Unknown model for schema check[/red]", "[red]Skipped (Validation Failed)[/red]", "[red]Fail (Invalid/Unknown Model?)[/red]")
    mock_table_instance.add_row.assert_any_call("claude-test", "[red]Skipped[/red]", "[red]Check Error: API error[/red]", "[red]Skipped (Schema Check Error)[/red]", "[red]Fail (Schema Check Error)[/red]")
    mock_to_csv.assert_not_called()
    mock_console.print.assert_any_call("\n[bold blue]No schema changes or data updates needed. CSV file not saved.[/bold blue]")
    mock_console.print.assert_any_call("- Models with fetch/check errors: 2")

# 4. Mixed Scenarios
def test_csv_mix_of_missing_and_present_data(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [
        {'provider': 'OpenAI', 'model': 'gpt-needs-all', 'input': pd.NA, 'output': pd.NA, 'structured_output': pd.NA},
        {'provider': 'Anthropic', 'model': 'claude-needs-cost', 'input': pd.NA, 'output': 1.0, 'structured_output': 'True'},
        {'provider': 'Google', 'model': 'gemini-needs-struct', 'input': 2.0, 'output': 3.0, 'structured_output': pd.NA},
        {'provider': 'Mistral', 'model': 'mistral-complete', 'input': 4.0, 'output': 5.0, 'structured_output': 'False'},
        {'provider': 'Unknown', 'model': 'unknown-model', 'input': pd.NA, 'output': pd.NA, 'structured_output': pd.NA},
    ]
    mock_df = create_base_df(mock_df_data)
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())
    mocker.patch("litellm.model_cost", {
        'gpt-needs-all': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'claude-needs-cost': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004},
        'gemini-needs-struct': {'input_cost_per_token': 0.000002, 'output_cost_per_token': 0.000003},
        'mistral-complete': {'input_cost_per_token': 0.000004, 'output_cost_per_token': 0.000005},
    })
    def supports_schema_side_effect(model):
        if model == 'gpt-needs-all': return True
        if model == 'claude-needs-cost': return False 
        if model == 'gemini-needs-struct': return True
        if model == 'mistral-complete': return False
        if model == 'unknown-model': raise ValueError("Unknown model")
        return False
    mocker.patch("litellm.supports_response_schema", side_effect=supports_schema_side_effect)
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_table_instance = MagicMock(spec=Table)
    mocker.patch("pdd.update_model_costs.Table", return_value=mock_table_instance)

    update_model_data(str(temp_csv_path))

    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)
    gpt_row = called_df[called_df['model'] == 'gpt-needs-all'].iloc[0]
    assert gpt_row['input'] == 1.0; assert gpt_row['output'] == 2.0; assert gpt_row['structured_output'] is True
    claude_row = called_df[called_df['model'] == 'claude-needs-cost'].iloc[0]
    assert claude_row['input'] == 3.0; assert claude_row['output'] == 1.0; assert claude_row['structured_output'] is True 
    gemini_row = called_df[called_df['model'] == 'gemini-needs-struct'].iloc[0]
    assert gemini_row['input'] == 2.0; assert gemini_row['output'] == 3.0; assert gemini_row['structured_output'] is True
    mistral_row = called_df[called_df['model'] == 'mistral-complete'].iloc[0]
    assert mistral_row['input'] == 4.0; assert mistral_row['output'] == 5.0; assert mistral_row['structured_output'] is False
    unknown_row = called_df[called_df['model'] == 'unknown-model'].iloc[0]
    assert pd.isna(unknown_row['input']); assert pd.isna(unknown_row['output']); assert pd.isna(unknown_row['structured_output'])
    mock_table_instance.add_row.assert_any_call("gpt-needs-all", "[green]Updated (Input: 1.0000, Output: 2.0000)[/green]", "[green]Updated (True)[/green]", ANY, ANY)
    mock_table_instance.add_row.assert_any_call("claude-needs-cost", "[green]Updated (Input: 3.0000)[/green]", "Checked (Exists)", "[bold red]Mismatch! (Output (CSV: 1.0000, LLM: 4.0000))[/bold red]", ANY)
    mock_table_instance.add_row.assert_any_call("gemini-needs-struct", ANY, "[green]Updated (True)[/green]", "[green]Match (Input, Output)[/green]", ANY)
    mock_table_instance.add_row.assert_any_call("mistral-complete", ANY, "Checked (Exists)", "[green]Match (Input, Output)[/green]", ANY)
    mock_table_instance.add_row.assert_any_call("unknown-model", "[red]Skipped[/red]", "[red]Validation Failed: Unknown model[/red]", "[red]Skipped (Validation Failed)[/red]", "[red]Fail (Invalid/Unknown Model?)[/red]")
    mock_console.print.assert_any_call("- Models with cost mismatches: 1")
    mock_console.print.assert_any_call("- Models with fetch/check errors: 1")

def test_csv_with_missing_model_identifier(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [
        {'provider': 'OpenAI', 'model': 'gpt-test', 'input': pd.NA, 'output': pd.NA, 'structured_output': pd.NA},
        {'provider': 'Anthropic', 'model': pd.NA, 'input': 1.0, 'output': 2.0, 'structured_output': 'True'},
        {'provider': 'Google', 'model': 'gemini-test', 'input': 3.0, 'output': 4.0, 'structured_output': pd.NA},
    ]
    mock_df = create_base_df(mock_df_data)
    
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())
    mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'gemini-test': {'input_cost_per_token': 0.000003, 'output_cost_per_token': 0.000004},
    })
    mocker.patch("litellm.supports_response_schema", side_effect=lambda model: model == 'gpt-test')
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")
    mock_table_instance = MagicMock(spec=Table)
    mocker.patch("pdd.update_model_costs.Table", return_value=mock_table_instance)

    update_model_data(str(temp_csv_path))

    mock_to_csv.assert_called_once()
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0; assert gpt_row['output'] == 2.0; assert gpt_row['structured_output'] is True
    
    # The index for the Anthropic row in the original mock_df (which is 0-indexed)
    anthropic_row_index_in_mock_df = mock_df[mock_df['provider'] == 'Anthropic'].index[0]
    mock_console.print.assert_any_call(f"[yellow]Warning:[/yellow] Skipping row {anthropic_row_index_in_mock_df} due to missing model identifier.")
    
    gemini_row = called_df[called_df['model'] == 'gemini-test'].iloc[0]
    assert gemini_row['input'] == 3.0; assert gemini_row['output'] == 4.0; assert gemini_row['structured_output'] is False
    mock_table_instance.add_row.assert_any_call("gpt-test", "[green]Updated (Input: 1.0000, Output: 2.0000)[/green]", "[green]Updated (True)[/green]", ANY, ANY)
    mock_table_instance.add_row.assert_any_call("gemini-test", ANY, "[green]Updated (False)[/green]", "[green]Match (Input, Output)[/green]", ANY)

# 5. Output and Saving
def test_output_messages(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [
        {'provider': 'OpenAI', 'model': 'gpt-test', 'input': pd.NA, 'output': pd.NA, 'structured_output': pd.NA},
        {'provider': 'Anthropic', 'model': 'claude-test', 'input': 1.0, 'output': 2.0, 'structured_output': 'True'}
    ]
    mock_df = create_base_df(mock_df_data)
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())
    mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
        'claude-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
    })
    mocker.patch("litellm.supports_response_schema", return_value=True)
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    mock_console.print.assert_any_call(f"[bold blue]Starting model data update for:[/bold blue] {temp_csv_path}")
    mock_console.print.assert_any_call(f"[green]Successfully loaded:[/green] {temp_csv_path}")
    mock_console.print.assert_any_call("[green]Successfully fetched LiteLLM model cost data.[/green]")
    mock_console.print.assert_any_call("\n[bold blue]Processing models...[/bold blue]")
    mock_console.print.assert_any_call("- Models processed: 2")
    mock_console.print.assert_any_call("- Rows potentially updated (data changed): 1")
    mock_console.print.assert_any_call("- Models with fetch/check errors: 0")
    mock_console.print.assert_any_call("- Models with cost mismatches: 0")
    mock_console.print.assert_any_call(f"[bold green]Successfully saved updated data to:[/bold green] {temp_csv_path}")
    mock_console.print.assert_any_call(f"\n[bold yellow]Reminder:[/bold yellow] The '{'max_reasoning_tokens'}' column is not automatically updated by this script and requires manual maintenance.")
    mock_console.print.assert_any_call(f"[bold blue]Model data update process finished.[/bold blue]")

def test_save_no_updates(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [{'provider': 'OpenAI', 'model': 'gpt-test', 'input': 1.0, 'output': 2.0, 'structured_output': True}]
    mock_df = create_base_df(mock_df_data)
    
    mocker.patch("pandas.read_csv", return_value=mock_df.copy())
    mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
    })
    mocker.patch("litellm.supports_response_schema", return_value=True)
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    mock_to_csv.assert_not_called()
    mock_console.print.assert_any_call("\n[bold blue]No schema changes or data updates needed. CSV file not saved.[/bold blue]")

def test_save_with_updates(mocker, temp_csv_path, capsys_rich):
    mock_df_data = [{'provider': 'OpenAI', 'model': 'gpt-test', 'input': pd.NA, 'output': pd.NA, 'structured_output': pd.NA}]
    mock_df = create_base_df(mock_df_data)
    assert mock_df.loc[0, 'model'] == 'gpt-test'

    mocker.patch("pandas.read_csv", return_value=mock_df.copy())
    mocker.patch("litellm.model_cost", {
        'gpt-test': {'input_cost_per_token': 0.000001, 'output_cost_per_token': 0.000002},
    })
    mocker.patch("litellm.supports_response_schema", return_value=True) 
    mock_to_csv = mocker.patch("pandas.DataFrame.to_csv", autospec=True)
    mock_console = mocker.patch("pdd.update_model_costs.console")

    update_model_data(str(temp_csv_path))

    mock_to_csv.assert_called_once()
    assert mock_to_csv.call_args.args[1] == str(temp_csv_path)
    assert mock_to_csv.call_args.kwargs['index'] is False
    assert mock_to_csv.call_args.kwargs['na_rep'] == ''
    mock_console.print.assert_any_call(f"[bold green]Successfully saved updated data to:[/bold green] {temp_csv_path}")
    called_df = mock_to_csv.call_args.args[0]
    assert isinstance(called_df, pd.DataFrame)
    gpt_row = called_df[called_df['model'] == 'gpt-test'].iloc[0]
    assert gpt_row['input'] == 1.0
    assert gpt_row['output'] == 2.0
    assert gpt_row['structured_output'] is True

# 6. Main Function / Argument Parsing
def test_main_default_path(mocker, capsys_rich):
    mock_update = mocker.patch("pdd.update_model_costs.update_model_data")
    mocker.patch('sys.argv', ['update_model_costs.py']) # No --csv-path, uses default

    default_path_str = ".pdd/llm_model.csv" # Default path in argparse
    resolved_default_path_obj_str = str(Path(default_path_str).resolve())

    # Mock for Path.home() chain
    mock_home_dir_obj = MagicMock(spec=Path, name="mock_home_dir_obj")
    mock_home_pdd_dir_obj = MagicMock(spec=Path, name="mock_home_pdd_dir_obj")
    mock_user_config_file_obj = MagicMock(spec=Path, name="mock_user_config_file_obj")
    mock_home_dir_obj.__truediv__.return_value = mock_home_pdd_dir_obj
    mock_home_pdd_dir_obj.__truediv__.return_value = mock_user_config_file_obj
    mock_user_config_file_obj.is_file.return_value = False # User config does NOT exist

    # Mock for Path(args.csv_path) chain (args.csv_path will be default_path_str)
    mock_default_path_resolved_obj = MagicMock(spec=Path, name="mock_default_path_resolved_obj")
    mock_default_path_resolved_obj.parent.exists.return_value = True # Assume default dir exists
    mock_default_path_resolved_obj.__str__.return_value = resolved_default_path_obj_str

    mock_default_path_unresolved_obj = MagicMock(spec=Path, name="mock_default_path_unresolved_obj")
    mock_default_path_unresolved_obj.resolve.return_value = mock_default_path_resolved_obj
    
    # Mock Path class itself
    mock_path_class = mocker.patch("pdd.update_model_costs.Path", autospec=True)
    mock_path_class.home.return_value = mock_home_dir_obj
    # When Path(default_path_str) is called by main():
    mock_path_class.side_effect = lambda p: mock_default_path_unresolved_obj if p == default_path_str else MagicMock()


    mock_os_makedirs = mocker.patch('pdd.update_model_costs.os.makedirs')
    main()

    mock_update.assert_called_once_with(resolved_default_path_obj_str)
    mock_os_makedirs.assert_not_called() # Because parent.exists is True

def test_main_custom_path(mocker, capsys_rich):
    mock_update = mocker.patch("pdd.update_model_costs.update_model_data")
    
    custom_path_str = "custom/data/my_models.csv"
    resolved_custom_path_obj_str = str(Path(custom_path_str).resolve())
    custom_path_parent_str = str(Path(custom_path_str).parent)

    mocker.patch('sys.argv', ['update_model_costs.py', '--csv-path', custom_path_str])

    # Mock for Path.home() chain
    mock_home_dir_obj = MagicMock(spec=Path, name="mock_home_dir_obj")
    mock_home_pdd_dir_obj = MagicMock(spec=Path, name="mock_home_pdd_dir_obj")
    mock_user_config_file_obj = MagicMock(spec=Path, name="mock_user_config_file_obj")
    mock_home_dir_obj.__truediv__.return_value = mock_home_pdd_dir_obj
    mock_home_pdd_dir_obj.__truediv__.return_value = mock_user_config_file_obj
    mock_user_config_file_obj.is_file.return_value = False # User config does NOT exist

    # Mock for Path(args.csv_path) chain (args.csv_path will be custom_path_str)
    mock_custom_path_resolved_obj = MagicMock(spec=Path, name="mock_custom_path_resolved_obj")
    mock_custom_parent_dir_obj = MagicMock(spec=Path, name="mock_custom_parent_dir_obj")
    mock_custom_parent_dir_obj.exists.return_value = False # Custom dir does NOT exist
    mock_custom_parent_dir_obj.__str__.return_value = custom_path_parent_str
    mock_custom_path_resolved_obj.parent = mock_custom_parent_dir_obj
    mock_custom_path_resolved_obj.__str__.return_value = resolved_custom_path_obj_str
    
    mock_custom_path_unresolved_obj = MagicMock(spec=Path, name="mock_custom_path_unresolved_obj")
    mock_custom_path_unresolved_obj.resolve.return_value = mock_custom_path_resolved_obj

    # Mock Path class itself
    mock_path_class = mocker.patch("pdd.update_model_costs.Path", autospec=True)
    mock_path_class.home.return_value = mock_home_dir_obj
    # When Path(custom_path_str) is called by main():
    mock_path_class.side_effect = lambda p: mock_custom_path_unresolved_obj if p == Path(custom_path_str) or p == custom_path_str else MagicMock()


    mock_os_makedirs = mocker.patch('pdd.update_model_costs.os.makedirs')
    mock_console = mocker.patch("pdd.update_model_costs.console")
    main()

    mock_update.assert_called_once_with(resolved_custom_path_obj_str)
    mock_os_makedirs.assert_called_once_with(mock_custom_parent_dir_obj, exist_ok=True)
    mock_console.print.assert_any_call(f"[cyan]Created directory:[/cyan] {mock_custom_parent_dir_obj}")


def test_main_user_path_precedence(mocker, capsys_rich):
    mock_update = mocker.patch("pdd.update_model_costs.update_model_data")
    custom_path_arg_str = "custom/data/my_models.csv" # This will be ignored

    # Path.home() itself is not mocked here, we use real Path.home() to build the string
    # but the Path objects used by the SCRIPT will be mocked.
    user_path_obj_for_assertion = Path.home() / ".pdd" / "llm_model.csv"
    user_path_str_for_assertion = str(user_path_obj_for_assertion)

    mocker.patch('sys.argv', ['update_model_costs.py', '--csv-path', custom_path_arg_str])

    # Mock for Path.home() chain
    mock_home_dir_obj = MagicMock(spec=Path, name="mock_home_dir_obj")
    mock_home_pdd_dir_obj = MagicMock(spec=Path, name="mock_home_pdd_dir_obj")
    mock_user_config_file_obj = MagicMock(spec=Path, name="mock_user_config_file_obj")
    
    mock_home_dir_obj.__truediv__.return_value = mock_home_pdd_dir_obj
    mock_home_pdd_dir_obj.__truediv__.return_value = mock_user_config_file_obj
    
    mock_user_config_file_obj.is_file.return_value = True # User config DOES exist
    mock_user_config_file_obj.__str__.return_value = user_path_str_for_assertion # Critical for assertion

    # Mock for Path(args.csv_path) - not strictly needed to be fully configured if user path takes precedence
    mock_arg_path_unresolved_obj = MagicMock(spec=Path, name="mock_arg_path_unresolved_obj")
    # mock_arg_path_unresolved_obj.resolve.return_value = ... (not essential if this path isn't used)

    # Mock Path class itself
    mock_path_class = mocker.patch("pdd.update_model_costs.Path", autospec=True)
    mock_path_class.home.return_value = mock_home_dir_obj
    mock_path_class.return_value = mock_arg_path_unresolved_obj # For Path(custom_path_arg_str)

    mock_os_makedirs = mocker.patch('pdd.update_model_costs.os.makedirs')
    mock_console = mocker.patch("pdd.update_model_costs.console")
    main()

    mock_update.assert_called_once_with(user_path_str_for_assertion)
    mock_os_makedirs.assert_not_called() # Because user path is used, no dir creation for arg path
    mock_console.print.assert_any_call(f"[bold cyan]Found user-specific config, using:[/bold cyan] {mock_user_config_file_obj}")
