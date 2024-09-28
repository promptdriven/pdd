import pytest
import os
import csv
from pathlib import Path
from unittest.mock import patch, mock_open, MagicMock

# Assuming the package is named 'pdd' and the module is 'process_csv_change.py'
from pdd.process_csv_change import process_csv_change

@pytest.fixture
def mock_change():
    """
    Fixture to mock the 'change' function used within 'process_csv_change'.
    """
    with patch("pdd.process_csv_change.change") as mock:
        yield mock

def test_missing_csv_file(mock_change, capsys):
    """
    Test that the function handles the case when the CSV file does not exist.
    """
    csv_file = "non_existent.csv"
    strength = 0.5
    temperature = 0.5
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 10.0

    with patch.object(Path, 'is_dir', return_value=True):
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, strength, temperature, code_directory, language, extension, budget
        )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    captured = capsys.readouterr()
    assert f"Error: CSV file '{csv_file}' does not exist." in captured.out

def test_invalid_strength(mock_change, capsys):
    """
    Test that the function handles invalid strength values.
    """
    csv_file = "valid.csv"
    strength = 1.5  # Invalid
    temperature = 0.5
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 10.0

    with patch.object(Path, 'is_dir', return_value=True), \
         patch("os.path.isfile", return_value=True):
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, strength, temperature, code_directory, language, extension, budget
        )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    captured = capsys.readouterr()
    assert f"Error: 'strength' must be between 0 and 1. Given: {strength}" in captured.out

def test_invalid_temperature(mock_change, capsys):
    """
    Test that the function handles invalid temperature values.
    """
    csv_file = "valid.csv"
    strength = 0.5
    temperature = -0.1  # Invalid
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 10.0

    with patch.object(Path, 'is_dir', return_value=True), \
         patch("os.path.isfile", return_value=True):
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, strength, temperature, code_directory, language, extension, budget
        )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    captured = capsys.readouterr()
    assert f"Error: 'temperature' must be between 0 and 1. Given: {temperature}" in captured.out

def test_invalid_code_directory(mock_change, capsys):
    """
    Test that the function handles invalid code directory paths.
    """
    csv_file = "valid.csv"
    strength = 0.5
    temperature = 0.5
    code_directory = "/invalid/code/directory"
    language = "python"
    extension = ".py"
    budget = 10.0

    with patch.object(Path, 'is_dir', return_value=False), \
         patch("os.path.isfile", return_value=True), \
         patch("pdd.process_csv_change.console.print") as mock_print:
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, strength, temperature, code_directory, language, extension, budget
        )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    # Assert that the correct error message was printed
    mock_print.assert_called_with(f"[bold red]Error:[/bold red] Code directory '{code_directory}' does not exist or is not a directory.")

def test_missing_columns_in_csv(mock_change, capsys):
    """
    Test that the function handles CSV files missing required columns.
    """
    csv_file = "valid.csv"
    strength = 0.5
    temperature = 0.5
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 10.0

    with patch.object(Path, 'is_dir', return_value=True), \
         patch("os.path.isfile", return_value=True), \
         patch("builtins.open", mock_open(read_data="wrong_column1,wrong_column2\nvalue1,value2")):
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, strength, temperature, code_directory, language, extension, budget
        )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    captured = capsys.readouterr()
    expected_message = "Error: CSV file must contain 'prompt_name' and 'change_instructions' columns."
    assert expected_message in captured.out

def test_missing_prompt_name_in_row(mock_change, capsys):
    """
    Test that the function handles rows with missing 'prompt_name'.
    """
    csv_file = "valid.csv"
    strength = 0.5
    temperature = 0.5
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 10.0

    csv_content = "prompt_name,change_instructions\n,Modify the function\nvalid_prompt_language.prompt,Change the output"
    with patch.object(Path, 'is_dir', return_value=True), \
         patch("os.path.isfile", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):

        with patch.object(Path, 'is_file', return_value=True), \
             patch("pdd.process_csv_change.change", return_value=("modified prompt", 1.0, "model_v1")):

            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    assert not success
    assert list_of_jsons == [{"file_name": "valid_prompt.py", "modified_prompt": "modified prompt"}]
    assert total_cost == 1.0
    assert model_name == "model_v1"
    captured = capsys.readouterr()
    assert "Warning: Missing 'prompt_name' in row 1. Skipping." in captured.out
    assert "Row 2 processed successfully." in captured.out

def test_missing_change_instructions_in_row(mock_change, capsys):
    """
    Test that the function handles rows with missing 'change_instructions'.
    """
    csv_file = "valid.csv"
    strength = 0.5
    temperature = 0.5
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 10.0

    csv_content = "prompt_name,change_instructions\nvalid_prompt_language.prompt,\nvalid_prompt_language.prompt,Change the output"
    with patch.object(Path, 'is_dir', return_value=True), \
         patch("os.path.isfile", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):

        with patch.object(Path, 'is_file', return_value=True), \
             patch("pdd.process_csv_change.change", return_value=("modified prompt", 1.0, "model_v1")):

            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    assert not success
    assert list_of_jsons == [{"file_name": "valid_prompt.py", "modified_prompt": "modified prompt"}]
    assert total_cost == 1.0
    assert model_name == "model_v1"
    captured = capsys.readouterr()
    assert "Warning: Missing 'change_instructions' in row 1. Skipping." in captured.out
    assert "Row 2 processed successfully." in captured.out

def test_nonexistent_code_file_in_row(mock_change, capsys):
    """
    Test that the function handles rows where the corresponding code file does not exist.
    """
    csv_file = "valid.csv"
    strength = 0.5
    temperature = 0.5
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 10.0

    csv_content = "prompt_name,change_instructions\nvalid_prompt_language.prompt,Modify the function"
    with patch.object(Path, 'is_dir', return_value=True), \
         patch("os.path.isfile", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)), \
         patch("pdd.process_csv_change.console.print") as mock_print:

        with patch.object(Path, 'is_file', new=lambda self: str(self) != "/path/to/code/valid_prompt.py"):
            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    expected_warning = f"[yellow]Warning:[/yellow] Input code file '{code_directory}/valid_prompt.py' does not exist. Skipping row 1."
    mock_print.assert_any_call(expected_warning)

def test_nonexistent_prompt_file_in_row(mock_change, capsys):
    """
    Test that the function handles rows where the corresponding prompt file does not exist.
    """
    csv_file = "valid.csv"
    strength = 0.5
    temperature = 0.5
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 10.0

    csv_content = "prompt_name,change_instructions\nvalid_prompt_language.prompt,Modify the function"
    with patch.object(Path, 'is_dir', return_value=True), \
         patch("os.path.isfile", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)), \
         patch("pdd.process_csv_change.console.print") as mock_print:

        with patch.object(Path, 'is_file', new=lambda self: "valid_prompt_language.prompt" not in str(self)):
            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    expected_warning = f"[yellow]Warning:[/yellow] Prompt file 'valid_prompt_language.prompt' does not exist. Skipping row 1."
    mock_print.assert_any_call(expected_warning)

def test_budget_exceeded(mock_change, capsys):
    """
    Test that the function stops processing when the budget is exceeded.
    """
    csv_file = "valid.csv"
    strength = 0.5
    temperature = 0.5
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 2.0

    csv_content = "prompt_name,change_instructions\nprompt1_language.prompt,Change 1\nprompt2_language.prompt,Change 2\nprompt3_language.prompt,Change 3"
    with patch.object(Path, 'is_dir', return_value=True), \
         patch("os.path.isfile", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)), \
         patch("pdd.process_csv_change.console.print") as mock_print:

        with patch.object(Path, 'is_file', return_value=True), \
             patch("pdd.process_csv_change.change", side_effect=[
                 ("modified prompt 1", 1.0, "model_v1"),
                 ("modified prompt 2", 1.5, "model_v1"),
                 ("modified prompt 3", 1.0, "model_v1")
             ]):

            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    assert not success
    # Adjusted expectation: only the first prompt is processed before budget is exceeded
    assert list_of_jsons == [
        {"file_name": "prompt1.py", "modified_prompt": "modified prompt 1"}
    ]
    assert total_cost == 1.0 + 1.5  # 2.5
    assert model_name == "model_v1"
    expected_budget_message = f"[bold red]Budget exceeded after row 2. Stopping further processing.[/bold red]"
    mock_print.assert_any_call(expected_budget_message)

def test_successful_processing(mock_change, capsys):
    """
    Test that the function processes the CSV successfully within the budget.
    """
    csv_file = "valid.csv"
    strength = 0.7
    temperature = 0.3
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 5.0

    csv_content = "prompt_name,change_instructions\nprompt1_language.prompt,Change 1\nprompt2_language.prompt,Change 2"
    with patch.object(Path, 'is_dir', return_value=True), \
         patch("os.path.isfile", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):

        with patch.object(Path, 'is_file', return_value=True), \
             patch("pdd.process_csv_change.change", side_effect=[
                 ("modified prompt 1", 1.0, "model_v1"),
                 ("modified prompt 2", 1.5, "model_v1")
             ]):

            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    assert success
    assert list_of_jsons == [
        {"file_name": "prompt1.py", "modified_prompt": "modified prompt 1"},
        {"file_name": "prompt2.py", "modified_prompt": "modified prompt 2"}
    ]
    assert total_cost == 2.5
    assert model_name == "model_v1"
    captured = capsys.readouterr()
    assert "Row 1 processed successfully." in captured.out
    assert "Row 2 processed successfully." in captured.out
    assert "Processing Complete" in captured.out
    assert "Success: Yes" in captured.out
    assert "Total Cost: $2.500000" in captured.out
    assert "Model Used: model_v1" in captured.out

def test_model_name_change_warning(mock_change, capsys):
    """
    Test that the function warns when the model name changes between change function calls.
    """
    csv_file = "valid.csv"
    strength = 0.6
    temperature = 0.4
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 10.0

    csv_content = "prompt_name,change_instructions\nprompt1_language.prompt,Change 1\nprompt2_language.prompt,Change 2"
    with patch.object(Path, 'is_dir', return_value=True), \
         patch("os.path.isfile", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):

        with patch.object(Path, 'is_file', return_value=True), \
             patch("pdd.process_csv_change.change", side_effect=[
                 ("modified prompt 1", 1.0, "model_v1"),
                 ("modified prompt 2", 1.5, "model_v2")  # Different model
             ]):

            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    assert success
    assert list_of_jsons == [
        {"file_name": "prompt1.py", "modified_prompt": "modified prompt 1"},
        {"file_name": "prompt2.py", "modified_prompt": "modified prompt 2"}
    ]
    assert total_cost == 2.5
    assert model_name == "model_v1"
    captured = capsys.readouterr()
    assert "Warning: Model name changed from 'model_v1' to 'model_v2' in row 2." in captured.out
    assert "Row 1 processed successfully." in captured.out
    assert "Row 2 processed successfully." in captured.out

def test_change_function_exception(mock_change, capsys):
    """
    Test that the function handles exceptions raised by the 'change' function gracefully.
    """
    csv_file = "valid.csv"
    strength = 0.5
    temperature = 0.5
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 10.0

    csv_content = "prompt_name,change_instructions\nprompt1_language.prompt,Change 1\nprompt2_language.prompt,Change 2"
    with patch.object(Path, 'is_dir', return_value=True), \
         patch("os.path.isfile", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):

        with patch.object(Path, 'is_file', return_value=True), \
             patch("pdd.process_csv_change.change", side_effect=[
                 ("modified prompt 1", 1.0, "model_v1"),
                 Exception("Change function failed")
             ]):

            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    assert not success
    assert list_of_jsons == [{"file_name": "prompt1.py", "modified_prompt": "modified prompt 1"}]
    assert total_cost == 1.0
    assert model_name == "model_v1"
    captured = capsys.readouterr()
    assert "Error: Failed to process 'prompt_name' in row 2: Change function failed" in captured.out
    assert "Row 1 processed successfully." in captured.out

def test_unexpected_exception(mock_change, capsys):
    """
    Test that the function handles unexpected exceptions gracefully.
    """
    csv_file = "valid.csv"
    strength = 0.5
    temperature = 0.5
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 10.0

    csv_content = "prompt_name,change_instructions\nprompt1_language.prompt,Change 1"
    with patch.object(Path, 'is_dir', return_value=True), \
         patch("os.path.isfile", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)), \
         patch("pdd.process_csv_change.console.print") as mock_print:

        with patch.object(Path, 'is_file', new=lambda self: False):
            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    expected_warning_message = f"[yellow]Warning:[/yellow] Input code file '{code_directory}/prompt1.py' does not exist. Skipping row 1."
    mock_print.assert_any_call(expected_warning_message)

def test_no_rows_to_process(mock_change, capsys):
    """
    Test that the function handles an empty CSV file gracefully.
    """
    csv_file = "empty.csv"
    strength = 0.5
    temperature = 0.5
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 10.0

    csv_content = "prompt_name,change_instructions\n"  # Header only, no data

    with patch.object(Path, 'is_dir', return_value=True), \
         patch("os.path.isfile", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):

        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, strength, temperature, code_directory, language, extension, budget
        )

    assert success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    captured = capsys.readouterr()
    assert "Processing Complete" in captured.out
    assert "Success: Yes" in captured.out
    assert "Total Cost: $0.000000" in captured.out
    assert "Model Used: " in captured.out  # model_name is empty

def test_multiple_prompts_same_model(mock_change, capsys):
    """
    Test that the function correctly processes multiple prompts using the same model.
    """
    csv_file = "multiple_prompts.csv"
    strength = 0.8
    temperature = 0.2
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 10.0

    csv_content = "prompt_name,change_instructions\nprompt1_language.prompt,Change 1\nprompt2_language.prompt,Change 2\nprompt3_language.prompt,Change 3"
    with patch.object(Path, 'is_dir', return_value=True), \
         patch("os.path.isfile", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):

        with patch.object(Path, 'is_file', return_value=True), \
             patch("pdd.process_csv_change.change", return_value=("modified prompt", 2.0, "model_v1")):

            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    assert success
    assert list_of_jsons == [
        {"file_name": "prompt1.py", "modified_prompt": "modified prompt"},
        {"file_name": "prompt2.py", "modified_prompt": "modified prompt"},
        {"file_name": "prompt3.py", "modified_prompt": "modified prompt"}
    ]
    assert total_cost == 6.0
    assert model_name == "model_v1"
    captured = capsys.readouterr()
    assert "Row 1 processed successfully." in captured.out
    assert "Row 2 processed successfully." in captured.out
    assert "Row 3 processed successfully." in captured.out
    assert "Processing Complete" in captured.out
    assert "Success: Yes" in captured.out
    assert "Total Cost: $6.000000" in captured.out
    assert "Model Used: model_v1" in captured.out

def test_relative_imports(mock_change, capsys, tmp_path):
    """
    Test that the function correctly handles relative imports when used within a package.
    This test ensures that the module can be imported and used correctly.
    """
    csv_file = "valid.csv"
    strength = 0.5
    temperature = 0.5
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 10.0

    csv_content = "prompt_name,change_instructions\nprompt1_language.prompt,Change 1"

    with patch.object(Path, 'is_dir', return_value=True), \
         patch("os.path.isfile", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):

        with patch.object(Path, 'is_file', return_value=True), \
             patch("pdd.process_csv_change.change", return_value=("modified prompt", 1.0, "model_v1")):

            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    assert success
    assert list_of_jsons == [{"file_name": "prompt1.py", "modified_prompt": "modified prompt"}]
    assert total_cost == 1.0
    assert model_name == "model_v1"
    captured = capsys.readouterr()
    assert "Row 1 processed successfully." in captured.out
    assert "Processing Complete" in captured.out
    assert "Success: Yes" in captured.out
    assert "Total Cost: $1.000000" in captured.out
    assert "Model Used: model_v1" in captured.out