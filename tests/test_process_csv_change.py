# tests/test_process_csv_change.py

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

    success, list_of_jsons, total_cost, model_name = process_csv_change(
        csv_file, strength, temperature, code_directory, language, extension, budget
    )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    captured = capsys.readouterr()
    assert f"CSV file '{csv_file}' does not exist." in captured.out

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

    # Mock os.path.isfile to return True for the CSV file
    with patch("os.path.isfile", return_value=True):
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, strength, temperature, code_directory, language, extension, budget
        )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    captured = capsys.readouterr()
    assert f"'strength' must be between 0 and 1. Given: {strength}" in captured.out

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

    # Mock os.path.isfile to return True for the CSV file
    with patch("os.path.isfile", return_value=True):
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, strength, temperature, code_directory, language, extension, budget
        )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    captured = capsys.readouterr()
    assert f"'temperature' must be between 0 and 1. Given: {temperature}" in captured.out

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

    # Mock os.path.isfile and Path(code_directory).is_dir()
    with patch("os.path.isfile", return_value=True), \
         patch("pathlib.Path.is_dir", return_value=False):
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, strength, temperature, code_directory, language, extension, budget
        )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    captured = capsys.readouterr()
    assert f"Code directory '{code_directory}' does not exist or is not a directory." in captured.out

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

    # Mock os.path.isfile and open the CSV without required columns
    with patch("os.path.isfile", return_value=True), \
         patch("builtins.open", mock_open(read_data="wrong_column1,wrong_column2\nvalue1,value2")):
        success, list_of_jsons, total_cost, model_name = process_csv_change(
            csv_file, strength, temperature, code_directory, language, extension, budget
        )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    captured = capsys.readouterr()
    assert "CSV file must contain 'prompt_name' and 'change_instructions' columns." in captured.out

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

    # Mock os.path.isfile and open the CSV with missing 'prompt_name' in one row
    csv_content = "prompt_name,change_instructions\n,Modify the function\nvalid_prompt.py,Change the output"
    with patch("os.path.isfile", return_value=True), \
         patch("pathlib.Path.is_dir", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):
        
        # Mock the existence of prompt and code files
        with patch("pathlib.Path.is_file", return_value=True), \
             patch("builtins.open", mock_open(read_data="prompt content")) as mocked_file, \
             patch("pdd.process_csv_change.Path.read_text", return_value="prompt content"), \
             patch("pdd.process_csv_change.change", return_value=("modified prompt", 1.0, "model_v1")):
            
            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    assert not success
    assert list_of_jsons == [{"file_name": "valid_prompt.py", "modified_prompt": "modified prompt"}]
    assert total_cost == 1.0
    assert model_name == "model_v1"
    captured = capsys.readouterr()
    assert "Missing 'prompt_name' in row 1. Skipping." in captured.out
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

    # Mock os.path.isfile and open the CSV with missing 'change_instructions' in one row
    csv_content = "prompt_name,change_instructions\nvalid_prompt.py,\nvalid_prompt.py,Change the output"
    with patch("os.path.isfile", return_value=True), \
         patch("pathlib.Path.is_dir", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):
        
        # Mock the existence of prompt and code files
        with patch("pathlib.Path.is_file", return_value=True), \
             patch("builtins.open", mock_open(read_data="prompt content")) as mocked_file, \
             patch("pdd.process_csv_change.Path.read_text", return_value="prompt content"), \
             patch("pdd.process_csv_change.change", return_value=("modified prompt", 1.0, "model_v1")):
            
            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    assert not success
    assert list_of_jsons == [{"file_name": "valid_prompt.py", "modified_prompt": "modified prompt"}]
    assert total_cost == 1.0
    assert model_name == "model_v1"
    captured = capsys.readouterr()
    assert "Missing 'change_instructions' in row 1. Skipping." in captured.out
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

    with patch("os.path.isfile", return_value=True), \
         patch("pathlib.Path.is_dir", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):
        
        # Mock Path.is_file to return False for the code file
        with patch("pathlib.Path.is_file", side_effect=lambda x: False if "valid_prompt.py" in x else True):
            
            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    captured = capsys.readouterr()
    expected_warning = "Input code file '/path/to/code/valid_prompt.py' does not exist. Skipping row 1."
    assert expected_warning in captured.out

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

    with patch("os.path.isfile", return_value=True), \
         patch("pathlib.Path.is_dir", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):
        
        # Mock Path.is_file to return False for the prompt file
        with patch("pathlib.Path.is_file", side_effect=lambda x: False if "valid_prompt_language.prompt" in x else True):
            
            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    captured = capsys.readouterr()
    expected_warning = "Prompt file 'valid_prompt_language.prompt' does not exist. Skipping row 1."
    assert expected_warning in captured.out

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

    with patch("os.path.isfile", return_value=True), \
         patch("pathlib.Path.is_dir", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):
        
        # Mock Path.is_file to return True for all files
        with patch("pathlib.Path.is_file", return_value=True), \
             patch("builtins.open", mock_open(read_data="prompt content")), \
             patch("pdd.process_csv_change.change", side_effect=[
                 ("modified prompt 1", 1.0, "model_v1"),
                 ("modified prompt 2", 1.5, "model_v1"),
                 ("modified prompt 3", 1.0, "model_v1")
             ]):

            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    # Only first two changes should be processed (total_cost = 2.5 > budget)
    assert not success
    assert list_of_jsons == [
        {"file_name": "prompt1.py", "modified_prompt": "modified prompt 1"},
        {"file_name": "prompt2.py", "modified_prompt": "modified prompt 2"}
    ]
    assert total_cost == 2.5
    assert model_name == "model_v1"
    captured = capsys.readouterr()
    assert "Budget exceeded after row 2. Stopping further processing." in captured.out

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

    with patch("os.path.isfile", return_value=True), \
         patch("pathlib.Path.is_dir", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):
        
        # Mock Path.is_file to return True for all files
        with patch("pathlib.Path.is_file", return_value=True), \
             patch("builtins.open", mock_open(read_data="prompt content")), \
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

    with patch("os.path.isfile", return_value=True), \
         patch("pathlib.Path.is_dir", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):
        
        # Mock Path.is_file to return True for all files
        with patch("pathlib.Path.is_file", return_value=True), \
             patch("builtins.open", mock_open(read_data="prompt content")), \
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
    assert model_name == "model_v1"  # The first model name should be set
    captured = capsys.readouterr()
    assert "Model name changed from 'model_v1' to 'model_v2' in row 2." in captured.out

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

    with patch("os.path.isfile", return_value=True), \
         patch("pathlib.Path.is_dir", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):
        
        # Mock Path.is_file to return True for all files
        with patch("pathlib.Path.is_file", return_value=True), \
             patch("builtins.open", mock_open(read_data="prompt content")), \
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
    assert "Failed to apply change in row 2: Change function failed" in captured.out

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

    with patch("os.path.isfile", return_value=True), \
         patch("pathlib.Path.is_dir", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):
        
        # Mock Path.is_file to raise an unexpected exception
        with patch("pathlib.Path.is_file", side_effect=Exception("Unexpected error")):

            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )

    assert not success
    assert list_of_jsons == []
    assert total_cost == 0.0
    assert model_name == ""
    captured = capsys.readouterr()
    assert "Unexpected Error: Unexpected error" in captured.out

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

    with patch("os.path.isfile", return_value=True), \
         patch("pathlib.Path.is_dir", return_value=True), \
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

    csv_content = """
prompt_name,change_instructions
prompt1_language.prompt,Change 1
prompt2_language.prompt,Change 2
prompt3_language.prompt,Change 3
""".strip()

    with patch("os.path.isfile", return_value=True), \
         patch("pathlib.Path.is_dir", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):
        
        # Mock all necessary file checks and reads
        with patch("pathlib.Path.is_file", return_value=True), \
             patch("builtins.open", mock_open(read_data="prompt content")), \
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

def test_relative_imports(mock_change, capsys, tmp_path):
    """
    Test that the function correctly handles relative imports when used within a package.
    This test ensures that the module can be imported and used correctly.
    """
    # This test assumes that 'process_csv_change' is part of a package and uses relative imports.
    # Since we've already imported 'process_csv_change' at the top, this test can ensure that
    # the function can be called without import errors.
    csv_file = "valid.csv"
    strength = 0.5
    temperature = 0.5
    code_directory = "/path/to/code"
    language = "python"
    extension = ".py"
    budget = 10.0

    csv_content = "prompt_name,change_instructions\nprompt1_language.prompt,Change 1"

    with patch("os.path.isfile", return_value=True), \
         patch("pathlib.Path.is_dir", return_value=True), \
         patch("builtins.open", mock_open(read_data=csv_content)):
        
        # Mock all necessary file checks and reads
        with patch("pathlib.Path.is_file", return_value=True), \
             patch("builtins.open", mock_open(read_data="prompt content")), \
             patch("pdd.process_csv_change.change", return_value=("modified prompt", 1.0, "model_v1")):
            
            # Call the function
            success, list_of_jsons, total_cost, model_name = process_csv_change(
                csv_file, strength, temperature, code_directory, language, extension, budget
            )
    
    # Assertions
    assert success
    assert list_of_jsons == [{"file_name": "prompt1.py", "modified_prompt": "modified prompt"}]
    assert total_cost == 1.0
    assert model_name == "model_v1"
    captured = capsys.readouterr()
    assert "Row 1 processed successfully." in captured.out
    assert "Processing Complete" in captured.out
