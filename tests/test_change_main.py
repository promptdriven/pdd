import pytest
import csv
import os
from pathlib import Path
from unittest.mock import MagicMock, patch
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
    mock_process_csv_change.return_value = (True, [{'file1.py': 'Modified content 1'}, {'file2.py': 'Modified content 2'}], 0.5, 'gpt-3.5-turbo')
    
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
    assert "Results saved successfully" in caplog.text
    assert "Returning success message for CSV mode" in caplog.text

    print("All assertions passed successfully.")