import pytest
import csv
import os
from pathlib import Path
from unittest.mock import MagicMock
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
    prompt1.write_text("Modify the function to handle overflow errors.")
    
    prompt2 = code_directory / "script2_python.prompt"
    prompt2.write_text("Optimize the function for large integers.")
    
    # Create batch_changes.csv
    batch_changes_csv = tmp_path / "batch_changes.csv"
    batch_changes_csv.write_text("prompt_name,change_instructions\n")
    batch_changes_csv.write_text(f"{prompt1},Modify the function to handle overflow errors.\n")
    batch_changes_csv.write_text(f"{prompt2},Optimize the function for large integers.\n")
    
    # Define the output file
    batch_output_file = tmp_path / "batch_modified_prompts.csv"
    
    # Prepare the expected correct_batch.csv content
    correct_batch_csv = tmp_path / "correct_batch.csv"
    correct_batch_csv.write_text("file_name,modified_prompt\n")
    correct_batch_csv.write_text(f"{prompt1},Modified function to handle overflow errors.\n")
    correct_batch_csv.write_text(f"{prompt2},Optimized function for large integers.\n")
    
    return {
        "code_directory": str(code_directory),
        "batch_changes_csv": str(batch_changes_csv),
        "batch_output_file": str(batch_output_file),
        "correct_batch_csv": str(correct_batch_csv)
    }

def test_change_main_batch_mode(setup_environment, monkeypatch):
    """
    Tests the `change_main` function in CSV batch-change mode by comparing the generated
    output with the expected correct output.
    """
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
    
    # Mock the process_csv_change function if necessary
    # For this example, we'll assume it works correctly and does not need to be mocked.
    # If the actual implementation interacts with external services, consider mocking it here.
    
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
    
    # Read the generated output CSV
    generated_output = {}
    with open(env["batch_output_file"], mode='r', newline='', encoding='utf-8') as csvfile:
        reader = csv.DictReader(csvfile)
        for row in reader:
            generated_output[row['file_name']] = row['modified_prompt']
    
    # Read the expected correct CSV
    expected_output = {}
    with open(env["correct_batch_csv"], mode='r', newline='', encoding='utf-8') as csvfile:
        reader = csv.DictReader(csvfile)
        for row in reader:
            expected_output[row['file_name']] = row['modified_prompt']
    
    # Compare the generated output with the expected output
    assert generated_output == expected_output, (
        f"Generated output does not match expected output.\n"
        f"Expected: {expected_output}\n"
        f"Got: {generated_output}"
    )
    
    # Optionally, assert that the total_cost and model_name meet certain criteria
    assert total_cost > 0, "Total cost should be greater than zero."
    assert model_name != "", "Model name should not be empty."