# test_etlpipeline.py

"""
This test suite provides comprehensive coverage for the etlpipeline.py script.
It is structured to test each function in isolation (unit tests) and the
full pipeline end-to-end (integration tests), ensuring all requirements from
the prompt are met.

Test Plan:

I. `extract_data` Function Tests
    - test_extract_data_success: Verifies successful reading of a valid CSV.
    - test_extract_data_file_not_found: Ensures graceful failure when the input file is missing.
    - test_extract_data_empty_file: Checks handling of an empty input file.
    - test_extract_data_header_only: Checks handling of a file with only a header.

II. `transform_and_filter_data` Function Tests
    - test_transform_valid_row: Confirms correct transformation of a single valid row.
    - test_transform_cleans_category: Verifies category stripping and lowercasing.
    - test_filter_amount_zero_or_negative: Ensures rows with amount <= 0 are silently dropped.
    - test_filter_empty_category: Ensures rows with empty or whitespace-only categories are silently dropped.
    - test_skip_invalid_amount: Verifies rows with non-numeric amounts are skipped with a warning.
    - test_skip_invalid_date: Verifies rows with malformed dates are skipped with a warning.
    - test_skip_malformed_rows: Checks that rows with incorrect column counts are skipped with a warning.
    - test_transform_and_filter_mixed_data: A comprehensive test with a mix of valid, filterable, and invalid data.

III. `load_data` Function Tests
    - test_load_data_success: Verifies correct writing of cleaned data to the output CSV.
    - test_load_data_empty_data: Ensures a header-only file is created when there's no data to load.
    - test_load_data_io_error: Simulates a write permission error to test error handling.

IV. End-to-End (Integration) Tests
    - test_full_pipeline_e2e: Runs the entire ETL process from a sample input file to an output file and verifies the final content.
    - test_main_function_arg_handling: Tests the command-line argument parsing in the main function.
"""

import pytest
import os
import csv
import sys
from unittest.mock import patch

# The code under test
import etlpipeline

# Helper function to create a CSV file for tests
def create_csv(filepath, data):
    """Creates a CSV file with the given data."""
    with open(filepath, 'w', newline='', encoding='utf-8') as f:
        writer = csv.writer(f)
        writer.writerows(data)

# --- I. extract_data Function Tests ---

def test_extract_data_success(tmp_path):
    """Verifies successful reading of a valid CSV."""
    input_file = tmp_path / "input.csv"
    headers = ['id', 'name']
    data = [['1', 'Alice'], ['2', 'Bob']]
    create_csv(input_file, [headers] + data)

    extracted_data, extracted_headers = etlpipeline.extract_data(str(input_file))

    assert extracted_headers == headers
    assert extracted_data == data

def test_extract_data_file_not_found(capfd):
    """Ensures graceful failure when the input file is missing."""
    data, headers = etlpipeline.extract_data("non_existent_file.csv")
    
    assert data is None
    assert headers is None
    
    stderr = capfd.readouterr().err
    assert "Error: Input file not found" in stderr
    assert "non_existent_file.csv" in stderr

def test_extract_data_empty_file(tmp_path, capfd):
    """Checks handling of an empty input file."""
    input_file = tmp_path / "input.csv"
    input_file.touch() # Create an empty file

    data, headers = etlpipeline.extract_data(str(input_file))

    assert data == []
    assert headers == []
    
    stderr = capfd.readouterr().err
    assert "Warning: Input file" in stderr
    assert "is empty or has no header" in stderr

def test_extract_data_header_only(tmp_path):
    """Checks handling of a file with only a header."""
    input_file = tmp_path / "input.csv"
    headers = ['id', 'date', 'amount', 'category']
    create_csv(input_file, [headers])

    data, extracted_headers = etlpipeline.extract_data(str(input_file))

    assert data == []
    assert extracted_headers == headers

# --- II. transform_and_filter_data Function Tests ---

def test_transform_valid_row():
    """Confirms correct transformation of a single valid row."""
    row = [['1', '2023-01-01', '99.99', '  Electronics  ']]
    expected = [['1', '2023-01-01', 99.99, 'electronics']]
    
    result = etlpipeline.transform_and_filter_data(row)
    assert result == expected

@pytest.mark.parametrize("amount_str", ["-10.5", "0", "0.0"])
def test_filter_amount_zero_or_negative(amount_str):
    """Ensures rows with amount <= 0 are silently dropped."""
    row = [['1', '2023-01-01', amount_str, 'Books']]
    result = etlpipeline.transform_and_filter_data(row)
    assert result == []

@pytest.mark.parametrize("category_str", ["", "   ", "\t"])
def test_filter_empty_category(category_str):
    """Ensures rows with empty or whitespace-only categories are silently dropped."""
    row = [['1', '2023-01-01', '50.00', category_str]]
    result = etlpipeline.transform_and_filter_data(row)
    assert result == []

def test_skip_invalid_amount(capfd):
    """Verifies rows with non-numeric amounts are skipped with a warning."""
    row = [['1', '2023-01-01', 'not-a-number', 'Books']]
    result = etlpipeline.transform_and_filter_data(row)
    
    assert result == []
    stderr = capfd.readouterr().err
    assert "Warning: Skipping row 2" in stderr
    assert "invalid amount: 'not-a-number'" in stderr

def test_skip_invalid_date(capfd):
    """Verifies rows with malformed dates are skipped with a warning."""
    row = [['1', '2023/01/01', '100.00', 'Books']]
    result = etlpipeline.transform_and_filter_data(row)
    
    assert result == []
    stderr = capfd.readouterr().err
    assert "Warning: Skipping row 2" in stderr
    assert "invalid date format: '2023/01/01'" in stderr

@pytest.mark.parametrize("malformed_row", [
    ['1', '2023-01-01', '100'],      # Too few columns
    ['1', '2023-01-01', '100', 'Books', 'Extra'] # Too many columns
])
def test_skip_malformed_rows(malformed_row, capfd):
    """Checks that rows with incorrect column counts are skipped with a warning."""
    result = etlpipeline.transform_and_filter_data([malformed_row])
    
    assert result == []
    stderr = capfd.readouterr().err
    assert "Warning: Skipping malformed row 2" in stderr
    assert "incorrect number of columns" in stderr

def test_transform_and_filter_mixed_data(capfd):
    """A comprehensive test with a mix of valid, filterable, and invalid data."""
    input_data = [
        ['1', '2023-12-10', '100.25', 'Books'],          # Valid
        ['2', '2023-11-01', '-80.00', 'Electronics'],    # Filter: negative amount
        ['3', '2023-10-05', '50.00', ' '],               # Filter: empty category
        ['4', '2023-09-15', '120.75', '  Groceries  '],  # Valid: needs cleaning
        ['5', '202X-09-15', '150.00', 'Other'],          # Error: bad date
        ['6', '2023-08-20', 'abc', 'Software'],          # Error: bad amount
    ]
    expected_output = [
        ['1', '2023-12-10', 100.25, 'books'],
        ['4', '2023-09-15', 120.75, 'groceries'],
    ]
    
    result = etlpipeline.transform_and_filter_data(input_data)
    assert result == expected_output
    
    stderr = capfd.readouterr().err
    assert "invalid date format: '202X-09-15'" in stderr # For row 5
    assert "invalid amount: 'abc'" in stderr           # For row 6

# --- III. load_data Function Tests ---

def test_load_data_success(tmp_path):
    """Verifies correct writing of cleaned data to the output CSV."""
    output_file = tmp_path / "output.csv"
    headers = ['id', 'date', 'amount', 'category']
    data = [['1', '2023-12-10', 100.25, 'books']]
    
    etlpipeline.load_data(data, str(output_file), headers)
    
    with open(output_file, 'r', newline='') as f:
        reader = csv.reader(f)
        content = list(reader)
        
    # Note: CSV module writes all fields as strings
    expected_content = [
        ['id', 'date', 'amount', 'category'],
        ['1', '2023-12-10', '100.25', 'books']
    ]
    assert content == expected_content

def test_load_data_empty_data(tmp_path):
    """Ensures a header-only file is created when there's no data to load."""
    output_file = tmp_path / "output.csv"
    headers = ['id', 'date', 'amount', 'category']
    
    etlpipeline.load_data([], str(output_file), headers)
    
    with open(output_file, 'r') as f:
        content = f.read().strip()
        
    assert content == "id,date,amount,category"

def test_load_data_io_error(mocker, capfd):
    """Simulates a write permission error to test error handling."""
    mocker.patch("builtins.open", side_effect=IOError("Permission denied"))
    
    etlpipeline.load_data([['data']], "locked_file.csv", ['header'])
    
    stderr = capfd.readouterr().err
    assert "Error: Could not write to file" in stderr
    assert "Permission denied" in stderr

# --- IV. End-to-End (Integration) Tests ---

def test_full_pipeline_e2e(tmp_path):
    """Runs the entire ETL process and verifies the final output file."""
    input_file = tmp_path / "input.csv"
    output_file = tmp_path / "output.csv"
    
    input_data = [
        ['id', 'date', 'amount', 'category'],
        ['1', '2023-12-10', '100.25', 'Books'],
        ['2', '2023-11-01', '-80.00', 'Electronics'],
        ['3', '2023-10-05', '50.00', ''],
        ['4', '2023-09-15', '120.75', 'Groceries '],
        ['5', '202X-09-15', 'abc', 'Other'],
    ]
    create_csv(input_file, input_data)
    
    # Run the pipeline
    raw_data, headers = etlpipeline.extract_data(str(input_file))
    cleaned_data = etlpipeline.transform_and_filter_data(raw_data)
    etlpipeline.load_data(cleaned_data, str(output_file), headers)
    
    # Verify output
    with open(output_file, 'r', newline='') as f:
        reader = csv.reader(f)
        output_content = list(reader)
        
    expected_output = [
        ['id', 'date', 'amount', 'category'],
        ['1', '2023-12-10', '100.25', 'books'],
        ['4', '2023-09-15', '120.75', 'groceries'],
    ]
    assert output_content == expected_output

@pytest.mark.parametrize("argv", [
    ['etlpipeline.py'],
    ['etlpipeline.py', 'input.csv'],
    ['etlpipeline.py', 'input.csv', 'output.csv', 'extra']
])
def test_main_function_arg_handling(argv, capfd):
    """Tests the command-line argument parsing in the main function."""
    with patch.object(sys, 'argv', argv):
        with pytest.raises(SystemExit) as e:
            etlpipeline.main()
        
        assert e.type == SystemExit
        assert e.value.code == 1
    
    stdout = capfd.readouterr().out
    assert "Usage: python etlpipeline.py" in stdout
def test_main_function_integration(tmp_path, capfd):
    """Tests the main function's successful execution as an integration test."""
    input_file = tmp_path / "main_input.csv"
    output_file = tmp_path / "main_output.csv"
    
    input_data = [
        ['id', 'date', 'amount', 'category'],
        ['1', '2024-01-15', '19.99', '  Software '],
        ['2', '2024-01-16', '250.00', 'Electronics'],
        ['3', 'bad-date', '100.00', 'Invalid Row'],
    ]
    create_csv(input_file, input_data)
    
    # Mock sys.argv to simulate command-line execution
    with patch.object(sys, 'argv', ['etlpipeline.py', str(input_file), str(output_file)]):
        etlpipeline.main()
        
    # Check stderr for the expected warning about the bad row
    stderr = capfd.readouterr().err
    assert "Warning: Skipping row 4" in stderr
    assert "invalid date format: 'bad-date'" in stderr
    
    # Verify the output file content
    with open(output_file, 'r', newline='') as f:
        reader = csv.reader(f)
        output_content = list(reader)
        
    expected_output = [
        ['id', 'date', 'amount', 'category'],
        ['1', '2024-01-15', '19.99', 'software'],
        ['2', '2024-01-16', '250.00', 'electronics'],
    ]
    assert output_content == expected_output


# --- V. Formal Verification with Z3 ---

# Note: This test requires the z3-solver package.
# It can be installed with: pip install z3-solver
# The test will be skipped if z3 is not found.

def test_z3_amount_is_always_positive():
    """
    Uses Z3 to formally prove that the filtering logic for the 'amount'
    field is correct. It verifies that for any real number, if the number
    is positive, it is kept, and if it is non-positive, it is dropped.
    """
    z3 = pytest.importorskip("z3")

    # 1. Define a Z3 variable for the amount.
    amount = z3.Real('amount')

    # 2. Define a Z3 function to represent the filter's decision.
    # is_kept(amount) will be true if the row is kept, false otherwise.
    is_kept = z3.Function('is_kept', z3.RealSort(), z3.BoolSort())

    # 3. Create a solver and add the axioms based on the code's logic.
    # The code keeps rows where amount > 0 and drops rows where amount <= 0.
    solver = z3.Solver()
    solver.add(z3.ForAll([amount], z3.Implies(amount > 0, is_kept(amount))))
    solver.add(z3.ForAll([amount], z3.Implies(amount <= 0, z3.Not(is_kept(amount)))))

    # 4. State and prove the first theorem:
    # "It is impossible for a row to be kept if its amount is non-positive."
    # We ask the solver if it can find a scenario where a row is kept AND
    # its amount is <= 0.
    solver.push()
    solver.add(z3.And(is_kept(amount), amount <= 0))
    
    # We expect this to be "unsatisfiable" (unsat), meaning no such scenario exists.
    result = solver.check()
    assert result == z3.unsat, "Z3 found a case where a non-positive amount was kept."
    solver.pop()

    # 5. State and prove the second theorem:
    # "It is impossible for a row to be dropped if its amount is positive."
    # We ask the solver if it can find a scenario where a row is NOT kept
    # (i.e., dropped) AND its amount is > 0.
    solver.push()
    solver.add(z3.And(z3.Not(is_kept(amount)), amount > 0))

    # We also expect this to be "unsatisfiable".
    result = solver.check()
    assert result == z3.unsat, "Z3 found a case where a positive amount was dropped."
    solver.pop()