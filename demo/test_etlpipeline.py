# test_etlpipeline.py

"""
This test suite provides comprehensive testing for the etlpipeline.py script.
The tests are designed to verify the script's functionality against the requirements
outlined in the original prompt, focusing on correctness, robustness, and error handling.
"""

# Test Plan
#
# 1. Formal Verification vs. Unit Tests Analysis
#
# The core logic of the ETL pipeline involves file I/O, data type conversions (string to float/datetime),
# and string manipulations.
#
# - Z3 (Formal Verification): Z3 is a theorem prover, best suited for verifying properties of
#   pure, mathematical, or logical functions. While we could model the filtering logic
#   (e.g., `amount > 0 AND category != ""`), it would be overly complex and provide little
#   benefit over unit tests. Key operations like file reading (`open`), CSV parsing (`csv.reader`),
#   date parsing (`datetime.strptime`), and float conversion (`float()`) are external dependencies
#   or built-in functions whose behavior we trust. Verifying our interaction with them is the
#   primary goal, which is a classic use case for unit and integration testing.
#
# - Unit Tests (Pytest): This approach is ideal for the given code. We can test each
#   function (`extract`, `transform`, `load`) in isolation to verify its specific logic,
#   and also perform end-to-end tests that simulate the real-world usage of the script.
#   Pytest's fixtures are perfect for managing temporary test files, and its `capsys` and
#   `caplog` fixtures allow us to assert that correct warnings and errors are printed to
#   stderr/stdout.
#
# Conclusion: A comprehensive suite of unit and integration tests using pytest is the most
# effective and practical approach for ensuring the correctness of this ETL script.
#
# 2. Detailed Test Strategy
#
# We will structure the tests to cover each component and the overall pipeline.
#
#   - Fixtures:
#     - A fixture will be used to create a temporary directory (`tmp_path`) for test files.
#     - A helper function or fixture will create the `input.csv` file with specified content
#       for each test, ensuring test isolation.
#
#   - Test Categories:
#
#     a) End-to-End Pipeline Tests:
#        - `test_full_pipeline_success`: Simulates running the script on a comprehensive
#          sample file. It will verify that valid rows are transformed correctly, invalid rows
#          are filtered/skipped, and the final `output.csv` matches the expected result exactly.
#          This test covers the main success path and multiple requirements simultaneously.
#        - `test_pipeline_with_no_valid_rows`: Ensures that if all rows are invalid or filtered,
#          the script produces an `output.csv` with only the header row.
#
#     b) `extract_data` Function Tests:
#        - `test_extract_nonexistent_file`: Verifies that the function returns `(None, None)`
#          and prints an error if the input file does not exist.
#        - `test_extract_empty_file`: Checks that an empty input file results in empty lists
#          for data and headers, along with a warning.
#        - `test_extract_header_only_file`: Ensures a file with only a header row is handled
#          correctly (empty data list, correct headers).
#
#     c) `transform_and_filter_data` Function Tests:
#        - `test_transform_valid_data`: Verifies correct transformation of amount (to float),
#          category (lowercase, stripped), and date (passed through).
#        - `test_transform_amount_filtering`: Specifically tests the `amount > 0` rule, ensuring
#          rows with zero or negative amounts are filtered out.
#        - `test_transform_category_filtering`: Specifically tests the category rule, ensuring
#          rows with empty or whitespace-only categories are filtered.
#        - `test_transform_data_validation_errors`: Checks that rows with malformed data
#          (invalid date, non-numeric amount, wrong column count) are skipped and that
#          appropriate warnings are printed to stderr for each case.
#
#     d) `load_data` Function Tests:
#        - `test_load_data_amount_formatting`: Crucially verifies that float amounts are
#          formatted to a string with exactly two decimal places in the output file (e.g.,
#          50.0 -> "50.00", 19.9 -> "19.90").
#        - `test_load_data_with_empty_input`: Confirms that calling `load_data` with an
#          empty list of cleaned data results in a file with only headers.
#
#     e) Command-Line Interface (CLI) Tests:
#        - `test_main_cli_invocation`: Uses `monkeypatch` to simulate command-line arguments
#          and runs the `main()` function to test the full CLI execution path.
#        - `test_main_cli_incorrect_args`: Verifies that the script exits with an error and
#          prints a usage message if called with the wrong number of arguments.

import pytest
import csv
import os
import sys
from io import StringIO

# Import the code to be tested
import etlpipeline

@pytest.fixture
def create_csv_file(tmp_path):
    """A pytest fixture to create a CSV file in a temporary directory."""
    def _create_csv(filename, data):
        file_path = tmp_path / filename
        with open(file_path, 'w', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            writer.writerows(data)
        return file_path
    return _create_csv

# --- End-to-End Pipeline Tests ---

def test_full_pipeline_success(create_csv_file, capsys):
    """
    Tests the full ETL pipeline from input file to output file with a mix of data.
    Verifies transformations, filtering, and output formatting.
    """
    input_data = [
        ['id', 'date', 'amount', 'category'],
        ['1', '2023-12-10', '100.25', 'Books'],          # Valid
        ['2', '2023-11-01', '-80.00', 'Electronics'],    # Filter: negative amount
        ['3', '2023-10-05', '50.00', ' '],               # Filter: empty category
        ['4', '2023-09-15', '120.75', '  Groceries  '],  # Valid: needs cleaning
        ['5', '202X-09-15', '150.00', 'Other'],          # Error: bad date
        ['6', '2023-08-20', 'abc', 'Software'],          # Error: non-numeric amount
        ['7', '2023-07-11', '25.5', 'Gifts'],            # Valid: amount needs formatting
        ['8', '2023-06-01', '0', 'Food']                 # Filter: zero amount
    ]
    expected_output = [
        ['id', 'date', 'amount', 'category'],
        ['1', '2023-12-10', '100.25', 'books'],
        ['4', '2023-09-15', '120.75', 'groceries'],
        ['7', '2023-07-11', '25.50', 'gifts']
    ]
    
    input_path = create_csv_file("input.csv", input_data)
    output_path = input_path.parent / "output.csv"

    # Run the main pipeline logic
    etlpipeline.main.__globals__['sys'].argv = ['etlpipeline.py', str(input_path), str(output_path)]
    etlpipeline.main()

    # Assert output file content
    with open(output_path, 'r', newline='', encoding='utf-8') as f:
        reader = csv.reader(f)
        actual_output = list(reader)
    
    assert actual_output == expected_output

    # Assert that warnings for skipped rows were printed to stderr
    captured = capsys.readouterr()
    assert "invalid date format: '202X-09-15'" in captured.err
    assert "invalid amount: 'abc'" in captured.err

def test_pipeline_with_no_valid_rows(create_csv_file):
    """
    Tests that an output file with only a header is created when no rows are valid.
    """
    input_data = [
        ['id', 'date', 'amount', 'category'],
        ['1', '2023-11-01', '-10.00', 'Electronics'],
        ['2', '2023-10-05', '50.00', ''],
        ['3', 'bad-date', '20.00', 'Books'],
    ]
    expected_output = [['id', 'date', 'amount', 'category']]
    
    input_path = create_csv_file("input.csv", input_data)
    output_path = input_path.parent / "output.csv"

    raw_data, headers = etlpipeline.extract_data(str(input_path))
    cleaned_data = etlpipeline.transform_and_filter_data(raw_data)
    etlpipeline.load_data(cleaned_data, str(output_path), headers)

    with open(output_path, 'r', newline='', encoding='utf-8') as f:
        reader = csv.reader(f)
        actual_output = list(reader)
        
    assert actual_output == expected_output

# --- `extract_data` Function Tests ---

def test_extract_nonexistent_file(capsys):
    """
    Verifies correct handling of a missing input file.
    """
    data, headers = etlpipeline.extract_data("nonexistent_file.csv")
    assert data is None
    assert headers is None
    captured = capsys.readouterr()
    assert "Error: Input file not found" in captured.err

def test_extract_empty_file(create_csv_file, capsys):
    """
    Verifies correct handling of an empty input file.
    """
    input_path = create_csv_file("input.csv", [])
    data, headers = etlpipeline.extract_data(str(input_path))
    assert data == []
    assert headers == []
    captured = capsys.readouterr()
    assert "Warning: Input file" in captured.err and "is empty" in captured.err

def test_extract_header_only_file(create_csv_file):
    """
    Verifies correct handling of a file with only a header row.
    """
    input_path = create_csv_file("input.csv", [['id', 'date', 'amount', 'category']])
    data, headers = etlpipeline.extract_data(str(input_path))
    assert data == []
    assert headers == ['id', 'date', 'amount', 'category']

# --- `transform_and_filter_data` Function Tests ---

def test_transform_and_filter_data_logic():
    """
    Tests the transformation and filtering logic in isolation.
    """
    input_rows = [
        ['1', '2023-12-10', '100.25', 'Books'],          # Valid
        ['2', '2023-11-01', '-80.00', 'Electronics'],    # Filter: negative amount
        ['3', '2023-10-05', '50.00', ' '],               # Filter: empty category
        ['4', '2023-09-15', '120.75', '  Groceries  '],  # Valid: needs cleaning
        ['7', '2023-07-11', '25.5', 'Gifts'],            # Valid
        ['8', '2023-06-01', '0.00', 'Food']              # Filter: zero amount
    ]
    
    expected_cleaned = [
        ['1', '2023-12-10', 100.25, 'books'],
        ['4', '2023-09-15', 120.75, 'groceries'],
        ['7', '2023-07-11', 25.5, 'gifts']
    ]

    cleaned_data = etlpipeline.transform_and_filter_data(input_rows)
    assert cleaned_data == expected_cleaned

def test_transform_data_validation_errors(capsys):
    """
    Tests that rows with validation errors are skipped and warnings are logged.
    """
    input_rows = [
        ['1', '202X-09-15', '150.00', 'Other'],          # Error: bad date
        ['2', '2023-08-20', 'abc', 'Software'],          # Error: non-numeric amount
        ['3', '2023-07-01', '10.00'],                    # Error: wrong column count
        ['4', '2023-06-01', '20.00', 'Valid', 'Extra']   # Error: wrong column count
    ]
    
    cleaned_data = etlpipeline.transform_and_filter_data(input_rows)
    assert cleaned_data == [] # No rows should be valid

    captured = capsys.readouterr()
    assert "invalid date format: '202X-09-15'" in captured.err
    assert "invalid amount: 'abc'" in captured.err
    assert "incorrect number of columns" in captured.err
    assert "['3', '2023-07-01', '10.00']" in captured.err
    assert "['4', '2023-06-01', '20.00', 'Valid', 'Extra']" in captured.err

# --- `load_data` Function Tests ---

def test_load_data_amount_formatting(tmp_path):
    """
    Verifies that the amount is formatted to a string with two decimal places.
    """
    headers = ['id', 'date', 'amount', 'category']
    cleaned_data = [
        ['1', '2023-01-01', 50.0, 'food'],      # Integer amount
        ['2', '2023-01-02', 19.9, 'gifts'],     # One decimal place
        ['3', '2023-01-03', 123.456, 'other']   # More than two decimal places
    ]
    expected_rows = [
        ['id', 'date', 'amount', 'category'],
        ['1', '2023-01-01', '50.00', 'food'],
        ['2', '2023-01-02', '19.90', 'gifts'],
        ['3', '2023-01-03', '123.46', 'other'] # Note: f-string formatting rounds
    ]

    output_path = tmp_path / "output.csv"
    etlpipeline.load_data(cleaned_data, str(output_path), headers)

    with open(output_path, 'r', newline='', encoding='utf-8') as f:
        reader = csv.reader(f)
        actual_rows = list(reader)
    
    assert actual_rows == expected_rows

# --- Command-Line Interface (CLI) Tests ---

def test_main_cli_incorrect_args(monkeypatch, capsys):
    """
    Verifies the script exits and shows usage with incorrect arguments.
    """
    # Simulate calling with too few arguments
    monkeypatch.setattr(sys, 'argv', ['etlpipeline.py', 'input.csv'])
    
    with pytest.raises(SystemExit) as e:
        etlpipeline.main()
    
    assert e.type == SystemExit
    assert e.value.code == 1

    captured = capsys.readouterr()
    assert "Usage: python etlpipeline.py <input_csv_path> <output_csv_path>" in captured.out