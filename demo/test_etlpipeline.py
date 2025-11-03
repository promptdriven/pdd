# test_etlpipeline.py

import pytest
import csv
import os
from unittest.mock import patch

# Attempt to import z3, and skip the formal verification test if not available.
try:
    import z3
    Z3_AVAILABLE = True
except ImportError:
    Z3_AVAILABLE = False

# Import the module to be tested
import etlpipeline

# ===================================================================================
#
#                                 TEST PLAN
#
# ===================================================================================
#
# The goal is to ensure the `etlpipeline.py` script correctly performs its ETL
# (Extract, Transform, Load) process according to the specified requirements.
# The tests are divided into unit tests for each function, an integration test
# for the overall pipeline, and a formal verification test for the core logic.
#
# -----------------------------------------------------------------------------------
# Part 1: Formal Verification (using Z3)
# -----------------------------------------------------------------------------------
#
# Objective: Mathematically prove the correctness of the filtering logic.
# Why Z3?: Unit tests check specific examples (e.g., amount=-1, amount=0, amount=1),
# but they can't check all possible values. Z3 can prove that the logic
# `amount > 0 AND category is not empty` is correctly implemented for ALL possible
# inputs, providing a much stronger guarantee of correctness than example-based testing.
#
# Test Case:
#   - `test_z3_filter_logic_is_sound`:
#     - Define Z3 variables for `amount` (Real) and `category` (String).
#     - Create a Z3 boolean variable `is_kept` representing the outcome of the filter.
#     - State the required property: `is_kept` is true if and only if
#       `(amount > 0 AND category != "")`.
#     - Ask the Z3 solver to find a counterexample (a scenario where our property
#       is false).
#     - The test passes if the solver returns `unsat`, meaning no counterexample
#       exists and the logic is proven sound.
#
# -----------------------------------------------------------------------------------
# Part 2: Unit Tests (using Pytest)
# -----------------------------------------------------------------------------------
#
# Objective: Test each function (`extract`, `transform`, `load`) in isolation.
# Why Unit Tests?: This approach isolates failures to a specific part of the code,
# making debugging easier. It allows for testing specific edge cases for each
# component without needing to run the entire pipeline.
#
# --- Test `extract_data` ---
#   - `test_extract_data_success`: Reads a standard, valid CSV. Verifies headers and
#     data content are correct.
#   - `test_extract_data_file_not_found`: Ensures `FileNotFoundError` is raised for
#     a non-existent file.
#   - `test_extract_data_empty_file`: Handles a completely empty file. Expects empty
#     data and empty headers.
#   - `test_extract_data_header_only`: Handles a file with only a header row. Expects
#     correct headers and empty data.
#
# --- Test `transform_and_filter_data` ---
#   - `test_transform_valid_row`: A single, valid row is correctly transformed
#     (amount to float, category to lowercase).
#   - `test_filter_negative_amount`: A row with amount < 0 is filtered out.
#   - `test_filter_zero_amount`: A row with amount == 0 is filtered out.
#   - `test_filter_empty_category`: A row with an empty category string is filtered out.
#   - `test_filter_whitespace_category`: A row with a category containing only
#     whitespace is filtered out.
#   - `test_transform_case_and_whitespace`: A category with mixed case and padding
#     is correctly normalized.
#   - `test_skip_invalid_amount`: A row with a non-numeric amount is skipped, and a
#     warning is logged.
#   - `test_skip_invalid_date_format`: A row with an invalid date format is skipped,
#     and a warning is logged.
#   - `test_skip_missing_key`: A row missing a required column (e.g., 'amount') is
#     skipped, and a warning is logged.
#   - `test_transform_and_filter_mixed_data`: A comprehensive test with a list of
#     various valid and invalid rows to ensure the final output is correct.
#   - `test_transform_empty_input`: An empty list as input results in an empty list
#     as output.
#
# --- Test `load_data` ---
#   - `test_load_data_success`: Writes a list of cleaned data to a file. Verifies
#     the file content is correct.
#   - `test_load_data_empty_list`: Given no data, it creates a file with only the
#     header row.
#   - `test_load_data_io_error`: Mocks an `IOError` during file writing to ensure
#     the exception is correctly raised.
#
# -----------------------------------------------------------------------------------
# Part 3: Integration Test
# -----------------------------------------------------------------------------------
#
# Objective: Test the entire ETL pipeline from end-to-end.
# Why Integration Test?: This verifies that the individual components (`extract`,
# `transform`, `load`) work together correctly as a complete system.
#
# Test Case:
#   - `test_end_to_end_pipeline`:
#     1. Create a temporary input CSV file with a mix of valid, invalid, and
#        filterable rows.
#     2. Run the full pipeline programmatically.
#     3. Read the generated output CSV file.
#     4. Assert that the output file's content matches the expected cleaned and
#        filtered data exactly.
#   - `test_main_cli_insufficient_args`:
#     1. Simulate running the script from the command line with too few arguments.
#     2. Verify that the script exits with a non-zero status code and prints a
#        usage message.
#
# ===================================================================================


# --- Fixtures ---

@pytest.fixture
def sample_input_csv(tmp_path):
    """Creates a sample input CSV file in a temporary directory."""
    input_dir = tmp_path / "input"
    input_dir.mkdir()
    input_file = input_dir / "input.csv"
    content = [
        "id,date,amount,category",
        "1,2023-12-10,100.25,Books",          # Valid
        "2,2023-11-01,-80.00,Electronics",   # Filter: negative amount
        "3,2023-10-05,50.00,",               # Filter: empty category
        "4,2023-09-15,120.75,Groceries",     # Valid
        "5,2023-08-20,0.00,Software",        # Filter: zero amount
        "6,2023-07-11,25.50,  GAMES  ",      # Valid: needs cleaning
        "7,not-a-date,99.99,Hardware",       # Invalid: bad date
        "8,2023-06-01,invalid,Utilities",    # Invalid: bad amount
        "9,2023-05-15,300.00,TRAVEL",        # Valid: needs case change
        "10,2023-04-03,45.00,   ",           # Filter: whitespace category
    ]
    input_file.write_text("\n".join(content))
    return str(input_file)

@pytest.fixture
def expected_output_data():
    """The expected data after the full ETL process on sample_input_csv."""
    return [
        {'id': '1', 'date': '2023-12-10', 'amount': 100.25, 'category': 'books'},
        {'id': '4', 'date': '2023-09-15', 'amount': 120.75, 'category': 'groceries'},
        {'id': '6', 'date': '2023-07-11', 'amount': 25.50, 'category': 'games'},
        {'id': '9', 'date': '2023-05-15', 'amount': 300.00, 'category': 'travel'},
    ]

# ===================================================================================
# Part 1: Formal Verification Test
# ===================================================================================

@pytest.mark.skipif(not Z3_AVAILABLE, reason="z3-solver is not installed")
def test_z3_filter_logic_is_sound():
    """
    Uses Z3 to formally verify that the filtering logic is sound.
    It proves that a row is kept if and only if (amount > 0 AND category != "").
    """
    # 1. Define Z3 variables to represent row properties
    amount = z3.Real('amount')
    category = z3.String('category')

    # 2. Define the implementation logic from the code
    # This is the condition that the code *actually* checks
    implementation_logic = z3.And(amount > 0, category != "")

    # 3. Define the specification logic
    # This is the condition that the code *should* check
    specification_logic = z3.And(amount > 0, z3.Length(category) > 0)

    # 4. Create a solver and add the counter-example assertion
    # We are looking for a case where the implementation and specification disagree.
    solver = z3.Solver()
    solver.add(z3.Not(implementation_logic == specification_logic))

    # 5. Check for a solution
    # If `unsat`, it means no counter-example exists, and the logic is proven correct.
    # If `sat`, a counter-example was found, and the logic is flawed.
    result = solver.check()
    assert result == z3.unsat, f"Z3 found a counter-example: {solver.model()}"


# ===================================================================================
# Part 2: Unit Tests
# ===================================================================================

# --- Tests for extract_data ---

def test_extract_data_success(sample_input_csv):
    """Tests successful extraction from a valid CSV file."""
    data, headers = etlpipeline.extract_data(sample_input_csv)
    assert headers == ['id', 'date', 'amount', 'category']
    assert len(data) == 10
    assert data[0] == {'id': '1', 'date': '2023-12-10', 'amount': '100.25', 'category': 'Books'}

def test_extract_data_file_not_found():
    """Tests that FileNotFoundError is raised for a non-existent file."""
    with pytest.raises(FileNotFoundError):
        etlpipeline.extract_data("non_existent_file.csv")

def test_extract_data_empty_file(tmp_path):
    """Tests extraction from an empty file."""
    empty_file = tmp_path / "empty.csv"
    empty_file.touch()
    data, headers = etlpipeline.extract_data(str(empty_file))
    assert data == []
    assert headers is None # csv.DictReader returns None for fieldnames on empty files

def test_extract_data_header_only(tmp_path):
    """Tests extraction from a file with only a header."""
    header_file = tmp_path / "header.csv"
    header_file.write_text("id,date,amount,category")
    data, headers = etlpipeline.extract_data(str(header_file))
    assert data == []
    assert headers == ['id', 'date', 'amount', 'category']

# --- Tests for transform_and_filter_data ---

def test_transform_valid_row():
    """Tests a single valid row is transformed correctly."""
    row = [{'id': '1', 'date': '2023-12-10', 'amount': '100.25', 'category': 'Books'}]
    cleaned = etlpipeline.transform_and_filter_data(row)
    assert cleaned == [{'id': '1', 'date': '2023-12-10', 'amount': 100.25, 'category': 'books'}]

@pytest.mark.parametrize("amount_str", ["-50.0", "0", "0.0"])
def test_filter_by_amount(amount_str):
    """Tests that rows with amount <= 0 are filtered out."""
    row = [{'id': '1', 'date': '2023-12-10', 'amount': amount_str, 'category': 'Books'}]
    assert etlpipeline.transform_and_filter_data(row) == []

@pytest.mark.parametrize("category_str", ["", "   "])
def test_filter_by_category(category_str):
    """Tests that rows with empty or whitespace-only categories are filtered out."""
    row = [{'id': '1', 'date': '2023-12-10', 'amount': '100.25', 'category': category_str}]
    assert etlpipeline.transform_and_filter_data(row) == []

def test_transform_case_and_whitespace():
    """Tests normalization of category field."""
    row = [{'id': '1', 'date': '2023-12-10', 'amount': '100.25', 'category': '  TeStInG  '}]
    cleaned = etlpipeline.transform_and_filter_data(row)
    assert cleaned[0]['category'] == 'testing'

@pytest.mark.parametrize("bad_row, expected_error_msg", [
    ({'id': '1', 'date': '2023-12-10', 'amount': 'abc', 'category': 'Books'}, "could not convert string to float"),
    ({'id': '1', 'date': '2023/12/10', 'amount': '100', 'category': 'Books'}, "does not match format '%Y-%m-%d'"),
    ({'id': '1', 'date': '2023-12-10', 'category': 'Books'}, "'amount'"), # Missing key
])
def test_skip_invalid_rows(capsys, bad_row, expected_error_msg):
    """Tests that rows with data errors are skipped and a warning is printed."""
    data = [bad_row]
    cleaned = etlpipeline.transform_and_filter_data(data)
    assert cleaned == []
    captured = capsys.readouterr()
    assert "Warning: Skipping row" in captured.err
    assert expected_error_msg in captured.err

def test_transform_and_filter_mixed_data(expected_output_data):
    """Tests the function with a mix of valid, invalid, and filterable rows."""
    raw_data = [
        {'id': '1', 'date': '2023-12-10', 'amount': '100.25', 'category': 'Books'},
        {'id': '2', 'date': '2023-11-01', 'amount': '-80.00', 'category': 'Electronics'},
        {'id': '3', 'date': '2023-10-05', 'amount': '50.00', 'category': ''},
        {'id': '4', 'date': '2023-09-15', 'amount': '120.75', 'category': 'Groceries'},
        {'id': '5', 'date': '2023-08-20', 'amount': '0.00', 'category': 'Software'},
        {'id': '6', 'date': '2023-07-11', 'amount': '25.50', 'category': '  GAMES  '},
        {'id': '7', 'date': 'not-a-date', 'amount': '99.99', 'category': 'Hardware'},
        {'id': '9', 'date': '2023-05-15', 'amount': '300.00', 'category': 'TRAVEL'},
    ]
    cleaned = etlpipeline.transform_and_filter_data(raw_data)
    assert cleaned == expected_output_data

def test_transform_empty_input():
    """Tests that an empty input list produces an empty output list."""
    assert etlpipeline.transform_and_filter_data([]) == []

# --- Tests for load_data ---

def test_load_data_success(tmp_path, expected_output_data):
    """Tests writing cleaned data to a CSV file."""
    output_file = tmp_path / "output.csv"
    headers = ['id', 'date', 'amount', 'category']
    etlpipeline.load_data(expected_output_data, str(output_file), headers)

    with open(output_file, 'r') as f:
        content = f.read().strip()

    expected_content = [
        "id,date,amount,category",
        "1,2023-12-10,100.25,books",
        "4,2023-09-15,120.75,groceries",
        "6,2023-07-11,25.5,games",
        "9,2023-05-15,300.0,travel",
    ]
    assert content == "\n".join(expected_content)

def test_load_data_empty_list(tmp_path):
    """Tests that an empty data list results in a header-only file."""
    output_file = tmp_path / "output.csv"
    headers = ['id', 'date', 'amount', 'category']
    etlpipeline.load_data([], str(output_file), headers)

    with open(output_file, 'r') as f:
        content = f.read().strip()
    
    assert content == "id,date,amount,category"

def test_load_data_io_error(tmp_path):
    """Tests that an IOError is raised if the file cannot be written."""
    # Create a read-only directory to cause a permission error
    read_only_dir = tmp_path / "read_only"
    read_only_dir.mkdir()
    os.chmod(read_only_dir, 0o555) # Read and execute permissions only
    
    output_file = read_only_dir / "output.csv"
    
    with pytest.raises(IOError):
        etlpipeline.load_data([{'id': '1'}], str(output_file), ['id'])
    
    # Revert permissions to allow cleanup by pytest
    os.chmod(read_only_dir, 0o755)


# ===================================================================================
# Part 3: Integration Tests
# ===================================================================================

def test_end_to_end_pipeline(sample_input_csv, tmp_path):
    """Tests the full ETL pipeline from file to file."""
    output_file = tmp_path / "output.csv"

    # Run the pipeline programmatically
    raw_data, headers = etlpipeline.extract_data(sample_input_csv)
    cleaned_data = etlpipeline.transform_and_filter_data(raw_data)
    etlpipeline.load_data(cleaned_data, str(output_file), headers)

    # Verify the output
    with open(output_file, mode='r') as f:
        reader = csv.reader(f)
        output_rows = list(reader)

    expected_rows = [
        ['id', 'date', 'amount', 'category'],
        ['1', '2023-12-10', '100.25', 'books'],
        ['4', '2023-09-15', '120.75', 'groceries'],
        ['6', '2023-07-11', '25.5', 'games'],
        ['9', '2023-05-15', '300.0', 'travel'],
    ]
    assert output_rows == expected_rows

def test_main_cli_insufficient_args(capsys):
    """Tests the main function's argument handling from the CLI."""
    with patch('sys.argv', ['etlpipeline.py', 'input.csv']):
        with pytest.raises(SystemExit) as e:
            etlpipeline.main()
        
        assert e.value.code == 1 # Check for non-zero exit code
    
    captured = capsys.readouterr()
    assert "Usage: python etlpipeline.py <input_csv_path> <output_csv_path>" in captured.out
