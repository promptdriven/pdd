# test_etlpipeline.py

import pytest
import os
import csv
from unittest.mock import patch, mock_open

# The code under test is in a file named etlpipeline.py
import etlpipeline

# Test Plan:
# 1. Fixtures:
#    - A fixture to create temporary CSV files for test isolation.
#
# 2. `extract_data` Tests:
#    - Test successful data extraction from a valid file.
#    - Test handling of a non-existent input file.
#    - Test handling of a completely empty file.
#    - Test handling of a file with only a header row.
#
# 3. `transform_and_filter_data` Tests (Logic-focused):
#    - Test transformation of a perfectly valid row (amount to float, category cleaning).
#    - Test filtering of rows with negative amounts.
#    - Test filtering of rows with zero amounts.
#    - Test filtering of rows with empty or whitespace-only categories.
#    - Test skipping rows with invalid date formats and ensure a warning is logged.
#    - Test skipping rows with non-numeric amounts and ensure a warning is logged.
#    - Test skipping rows with an incorrect number of columns.
#    - Test a comprehensive mix of good and bad data in a single run.
#
# 4. `load_data` Tests:
#    - Test successful writing of cleaned data to an output file.
#    - Verify that the 'amount' column is always formatted to two decimal places.
#    - Test writing an empty dataset (should result in a header-only file).
#    - Test error handling when the output file is not writable (using mocking).
#
# 5. End-to-End and CLI Tests:
#    - A full integration test that mimics the user running the script, checking the final output file.
#    - Test the command-line interface for correct/incorrect argument handling.


@pytest.fixture
def create_csv_file(tmp_path):
    """Fixture to create a temporary CSV file with given content."""
    def _create_file(filename, content):
        file_path = tmp_path / filename
        with open(file_path, 'w', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            writer.writerows(content)
        return file_path
    return _create_file

# --- Tests for extract_data ---

def test_extract_data_success(create_csv_file):
    """Tests successful extraction from a valid CSV file."""
    headers = ['id', 'date', 'amount', 'category']
    data_rows = [['1', '2023-01-01', '100.50', 'Groceries']]
    file_path = create_csv_file('input.csv', [headers] + data_rows)

    data, extracted_headers = etlpipeline.extract_data(file_path)

    assert extracted_headers == headers
    assert data == data_rows

def test_extract_data_file_not_found(capsys):
    """Tests that a non-existent file is handled gracefully."""
    data, headers = etlpipeline.extract_data('non_existent_file.csv')
    
    assert data is None
    assert headers is None
    captured = capsys.readouterr()
    assert "Error: Input file not found" in captured.err

def test_extract_data_empty_file(create_csv_file, capsys):
    """Tests that an empty file returns empty lists and a warning."""
    file_path = create_csv_file('input.csv', [])
    
    data, headers = etlpipeline.extract_data(file_path)

    assert data == []
    assert headers == []
    captured = capsys.readouterr()
    assert "Warning: Input file" in captured.err and "is empty" in captured.err

def test_extract_data_header_only(create_csv_file):
    """Tests that a file with only a header is handled correctly."""
    headers = ['id', 'date', 'amount', 'category']
    file_path = create_csv_file('input.csv', [headers])

    data, extracted_headers = etlpipeline.extract_data(file_path)

    assert extracted_headers == headers
    assert data == []

# --- Tests for transform_and_filter_data ---

def test_transform_valid_row():
    """Tests correct transformation of a single valid row."""
    raw_data = [['1', '2023-12-10', '150.75', '  Electronics  ']]
    cleaned = etlpipeline.transform_and_filter_data(raw_data)
    assert cleaned == [['1', '2023-12-10', 150.75, 'electronics']]

@pytest.mark.parametrize("amount_to_filter", ["-50.0", "0", "0.00"])
def test_filter_by_amount(amount_to_filter):
    """Tests that rows with amount <= 0 are filtered out."""
    raw_data = [['1', '2023-12-10', amount_to_filter, 'Books']]
    cleaned = etlpipeline.transform_and_filter_data(raw_data)
    assert cleaned == []

@pytest.mark.parametrize("category_to_filter", ["", "   ", "\t"])
def test_filter_by_category(category_to_filter):
    """Tests that rows with empty or whitespace-only categories are filtered out."""
    raw_data = [['1', '2023-12-10', '100', category_to_filter]]
    cleaned = etlpipeline.transform_and_filter_data(raw_data)
    assert cleaned == []

@pytest.mark.parametrize("bad_row", [
    ['1', '2023-12-10', '100'],  # Too few columns
    ['1', '2023-12-10', '100', 'Books', 'Extra'], # Too many columns
])
def test_skip_malformed_rows(bad_row, capsys):
    """Tests that rows with incorrect column counts are skipped."""
    cleaned = etlpipeline.transform_and_filter_data([bad_row])
    assert cleaned == []
    captured = capsys.readouterr()
    assert "Warning: Skipping malformed row" in captured.err

def test_skip_invalid_date(capsys):
    """Tests that rows with invalid date formats are skipped."""
    raw_data = [['1', '202X-12-10', '100', 'Books']]
    cleaned = etlpipeline.transform_and_filter_data(raw_data)
    assert cleaned == []
    captured = capsys.readouterr()
    assert "invalid date format" in captured.err

def test_skip_invalid_amount(capsys):
    """Tests that rows with non-numeric amounts are skipped."""
    raw_data = [['1', '2023-12-10', 'abc', 'Books']]
    cleaned = etlpipeline.transform_and_filter_data(raw_data)
    assert cleaned == []
    captured = capsys.readouterr()
    assert "invalid amount" in captured.err

# --- Tests for load_data ---

def test_load_data_and_amount_formatting(tmp_path):
    """Tests successful data loading and verifies amount formatting."""
    output_path = tmp_path / "output.csv"
    headers = ['id', 'date', 'amount', 'category']
    cleaned_data = [
        ['1', '2023-01-01', 100.25, 'books'],
        ['2', '2023-01-02', 50, 'food'],      # Integer amount
        ['3', '2023-01-03', 19.9, 'gifts'],   # Single decimal
    ]
    
    etlpipeline.load_data(cleaned_data, output_path, headers)

    with open(output_path, 'r', newline='') as f:
        reader = csv.reader(f)
        content = list(reader)

    expected_content = [
        ['id', 'date', 'amount', 'category'],
        ['1', '2023-01-01', '100.25', 'books'],
        ['2', '2023-01-02', '50.00', 'food'],
        ['3', '2023-01-03', '19.90', 'gifts'],
    ]
    assert content == expected_content

def test_load_empty_data(tmp_path):
    """Tests that loading empty data results in a header-only file."""
    output_path = tmp_path / "output.csv"
    headers = ['id', 'date', 'amount', 'category']
    
    etlpipeline.load_data([], output_path, headers)

    with open(output_path, 'r', newline='') as f:
        reader = csv.reader(f)
        content = list(reader)
    
    assert content == [headers]

def test_load_data_io_error(capsys):
    """Tests error logging when the output file is not writable."""
    with patch("builtins.open", mock_open()) as mock_file:
        mock_file.side_effect = IOError("Permission denied")
        etlpipeline.load_data([['1', '2023-01-01', 100, 'books']], 'locked_dir/output.csv', [])
        
        captured = capsys.readouterr()
        assert "Error: Could not write to file" in captured.err
        assert "Permission denied" in captured.err

# --- End-to-End Test ---

def test_full_pipeline(create_csv_file, tmp_path):
    """An end-to-end test covering the entire ETL process."""
    input_content = [
        ['id', 'date', 'amount', 'category'],
        ['1', '2023-12-10', '100.25', 'Books'],          # Valid
        ['2', '2023-11-01', '-80.00', 'Electronics'],    # Filter: negative amount
        ['3', '2023-10-05', '50.00', ' '],               # Filter: empty category
        ['4', '2023-09-15', '120.75', '  Groceries  '],  # Valid: needs cleaning
        ['5', '202X-09-15', '150.00', 'Other'],          # Error: bad date
        ['6', '2023-08-20', 'abc', 'Software'],          # Error: non-numeric amount
        ['7', '2023-07-11', '25.5', 'Gifts'],            # Valid: needs formatting
    ]
    input_path = create_csv_file('input.csv', input_content)
    output_path = tmp_path / 'output.csv'

    # Run the pipeline
    raw_data, headers = etlpipeline.extract_data(input_path)
    cleaned_data = etlpipeline.transform_and_filter_data(raw_data)
    etlpipeline.load_data(cleaned_data, output_path, headers)

    # Verify the output
    with open(output_path, 'r', newline='') as f:
        reader = csv.reader(f)
        output_content = list(reader)

    expected_output = [
        ['id', 'date', 'amount', 'category'],
        ['1', '2023-12-10', '100.25', 'books'],
        ['4', '2023-09-15', '120.75', 'groceries'],
        ['7', '2023-07-11', '25.50', 'gifts'],
    ]
    assert output_content == expected_output

# --- CLI Tests ---

def test_main_insufficient_args(monkeypatch, capsys):
    """Tests the main function exits if not enough CLI args are provided."""
    monkeypatch.setattr("sys.argv", ["etlpipeline.py"])
    with pytest.raises(SystemExit) as e:
        etlpipeline.main()
    
    assert e.value.code == 1
    captured = capsys.readouterr()
    assert "Usage: python etlpipeline.py" in captured.out

def test_main_file_not_found_arg(monkeypatch, capsys):
    """Tests the main function exits if the input file does not exist."""
    monkeypatch.setattr("sys.argv", ["etlpipeline.py", "no_such_file.csv", "output.csv"])
    with pytest.raises(SystemExit) as e:
        etlpipeline.main()
        
    assert e.value.code == 1
    captured = capsys.readouterr()
    assert "Error: Input file not found" in captured.err