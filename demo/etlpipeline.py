# etlpipeline.py

"""
A modular ETL (Extract, Transform, Load) pipeline script.

This script reads user data from an input CSV file, cleans and transforms the data
according to predefined rules, and writes the valid, cleaned data to an output
CSV file.

It is designed to be run from the command line or imported as a Python module.

Command-line usage:
    python etlpipeline.py input.csv output.csv

Module usage:
    import etlpipeline
    raw_data, headers = etlpipeline.extract_data('input.csv')
    cleaned_data = etlpipeline.transform_and_filter_data(raw_data)
    etlpipeline.load_data(cleaned_data, 'output.csv', headers)
"""

import csv
import sys
from datetime import datetime

def extract_data(input_filepath):
    """
    Extracts data from a given CSV file.

    Args:
        input_filepath (str): The path to the input CSV file.

    Returns:
        tuple: A tuple containing a list of data rows and a list of headers.
               Returns (None, None) if the file cannot be found or is empty.
    """
    try:
        with open(input_filepath, mode='r', encoding='utf-8') as infile:
            reader = csv.reader(infile)
            try:
                headers = next(reader)
                data = [row for row in reader]
                return data, headers
            except StopIteration:
                # Handle empty file
                print(f"Warning: Input file '{input_filepath}' is empty or has no header.", file=sys.stderr)
                return [], []
    except FileNotFoundError:
        print(f"Error: Input file not found at '{input_filepath}'", file=sys.stderr)
        return None, None

def transform_and_filter_data(data_rows):
    """
    Transforms, cleans, and filters a list of data rows.

    - Converts 'amount' to float.
    - Parses 'date' to ensure YYYY-MM-DD format.
    - Cleans 'category' by lowercasing and stripping whitespace.
    - Filters out rows with amount <= 0 or an empty category.
    - Skips and warns about rows with malformed data.

    Args:
        data_rows (list): A list of lists, where each inner list is a row of data.

    Returns:
        list: A list of cleaned and filtered data rows.
    """
    cleaned_data = []
    # Start at 2 to account for the header row and 1-based indexing for user-friendly logs
    for i, row in enumerate(data_rows, start=2):
        try:
            # Ensure row has the expected number of columns
            if len(row) != 4:
                print(f"Warning: Skipping malformed row {i} (incorrect number of columns): {row}", file=sys.stderr)
                continue

            id_val, date_str, amount_str, category_str = row

            # 1. Transform and validate 'amount'
            try:
                amount = float(amount_str)
            except (ValueError, TypeError):
                print(f"Warning: Skipping row {i} due to invalid amount: '{amount_str}'", file=sys.stderr)
                continue

            # 2. Transform and validate 'date'
            try:
                datetime.strptime(date_str, '%Y-%m-%d')
            except ValueError:
                print(f"Warning: Skipping row {i} due to invalid date format: '{date_str}'", file=sys.stderr)
                continue

            # 3. Transform 'category'
            cleaned_category = category_str.strip().lower()

            # 4. Filter data based on business rules
            if amount <= 0:
                continue  # Silently filter as per requirement
            if not cleaned_category:
                continue  # Silently filter as per requirement

            # If all checks pass, add the transformed row to our results
            cleaned_data.append([id_val, date_str, amount, cleaned_category])

        except Exception as e:
            print(f"Warning: An unexpected error occurred while processing row {i}: {row}. Error: {e}", file=sys.stderr)
            continue

    return cleaned_data

def load_data(cleaned_data, output_filepath, headers):
    """
    Writes the cleaned data to an output CSV file.

    Args:
        cleaned_data (list): The list of cleaned data rows to write.
        output_filepath (str): The path for the output CSV file.
        headers (list): The list of header strings for the CSV file.
    """
    try:
        with open(output_filepath, mode='w', newline='', encoding='utf-8') as outfile:
            writer = csv.writer(outfile)
            writer.writerow(headers)
            # Format the amount column to a string with two decimal places before writing
            formatted_data = [
                [row[0], row[1], f"{row[2]:.2f}", row[3]] for row in cleaned_data
            ]
            writer.writerows(formatted_data)
        print(f"Successfully wrote {len(cleaned_data)} rows to '{output_filepath}'")
    except IOError as e:
        print(f"Error: Could not write to file '{output_filepath}'. Reason: {e}", file=sys.stderr)

def main():
    """Main function to run the ETL pipeline from the command line."""
    if len(sys.argv) != 3:
        print("Usage: python etlpipeline.py <input_csv_path> <output_csv_path>")
        print("Example: python etlpipeline.py input.csv output.csv")
        sys.exit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2]

    print(f"Starting ETL process: {input_file} -> {output_file}")

    # Extract
    raw_data, headers = extract_data(input_file)
    if raw_data is None:
        sys.exit(1)  # Exit if file not found

    # Transform
    cleaned_data = transform_and_filter_data(raw_data)

    # Load
    load_data(cleaned_data, output_file, headers)

    # Per instructions, print output file contents for review
    print("\n--- Content of output.csv ---")
    try:
        with open(output_file, 'r', encoding='utf-8') as f:
            print(f.read().strip())
    except FileNotFoundError:
        print(f"Could not read output file '{output_file}' for review.")
    print("--- End of content ---")


if __name__ == "__main__":
    main()


# test_etlpipeline.py

import unittest
import os
import csv
import sys
from io import StringIO
import tempfile
import etlpipeline

class TestEtlPipeline(unittest.TestCase):
    """Unit tests for the ETL pipeline script."""

    def setUp(self):
        """Set up test environment before each test."""
        # Create a temporary directory to hold test files
        self.test_dir_obj = tempfile.TemporaryDirectory()
        
        # Define file paths within the temporary directory
        self.input_filename = os.path.join(self.test_dir_obj.name, 'input.csv')
        self.output_filename = os.path.join(self.test_dir_obj.name, 'output.csv')
        
        # Sample data covering all required cases
        self.test_csv_data = [
            ['id', 'date', 'amount', 'category'],
            ['1', '2023-12-10', '100.25', 'Books'],          # Valid row
            ['2', '2023-11-01', '-80.00', 'Electronics'],    # Filter: negative amount
            ['3', '2023-10-05', '50.00', ' '],               # Filter: empty category after strip
            ['4', '2023-09-15', '120.75', '  Groceries  '],  # Valid: needs cleaning
            ['5', '202X-09-15', '150.00', 'Other'],          # Error: bad date format
            ['6', '2023-08-20', 'abc', 'Software'],          # Error: non-numeric amount
            ['7', '2023-07-11', '25.50', 'Gifts'],           # Valid row
            ['8', '2023-06-01', '50', 'Food']                # Valid row with whole number amount
        ]

        # Expected output after ETL process
        self.expected_output_data = [
            ['id', 'date', 'amount', 'category'],
            ['1', '2023-12-10', '100.25', 'books'],
            ['4', '2023-09-15', '120.75', 'groceries'],
            ['7', '2023-07-11', '25.50', 'gifts'],
            ['8', '2023-06-01', '50.00', 'food']
        ]

        # Create the dummy input.csv file in the temporary directory
        with open(self.input_filename, 'w', newline='') as f:
            writer = csv.writer(f)
            writer.writerows(self.test_csv_data)

    def tearDown(self):
        """Clean up test files after each test."""
        # Automatically cleans up the directory and all its contents
        self.test_dir_obj.cleanup()

    def test_extract_data(self):
        """Test the data extraction function."""
        data, headers = etlpipeline.extract_data(self.input_filename)
        self.assertEqual(headers, self.test_csv_data[0])
        self.assertEqual(data, self.test_csv_data[1:])

    def test_transform_and_filter_data(self):
        """Test the data transformation and filtering logic in isolation."""
        raw_data = self.test_csv_data[1:]
        
        # Redirect stderr to capture warnings
        old_stderr = sys.stderr
        sys.stderr = captured_stderr = StringIO()
        
        cleaned_data = etlpipeline.transform_and_filter_data(raw_data)
        
        # Restore stderr
        sys.stderr = old_stderr
        
        # Check that appropriate warnings were printed for bad rows
        warnings = captured_stderr.getvalue()
        self.assertIn("invalid date format: '202X-09-15'", warnings)
        self.assertIn("invalid amount: 'abc'", warnings)

        # The transform function returns data with float amounts
        expected_transformed = [
            ['1', '2023-12-10', 100.25, 'books'],
            ['4', '2023-09-15', 120.75, 'groceries'],
            ['7', '2023-07-11', 25.50, 'gifts'],
            ['8', '2023-06-01', 50.0, 'food']
        ]
        self.assertEqual(cleaned_data, expected_transformed)

    def test_full_pipeline(self):
        """Test the full ETL process from file to file."""
        # Run the main pipeline logic
        raw_data, headers = etlpipeline.extract_data(self.input_filename)
        cleaned_data = etlpipeline.transform_and_filter_data(raw_data)
        etlpipeline.load_data(cleaned_data, self.output_filename, headers)

        # Verify the output file content
        self.assertTrue(os.path.exists(self.output_filename))
        
        with open(self.output_filename, 'r', newline='') as f:
            reader = csv.reader(f)
            output_content = list(reader)
        
        # Print for manual review as requested
        print("\n--- Test: Full Pipeline - Content of output.csv ---")
        with open(self.output_filename, 'r') as f:
            print(f.read().strip())
        print("--- End of content ---")

        # Assert that the content matches the expected output
        self.assertEqual(output_content, self.expected_output_data)

if __name__ == '__main__':
    unittest.main()
