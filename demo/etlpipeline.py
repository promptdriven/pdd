# etl_pipeline.py

import csv
import sys
from datetime import datetime

def extract_data(file_path: str) -> tuple[list[dict], list[str]]:
    """
    Extracts data from a given CSV file.

    Args:
        file_path (str): The path to the input CSV file.

    Returns:
        tuple[list[dict], list[str]]: A tuple containing a list of rows (as dictionaries)
                                      and a list of the header columns.
    
    Raises:
        FileNotFoundError: If the specified file_path does not exist.
    """
    try:
        with open(file_path, mode='r', encoding='utf-8') as infile:
            reader = csv.DictReader(infile)
            headers = reader.fieldnames
            data = [row for row in reader]
            print(f"Successfully extracted {len(data)} rows from '{file_path}'.")
            return data, headers
    except FileNotFoundError:
        print(f"Error: Input file not found at '{file_path}'", file=sys.stderr)
        raise

def transform_and_filter_data(data: list[dict]) -> list[dict]:
    """
    Applies transformations and filtering to the raw data.

    - Converts 'amount' to float.
    - Parses 'date' into YYYY-MM-DD format.
    - Converts 'category' to lowercase.
    - Filters out rows where amount <= 0 or category is empty.

    Args:
        data (list[dict]): A list of dictionaries, where each dictionary represents a row.

    Returns:
        list[dict]: The cleaned and transformed data.
    """
    cleaned_data = []
    for i, row in enumerate(data):
        try:
            # 1. Transformation
            amount = float(row['amount'])
            # Ensure date is in the correct format
            date_obj = datetime.strptime(row['date'], '%Y-%m-%d').date()
            category = row['category'].strip().lower()

            # 2. Filtering
            if amount > 0 and category:
                # Create a new dictionary with transformed values to preserve original data
                transformed_row = {
                    'id': row['id'],
                    'date': date_obj.strftime('%Y-%m-%d'),
                    'amount': amount,
                    'category': category
                }
                cleaned_data.append(transformed_row)

        except (ValueError, KeyError) as e:
            # Handle rows with incorrect data types or missing keys
            print(f"Warning: Skipping row {i+2} due to data error: {e}. Row: {row}", file=sys.stderr)
            continue
            
    print(f"Transformation complete. {len(cleaned_data)} rows remain after filtering.")
    return cleaned_data

def load_data(data: list[dict], file_path: str, headers: list[str]):
    """
    Writes the cleaned data to an output CSV file.

    Args:
        data (list[dict]): The data to be written.
        file_path (str): The path for the output CSV file.
        headers (list[str]): The list of column headers in the desired order.
    """
    if not data:
        print("Warning: No data to load after transformation and filtering.")
        # Create an empty file with headers
        with open(file_path, mode='w', newline='', encoding='utf-8') as outfile:
             writer = csv.writer(outfile)
             writer.writerow(headers)
        return

    try:
        with open(file_path, mode='w', newline='', encoding='utf-8') as outfile:
            # Use DictWriter to ensure columns are written in the correct order
            writer = csv.DictWriter(outfile, fieldnames=headers)
            writer.writeheader()
            writer.writerows(data)
        print(f"Successfully loaded data into '{file_path}'.")
    except IOError as e:
        print(f"Error: Could not write to output file '{file_path}'. Reason: {e}", file=sys.stderr)
        raise

def main():
    """
    Main function to orchestrate the ETL pipeline.
    """
    # Check for correct command-line arguments
    if len(sys.argv) != 3:
        print("Usage: python etl_pipeline.py <input_csv_path> <output_csv_path>")
        sys.exit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2]

    print("--- Starting ETL Pipeline ---")
    try:
        # 1. Extract
        raw_data, headers = extract_data(input_file)
        
        # 2. Transform
        cleaned_data = transform_and_filter_data(raw_data)
        
        # 3. Load
        load_data(cleaned_data, output_file, headers)
        
        print("--- ETL Pipeline Finished Successfully ---")
        
    except Exception as e:
        print(f"\n--- ETL Pipeline Failed: {e} ---", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    # To run this script, create an 'input.csv' file with the example content,
    # then execute from your terminal:
    # python etl_pipeline.py input.csv output.csv
    main()
