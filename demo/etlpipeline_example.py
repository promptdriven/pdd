# example_usage.py

import os
import etlpipeline
from typing import List, Dict, Optional

def run_pipeline_example() -> None:
    """
    Demonstrates the modular usage of the etlpipeline script.
    1. Creates a sample input CSV file.
    2. Runs the ETL process step-by-step.
    3. Prints the final output for verification.
    4. Cleans up the created files.
    """
    input_filename: str = 'input.csv'
    output_filename: str = 'output.csv'

    # Define sample data that covers valid, invalid, and filterable cases.
    # This data will be written to a temporary input.csv file.
    sample_csv_content: str = """id,date,amount,category
1,2023-12-10,100.25,Books
2,2023-11-01,-80.00,Electronics
3,2023-10-05,50.00, 
4,2023-09-15,120.75,  Groceries  
5,202X-09-15,150.00,Other
6,2023-08-20,abc,Software
7,2023-07-11,25.50,Gifts
"""

    # --- Setup: Create the input file for the demonstration ---
    print(f"1. SETUP: Creating sample '{input_filename}'...")
    with open(input_filename, 'w', encoding='utf-8') as f:
        f.write(sample_csv_content)
    print("   ...Done.\n")

    # --- ETL Process using the imported module ---
    print("2. ETL PROCESS: Running the pipeline functions...")

    # Step 1: EXTRACT data from the source file.
    print("   - Step (E): Extracting data...")
    # Assuming etlpipeline.extract_data returns (List[Dict], List[str]) or (None, List[str])
    raw_data: Optional[List[Dict[str, str]]]
    headers: List[str]
    raw_data, headers = etlpipeline.extract_data(input_filename)
    if raw_data is None:
        print("   Extraction failed. Exiting.")
        return
    print(f"     -> Extracted {len(raw_data)} rows with headers: {headers}")

    # Step 2: TRANSFORM and filter the extracted data.
    # The function will print warnings to stderr for invalid rows.
    print("   - Step (T): Transforming and filtering data...")
    cleaned_data: List[Dict[str, str]] = etlpipeline.transform_and_filter_data(raw_data)
    print(f"     -> Transformation resulted in {len(cleaned_data)} valid rows.")

    # Step 3: LOAD the cleaned data into the destination file.
    print("   - Step (L): Loading data into output file...")
    etlpipeline.load_data(cleaned_data, output_filename, headers)
    print("   ...Done.\n")

    # --- Verification: Display the content of the output file ---
    print(f"3. VERIFICATION: Contents of '{output_filename}':")
    try:
        with open(output_filename, 'r', encoding='utf-8') as f:
            print("-----------------------------------------")
            print(f.read().strip())
            print("-----------------------------------------")
    except FileNotFoundError:
        print(f"Error: Output file '{output_filename}' was not found.")
    finally:
        # --- Cleanup: Remove the created files ---
        print("\n4. CLEANUP: Removing temporary files...")
        if os.path.exists(input_filename):
            os.remove(input_filename)
        if os.path.exists(output_filename):
            os.remove(output_filename)
        print("   ...Done.")


if __name__ == "__main__":
    # To run this example, save it as 'example_usage.py' in the same
    # directory as 'etlpipeline.py' and execute: python example_usage.py
    run_pipeline_example()
