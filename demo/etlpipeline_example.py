import os
import etlpipeline

# Define filenames for clarity
INPUT_FILENAME = 'input.csv'
OUTPUT_FILENAME = 'output.csv'

# 1. SETUP: Create a sample input CSV file for the demonstration.
# This data includes valid rows, rows to be filtered, and rows with errors.
sample_data_content = """id,date,amount,category
1,2023-12-10,100.25,Books
2,2023-11-01,-80.00,Electronics
3,2023-10-05,50.00, 
4,2023-09-15,120.75,  Groceries  
5,202X-09-15,150.00,Other
6,2023-08-20,abc,Software
7,2023-07-11,25.50,Gifts
"""

try:
    print(f"--- Creating sample file: {INPUT_FILENAME} ---")
    with open(INPUT_FILENAME, 'w', encoding='utf-8') as f:
        f.write(sample_data_content)
    print("Sample file created successfully.")
    print("-" * 40)

    # 2. EXTRACT: Use the module to extract data from the input file.
    print(f"Step 1: Extracting data from '{INPUT_FILENAME}'...")
    raw_data, headers = etlpipeline.extract_data(INPUT_FILENAME)
    
    if raw_data is None:
        raise SystemExit("Extraction failed. Aborting.")
        
    print(f"Extracted {len(raw_data)} rows with headers: {headers}")
    print("-" * 40)

    # 3. TRANSFORM: Use the module to clean, validate, and filter the raw data.
    # The module will print warnings to stderr for rows it skips.
    print("Step 2: Transforming and filtering data...")
    cleaned_data = etlpipeline.transform_and_filter_data(raw_data)
    print(f"Transformation complete. {len(cleaned_data)} rows are valid.")
    # Note: The 'amount' is a float at this stage.
    print(f"Cleaned data in memory: {cleaned_data}")
    print("-" * 40)

    # 4. LOAD: Use the module to write the cleaned data to the output file.
    print(f"Step 3: Loading cleaned data into '{OUTPUT_FILENAME}'...")
    etlpipeline.load_data(cleaned_data, OUTPUT_FILENAME, headers)
    print("-" * 40)

    # 5. VERIFY: Read and print the content of the output file to confirm the result.
    print(f"--- Final Content of {OUTPUT_FILENAME} ---")
    if os.path.exists(OUTPUT_FILENAME):
        with open(OUTPUT_FILENAME, 'r', encoding='utf-8') as f:
            print(f.read().strip())
    else:
        print("Output file was not created.")
    print("--- End of Content ---")

finally:
    # 6. CLEANUP: Remove the created files to keep the directory clean.
    print("\n--- Cleaning up created files ---")

