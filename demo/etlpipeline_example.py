import etlpipeline
import os

# Define file paths for clarity
input_file = 'input.csv'
output_file = 'output.csv'

print(f"Starting ETL process: Reading from '{input_file}' and writing to '{output_file}'.")

# 1. EXTRACT: Read the raw data and headers from the input CSV.
# The function handles file-not-found errors and returns (data, headers).
raw_data, headers = etlpipeline.extract_data(input_file)

# Proceed only if the extraction was successful
if raw_data is not None:
    # 2. TRANSFORM: Clean, validate, and filter the data according to business rules.
    # This function processes the data in memory and returns a new list.
    # It will print warnings to stderr for any rows it has to skip.
    print("Transforming and filtering data...")
    cleaned_data = etlpipeline.transform_and_filter_data(raw_data)

    # 3. LOAD: Write the cleaned data to the output CSV file.
    # This function handles writing the headers and the cleaned rows.
    print("Loading cleaned data into the output file...")
    etlpipeline.load_data(cleaned_data, output_file, headers)

    # 4. VERIFY: (Optional) Read and print the output file's content to confirm the result.
    print("\n--- Verification: Content of output.csv ---")
    try:
        with open(output_file, 'r', encoding='utf-8') as f:
            print(f.read().strip())
    except FileNotFoundError:
        print(f"Could not read output file '{output_file}' for review.")
    print("--- End of content ---")

    # Clean up the generated output file
    # os.remove(output_file)

else:
    print(f"ETL process failed. Could not extract data from '{input_file}'.")