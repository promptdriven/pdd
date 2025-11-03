import os
import subprocess
import etlpipeline

def setup_input_file(file_path: str, content: str):
    """Creates a dummy CSV file for the example."""
    with open(file_path, "w") as f:
        f.write(content)
    print(f"✓ Created dummy input file: '{file_path}'")

def print_file_content(file_path: str, description: str):
    """Prints the content of a given file to the console."""
    print(f"\n--- {description} ('{file_path}') ---")
    if os.path.exists(file_path):
        with open(file_path, "r") as f:
            print(f.read().strip())
    else:
        print("File not found.")
    print("----------------------------------")

def run_programmatic_example():
    """
    Demonstrates importing and using the etlpipeline functions directly.
    This approach is ideal for integrating the ETL logic into a larger application.
    """
    print("\n\n======= 1. Programmatic Usage Example =======")
    input_file = 'programmatic_input.csv'
    output_file = 'programmatic_output.csv'

    # Define the raw data for our input file
    csv_content = (
        "id,date,amount,category\n"
        "1,2023-12-10,100.25,Books\n"
        "2,2023-11-01,-80.00,Electronics\n"
        "3,2023-10-05,50.00, \n" # Empty category
        "4,2023-09-15,120.75, Groceries \n" # Category with whitespace
        "5,not-a-date,99.99,Software\n" # Invalid date
        "6,2023-08-20,0,Utilities" # Amount is zero
    )
    
    try:
        # Create the input file
        setup_input_file(input_file, csv_content)
        print_file_content(input_file, "Input Data")

        # 1. Extract data from the source file
        raw_data, headers = etlpipeline.extract_data(input_file)

        # 2. Transform and filter the extracted data
        cleaned_data = etlpipeline.transform_and_filter_data(raw_data)

        # 3. Load the cleaned data into the destination file
        etlpipeline.load_data(cleaned_data, output_file, headers)

        # Display the final, cleaned output
        print_file_content(output_file, "Cleaned Output Data")

    finally:
        # Clean up created files
        #if os.path.exists(input_file): os.remove(input_file)
        #if os.path.exists(output_file): os.remove(output_file)
        print("\n✓ Cleaned up temporary files.")


def run_command_line_example():
    """
    Demonstrates running etlpipeline.py as a standalone script from the terminal.
    This is useful for ad-hoc data cleaning tasks or simple, scheduled jobs.
    """
    print("\n\n======= 2. Command-Line Usage Example =======")
    input_file = 'cli_input.csv'
    output_file = 'cli_output.csv'

    csv_content = (
        "id,date,amount,category\n"
        "10,2024-01-15,19.99,Food\n"
        "11,2024-01-16,250.00,TRAVEL\n"
        "12,2024-01-17,-50.00,Refund"
    )

    try:
        setup_input_file(input_file, csv_content)
        print_file_content(input_file, "Input Data")

        # Construct the command to execute
        command = ["python", "etlpipeline.py", input_file, output_file]
        print(f"\n$ {' '.join(command)}")

        # Run the script as a subprocess
        result = subprocess.run(command, capture_output=True, text=True, check=True)
        
        # Print the script's standard output and errors
        print("\n--- Script stdout ---")
        print(result.stdout)
        if result.stderr:
            print("--- Script stderr ---")
            print(result.stderr)

        # Display the final, cleaned output
        print_file_content(output_file, "Cleaned Output Data")

    except subprocess.CalledProcessError as e:
        print(f"Command-line execution failed: {e}")
        print(e.stderr)
    finally:
        # Clean up created files
        if os.path.exists(input_file): os.remove(input_file)
        if os.path.exists(output_file): os.remove(output_file)
        print("\n✓ Cleaned up temporary files.")


if __name__ == "__main__":
    run_programmatic_example()
    run_command_line_example()