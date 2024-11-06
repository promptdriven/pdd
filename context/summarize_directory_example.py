# Example usage of the summarize_directory function

import os
import glob
from pdd.summarize_directory import summarize_directory  # Adjust the import based on your project structure

# Set up the environment variable for the project path
os.environ['PDD_PATH'] = '/absolute/path/to/pdd'  # Replace with your actual path

# Create the necessary directory structure and files
os.makedirs('/absolute/path/to/pdd/prompts', exist_ok=True)
os.makedirs('/absolute/path/to/pdd/sample_files', exist_ok=True)

# Write a sample prompt file
with open('/absolute/path/to/pdd/prompts/summarize_file_LLM.prompt', 'w') as f:
    f.write("Summarize the following content:\n{file_contents}")

# Write a sample text file to summarize
with open('/absolute/path/to/pdd/sample_files/sample_file.txt', 'w') as f:
    f.write("This is a sample file that contains some text to be summarized.")

# Define the directory path with a wildcard to match the sample file
directory_path = '/absolute/path/to/pdd/sample_files/*.txt'

# Call the summarize_directory function with appropriate parameters
csv_output, total_cost, model_name = summarize_directory(directory_path, strength=0.7, temperature=0.5)

# Print the outputs
print("CSV Output:")
print(csv_output)
print(f"Total Cost: ${total_cost:.6f}")
print(f"Model Name: {model_name}")