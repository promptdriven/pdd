from context_generator import context_generator

# Define the input Python file and output file
input_python_file = 'path/to/your/module.py'  # Replace with the path to your Python file
output_file = 'path/to/output/example_usage.py'  # Replace with the desired output file path

# Call the context_generator function
success = context_generator(input_python_file, output_file, force=True)

# Check the result
if success:
    print("Context generation completed successfully.")
else:
    print("Context generation failed.")

# - The `force=True` argument allows overwriting the output file if it already exists. Set it to `False` if you want to avoid overwriting without confirmation.