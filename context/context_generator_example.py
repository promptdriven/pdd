Here's a concise example of how to use the `context_generator` function you provided. This example assumes you have a Python file named `example_module.py` that you want to process and generate an output file named `output_example.txt`.

```python
# Example usage of the context_generator function

if __name__ == "__main__":
    # Define the input and output file names
    python_filename = 'example_module.py'
    output_filename = 'output_example.txt'
    
    # Call the context_generator function
    success = context_generator(python_filename, output_filename, force=False)
    
    # Check if the operation was successful
    if success:
        print("Context generation completed successfully.")
    else:
        print("Context generation failed.")
```

### Instructions:
1. Ensure you have the necessary modules installed and available in your environment.
2. Create a Python file named `example_module.py` with some code that you want to generate an example for.
3. Run the script above to generate the output file `output_example.txt` with the concise example based on the contents of `example_module.py`.