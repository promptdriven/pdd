# Here's a concise example of how to use the `test_generator` function from the `test_generator.py` module, along with documentation for the input and output parameters.

# ### Example Usage of `test_generator`

# ```python
# Filename: staging/pdd/example_usage.py

from test_generator import test_generator

# Define parameters for the test_generator function
prompt_file = "path/to/prompt_file"  # Path to the prompt file
code_file = "path/to/code_file"        # Path to the code file to be tested
strength = 0.7                          # Strength parameter for the LLM
language = "python"                     # Programming language of the code
test_directory = "path/to/test/directory"  # Directory to save generated tests

# Generate the test code
test_code = test_generator(
    prompt_file=prompt_file,
    code_file=code_file,
    strength=strength,
    language=language,
    test_directory=test_directory
)

# Print the generated test code
print(test_code)
# ```

# ### Documentation

# #### Function: `test_generator`

# **Parameters:**
# - `prompt_file` (str): The path to the prompt file that guides the test generation.
# - `code_file` (str): The path to the source code file for which tests are to be generated.
# - `strength` (float): A value between 0 and 1 that influences the creativity of the generated tests.
# - `language` (str): The programming language of the code (e.g., "python").
# - `test_directory` (str): The directory where the generated test files will be saved.

# **Returns:**
# - `str`: The generated unit test code as a string.

# ### Notes
# - Ensure that the `PDD_PATH` environment variable is set correctly to locate the prompt files.
# - The example assumes that the `test_generator.py` module is in the same directory as the `example_usage.py` script. Adjust the import statement as necessary based on your project structure.