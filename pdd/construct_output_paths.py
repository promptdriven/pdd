# To implement the `construct_output_paths` function, we need to consider the different scenarios for the output paths based on the provided arguments. We'll define a helper function to handle the path construction logic and then use it to generate the required paths for both the runnable and example output files.

# Here's the implementation:

# ```python
import os

def construct_output_paths(basename, file_extension, argv_output_path, argv_example_output_path):
    def construct_path(base, ext, path):
        if path is None:
            # Default case: same directory, default naming
            return f"{base}{ext}"
        elif os.path.isdir(path):
            # Path given without file name
            return os.path.join(path, f"{base}{ext}")
        else:
            # File name given with or without path
            return path

    # Construct the runnable output path
    runnable_output_path = construct_path(basename, file_extension, argv_output_path)
    
    # Construct the example output path
    example_basename = f"{basename}_example"
    example_output_path = construct_path(example_basename, file_extension, argv_example_output_path)
    
    return runnable_output_path, example_output_path

# Example usage:
# print(construct_output_paths('context_generator', '.py', None, None))
# print(construct_output_paths('context_generator', '.py', None, 'context/'))
# print(construct_output_paths('context_generator', '.py', 'pdd/', 'context/'))
# print(construct_output_paths('pdd', '.prompt', 'pdd/pdd_v1.py', None))
# ```

# ### Explanation:

# 1. **Helper Function `construct_path`**:
#     - **Default Case**: If `path` is `None`, it constructs the path using the `base` and `ext` in the current directory.
#     - **Directory Path**: If `path` is a directory, it joins the directory path with the constructed file name.
#     - **File Path**: If `path` is a file name (with or without a path), it uses the provided `path` directly.

# 2. **Runnable Output Path**:
#     - Uses the `construct_path` function with the `basename`, `file_extension`, and `argv_output_path`.

# 3. **Example Output Path**:
#     - Constructs the example file name by appending `_example` to the `basename`.
#     - Uses the `construct_path` function with the modified `basename`, `file_extension`, and `argv_example_output_path`.

# 4. **Return**:
#     - Returns a tuple containing the `runnable_output_path` and `example_output_path`.

# This function should handle all the specified scenarios and generate the correct paths for the runnable and example output files.