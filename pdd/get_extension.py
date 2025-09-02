"""Module to retrieve file extensions for programming languages."""

import os
import pandas as pd

def get_extension(language: str) -> str:
    """
    Retrieves the file extension for a given programming language.

    Args:
        language: The name of the programming language.

    Returns:
        The file extension (e.g., ".py") or an empty string if not found
        or if the extension is invalid.

    Raises:
        ValueError: If the PDD_PATH environment variable is not set.
        FileNotFoundError: If the language_format.csv file is not found.
    """
    # Step 1: Load the environment variable PDD_PATH
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise ValueError("Environment variable PDD_PATH is not set.")
    
    # Construct the full path to the CSV file
    csv_file_path = os.path.join(pdd_path, 'data', 'language_format.csv')
    
    # Step 2: Lower case the language string
    language_lower = language.lower()
    
    # Step 3: Load the CSV file and look up the file extension
    try:
        dataframe = pd.read_csv(csv_file_path)
    except FileNotFoundError as exc:
        raise FileNotFoundError(
            f"The file {csv_file_path} does not exist."
        ) from exc
    
    # Check if the language exists in the DataFrame
    row = dataframe[dataframe['language'].str.lower() == language_lower]
    
    # Step 4: Return the file extension or an empty string if not found
    if not row.empty:
        extension = row['extension'].values[0]
        return extension if isinstance(extension, str) and extension else ''

    return ''

# Example usage:
# Assuming the environment variable PDD_PATH is set correctly
# print(get_extension('Python'))  # Output: .py

# ### Explanation of the Code:
# 1. **Environment Variable**: We use `os.getenv` to retrieve the `PDD_PATH` environment variable. If it's not set, we raise a `ValueError`.
# 2. **Lowercase Language**: The input language string is converted to lowercase to ensure case-insensitive comparison.
# 3. **Load CSV**: We use `pandas` to read the CSV file. If the file is not found, we raise a `FileNotFoundError`.
# 4. **Lookup**: We filter the DataFrame to find the row corresponding to the given language. If found, we check if the extension is a valid string and return it; otherwise, we return an empty string.
# 5. **Return Value**: If the language is not found, we return an empty string.

# ### Note:
# - Make sure to have the `pandas` library installed in your Python environment. You can install it using pip:
#   ```bash
#   pip install pandas
#   ```
# - Ensure that the CSV file is structured correctly and located at the specified path.