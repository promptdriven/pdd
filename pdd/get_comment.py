# To achieve the task of writing a Python function `get_comment` that returns the comment character(s) associated with a given programming language, we need to follow the steps outlined in your description. Here's how you can implement this:

# ```python
import os
import csv

def get_comment(language):
    # Step 1: Load environment variables to get the path to the CSV file
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        return 'del'  # Return 'del' if the environment variable is not set

    csv_file_path = os.path.join(pdd_path, 'data', 'language_format.csv')

    # Step 2: Lower case the language string
    language = language.lower()

    try:
        # Step 3: Open the CSV file and look up the comment character(s)
        with open(csv_file_path, mode='r', newline='') as csvfile:
            reader = csv.DictReader(csvfile)
            for row in reader:
                if row['language'].lower() == language:
                    comment = row['comment']
                    # Step 4: Check if the comment character(s) is valid
                    if comment:
                        return comment
                    else:
                        return 'del'
    except FileNotFoundError:
        return 'del'  # Return 'del' if the file is not found
    except Exception as e:
        return 'del'  # Return 'del' for any other exceptions

    return 'del'  # Return 'del' if the language is not found

# Example usage:
# Assuming the environment variable PDD_PATH is set correctly
# print(get_comment('Python'))  # Output: #
# print(get_comment('Java'))    # Output: //
# ```

# ### Explanation:

# 1. **Environment Variable**: The function first retrieves the `PDD_PATH` environment variable to locate the CSV file. If the environment variable is not set, it returns `'del'`.

# 2. **Case Insensitivity**: The input language string is converted to lowercase to ensure case-insensitive comparison.

# 3. **CSV Reading**: The function reads the CSV file using Python's `csv.DictReader`, which allows accessing each row as a dictionary. It checks if the lowercase version of the language matches any entry in the CSV.

# 4. **Validation**: If a match is found, it checks if the comment character(s) is valid (i.e., not an empty string). If valid, it returns the comment character(s); otherwise, it returns `'del'`.

# 5. **Error Handling**: The function handles potential errors such as file not found or other exceptions by returning `'del'`.

# This implementation assumes that the CSV file is correctly formatted and that the environment variable `PDD_PATH` is set to the correct path.