import os
import re

def preprocess(filename):
    def read_file(file_path):
        """Read the content of the file."""
        with open(file_path, 'r') as file:
            return file.read()

    def replace_includes(content):
        """Recursively replace angle brackets in triple backticks with file content."""
        pattern = r'```<([^>]+)>```'
        while re.search(pattern, content):
            content = re.sub(pattern, lambda m: read_file(m.group(1).strip()), content)
        return content

    def double_curly_braces(content):
        """Double the curly braces if they are not already doubled."""
        return re.sub(r'(?<!{){(?!{)', '{{', content).replace('}', '}}')

    # Step 1: Read the file content
    if not os.path.isfile(filename):
        raise FileNotFoundError(f"The file {filename} does not exist.")
    
    content = read_file(filename)

    # Step 2: Replace angle brackets in triple backticks
    content = replace_includes(content)

    # Step 3: Double the curly brackets
    content = double_curly_braces(content)

    # Step 4: Return the preprocessed prompt
    return content