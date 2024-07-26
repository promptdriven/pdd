import os
import re

def preprocess(filename):
    def read_file(file_path):
        with open(file_path, 'r') as f:
            return f.read()

    def replace_includes(text):
        # This regex finds text in triple backticks with angle brackets
        pattern = r'```<([^>]+)>```'
        while re.search(pattern, text):
            text = re.sub(pattern, lambda m: read_file(m.group(1).strip()), text)
        return text

    def double_curly_braces(text):
        # This regex finds single curly braces and doubles them if not already doubled
        return re.sub(r'(?<!{){(?!{)', '{{', text)

    # Step 1: Read the file content
    if not os.path.isfile(filename):
        raise FileNotFoundError(f"The file {filename} does not exist.")
    
    content = read_file(filename)

    # Step 2: Replace angle brackets in triple backticks recursively
    content = replace_includes(content)

    # Step 3: Double any curly brackets that are not already doubled
    content = double_curly_braces(content)

    # Step 4: Print and return the preprocessed prompt
    print(content)
    return content

# Example usage:
# preprocessed_prompt = preprocess('your_file.txt')