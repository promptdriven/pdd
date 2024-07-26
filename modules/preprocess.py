import os
import re

def read_file_content(filename):
    """Read the content of a file."""
    with open(filename, 'r') as file:
        return file.read()

def replace_included_files(content):
    """Recursively replace angle brackets in triple backticks with file content."""
    pattern = r'```<([^>]+)>```'
    
    while re.search(pattern, content):
        content = re.sub(pattern, lambda match: read_file_content(match.group(1).strip()), content)
    
    return content

def double_curly_braces(content):
    """Double the curly braces if they are not already doubled."""
    return re.sub(r'(?<!{){(?!{)', '{{', content)

def preprocess(filename):
    """Preprocess the prompt from the specified file."""
    # Step 1: Read the file content
    content = read_file_content(filename)
    
    # Step 2: Replace angle brackets in triple backticks with file content
    content = replace_included_files(content)
    
    # Step 3: Double the curly brackets if they are not already doubled
    content = double_curly_braces(content)
    
    # Step 4: Return the preprocessed prompt
    return content

# Example usage:
# preprocessed_prompt = preprocess('your_file.txt')
# print(preprocessed_prompt)