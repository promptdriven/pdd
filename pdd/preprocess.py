import os
import re

def preprocess(filename):
    def read_file(file_path):
        """Read the content of the file."""
        with open(file_path, 'r') as file:
            return file.read()

    def replace_includes(content):
        """Recursively replace angle brackets in triple backticks with file content retaining the backticks."""
        pattern = r'```<([^>]+)>```'
        
        def replacement(match):
            filename = match.group(1).strip()
            print(f"Reading file in replacement: {filename}")
            try:
                file_content = read_file(filename)
            except FileNotFoundError:
                return f"""```{match}```"""
            return f"""```
{file_content}
```"""
        
        while re.search(pattern, content):
            print(content)
            content = re.sub(pattern, replacement, content)
        print("finished:",content)
        return content

    def double_curly_braces(content):
        """Double the curly braces if they are not already doubled."""
        # Replace single opening braces
        content = re.sub(r'(?<!{){(?!{)', '{{', content)
        # Replace single closing braces
        content = re.sub(r'(?<!})}(?!})', '}}', content)
        return content

    # Step 1: Read the file content
    if not os.path.isfile(filename):
        raise FileNotFoundError(f"The file {filename} does not exist.")
    print(f"Reading file: {filename}")
    content = read_file(filename)

    # Step 2: Replace angle brackets in triple backticks
    content = replace_includes(content)

    # Step 3: Double the curly brackets
    content = double_curly_braces(content)

    # Step 4: Return the preprocessed prompt
    return content