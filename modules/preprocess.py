import os

def preprocess(filename):
    # Step 1: Ensure the file has a .prompt extension
    if not filename.endswith('.prompt'):
        filename += '.prompt'
    
    # Function to read the content of a file
    def read_file(file_path):
        with open(file_path, 'r') as f:
            return f.read()
    
    # Function to recursively replace angle brackets with file content
    def replace_angle_brackets(content):
        while '```<' in content and '>```' in content:
            start = content.index('```<') + 4
            end = content.index('>```', start)
            file_to_read = content[start:end].strip()
            try:
                file_content = read_file(file_to_read)
                content = content[:content.index('```<')] + '```' + file_content + '```' + content[end + 4:]
            except FileNotFoundError:
                print(f"Warning: File '{file_to_read}' not found.")
                break
        return content
    
    # Function to double curly brackets
    def double_curly_brackets(content):
        return content.replace('{', '{{').replace('}', '}}')
    
    # Read the initial content of the file
    try:
        prompt_content = read_file(filename)
    except FileNotFoundError:
        return f"Error: The file '{filename}' does not exist."
    
    # Step 2: Replace angle brackets with file content
    prompt_content = replace_angle_brackets(prompt_content)
    
    # Step 3: Double the curly brackets
    prompt_content = double_curly_brackets(prompt_content)
    
    # Step 4: Print and return the preprocessed prompt
    print(prompt_content)
    return prompt_content

# Example usage:
# preprocessed_prompt = preprocess('example.prompt')