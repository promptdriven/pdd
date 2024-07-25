import os
import argparse
import re
from langchain_core.prompts import ChatPromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser

def extract_python_code(result):
    # Use regex to find the python code block
    match = re.search(r'```python\n(.*?)\n```', result, re.DOTALL)
    if match:
        return match.group(1).strip()
    return None

def main():
    # Set up argument parser
    parser = argparse.ArgumentParser(description='Compile a prompt into a Python file using Langchain.')
    parser.add_argument('filename', type=str, help='The prompt file name (with .prompt extension)')
    parser.add_argument('-o', '--output', type=str, help='Output file name (without extension)')
    parser.add_argument('-force', action='store_true', help='Force overwrite existing files')
    
    args = parser.parse_args()
    
    # Ensure the file has a .prompt extension
    if not args.filename.endswith('.prompt'):
        args.filename += '.prompt'
    
    # Read the template from the file
    with open(args.filename, 'r') as file:
        template_content = file.read()
    
    # Create the LCEL template
    prompt_template = ChatPromptTemplate.from_messages([("user", template_content)])
    llm = ChatOpenAI(model="gpt-4o-mini", temperature=0)
    
    # Combine with a model and parser
    chain = prompt_template | llm | StrOutputParser()
    
    # Run the template
    result = chain.invoke({"input": "Your input here"})
    
    # Pretty print the result
    print(result)
    
    # Extract the Python code
    python_code = extract_python_code(result)
    
    if python_code is None:
        print("No Python code found in the result.")
        return
    
    # Determine output file name
    output_filename = args.output if args.output else os.path.splitext(args.filename)[0] + '.py'
    
    # Check if the output file already exists
    if os.path.exists(output_filename) and not args.force:
        overwrite = input(f"{output_filename} already exists. Overwrite? (y/n): ")
        if overwrite.lower() != 'y':
            print("Operation cancelled.")
            return
    
    # Write the Python code to the output file
    with open(output_filename, 'w') as output_file:
        output_file.write(python_code)
    
    print(f"Python code written to {output_filename}")

if __name__ == '__main__':
    main()