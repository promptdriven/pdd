import os
import argparse
from langchain_core.prompts import ChatPromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser
from rich.console import Console
from rich.markdown import Markdown

def read_prompt_file(file_path):
    with open(file_path, 'r') as file:
        return file.read()

def create_lcel_template(prompt_content):
    return ChatPromptTemplate.from_messages([("user", prompt_content)])

def run_prompt_through_model(prompt_template):
    llm = ChatOpenAI(model="gpt-4o-mini", temperature=0)
    chain = prompt_template | llm | StrOutputParser()
    return chain.invoke({"input": "Your input here"})

def extract_python_code(result):
    lines = result.splitlines()
    python_code = []
    in_python_block = False

    for line in lines:
        if line.startswith("```python"):
            in_python_block = True
            continue
        elif line.startswith("```") and in_python_block:
            break
        if in_python_block:
            python_code.append(line)

    return "\n".join(python_code)

def write_python_file(output_path, python_code):
    if os.path.exists(output_path):
        overwrite = input(f"{output_path} already exists. Overwrite? (y/n): ")
        if overwrite.lower() != 'y':
            return
    with open(output_path, 'w') as file:
        file.write(python_code)

def main():
    parser = argparse.ArgumentParser(description="Compile a prompt into a Python file.")
    parser.add_argument("filename", type=str, help="The prompt file name (with .prompt extension).")
    parser.add_argument("-o", "--output", type=str, help="Output file name (without extension).")
    parser.add_argument("-force", action='store_true', help="Force overwrite existing files.")
    
    args = parser.parse_args()

    # Ensure the file has a .prompt extension
    if not args.filename.endswith('.prompt'):
        args.filename += '.prompt'

    # Read the prompt from the file
    prompt_content = read_prompt_file(args.filename)

    # Create the LCEL template
    prompt_template = create_lcel_template(prompt_content)

    # Run the prompt through the model
    result = run_prompt_through_model(prompt_template)

    # Pretty print the result
    console = Console()
    console.print(Markdown(result))

    # Extract the Python code
    python_code = extract_python_code(result)

    # Determine output file name
    output_file = args.output if args.output else args.filename.replace('.prompt', '.py')

    # Write the Python code to the output file
    write_python_file(output_file, python_code)

if __name__ == "__main__":
    main()