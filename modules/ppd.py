import os
import argparse
from rich.console import Console
from rich.markdown import Markdown
from rich.prompt import Confirm
import tiktoken

# Function to read the prompt from a file
def read_prompt_file(file_path):
    with open(file_path, 'r') as file:
        return file.read()

# Function to create the Langchain LCEL template and run it
def run_langchain(prompt_content):
    from langchain_core.prompts import ChatPromptTemplate
    from langchain_openai import ChatOpenAI
    from langchain_core.output_parsers import StrOutputParser

    # Create the LCEL template
    prompt_template = ChatPromptTemplate.from_messages([("user", prompt_content)])
    llm = ChatOpenAI(model="gpt-4o-mini", temperature=0)
    
    # Combine with a model and parser
    chain = prompt_template | llm | StrOutputParser()

    # Run the template
    result = chain.invoke({"input": "Your input here"})
    return result

# Function to extract Python code from the result
def extract_python_code(result):
    lines = result.splitlines()
    python_code = []
    in_python_block = False

    for line in lines:
        if line.strip().startswith("```python"):
            in_python_block = True
            continue
        elif line.strip().startswith("```") and in_python_block:
            break
        if in_python_block:
            python_code.append(line)

    return "\n".join(python_code).strip()

# Function to write the Python code to a file
def write_python_file(file_path, python_code):
    with open(file_path, 'w') as file:
        file.write(python_code)

def main():
    parser = argparse.ArgumentParser(description="Compile a prompt into a Python file using Langchain.")
    parser.add_argument("filename", type=str, help="The prompt file name (with .prompt extension).")
    parser.add_argument("-o", "--output", type=str, help="Output file name (without extension).")
    parser.add_argument("-force", action='store_true', help="Force overwrite the output file if it exists.")
    
    args = parser.parse_args()

    # Ensure the file has a .prompt extension
    if not args.filename.endswith('.prompt'):
        args.filename += '.prompt'

    # Read the prompt content
    prompt_content = read_prompt_file(args.filename)
    prompt_tokens = len(tiktoken.encoding_for_model("gpt-4o-mini").encode(prompt_content))
    
    print(f"Running the prompt with {prompt_tokens} tokens...")

    # Run the Langchain model
    result = run_langchain(prompt_content)

    # Pretty print the result
    console = Console()
    console.print(Markdown(result))

    # Count tokens in the result
    result_tokens = len(tiktoken.encoding_for_model("gpt-4o-mini").encode(result))
    print(f"Result contains {result_tokens} tokens.")

    # Extract Python code
    python_code = extract_python_code(result)

    # Determine output file path
    output_file = args.output if args.output else os.path.splitext(args.filename)[0] + '.py'

    # Check if the output file exists
    if os.path.exists(output_file):
        if not args.force:
            if not Confirm.ask(f"{output_file} already exists. Overwrite?"):
                print("Operation cancelled.")
                return

    # Write the Python code to the output file
    write_python_file(output_file, python_code)
    print(f"Python code written to {output_file}.")

if __name__ == "__main__":
    main()