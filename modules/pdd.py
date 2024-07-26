import argparse
import os
import sys
from langchain_core.prompts import ChatPromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser
from rich.console import Console
from rich.markdown import Markdown
import tiktoken
from preprocess import preprocess

def main():
    # Set up argument parser
    parser = argparse.ArgumentParser(description='Compile a prompt into a Python file using Langchain.')
    parser.add_argument('filename', type=str, help='The prompt file to read from.')
    parser.add_argument('-o', '--output', type=str, help='Output file name (with .py extension).')
    parser.add_argument('-force', action='store_true', help='Force overwrite the output file if it exists.')
    
    args = parser.parse_args()

    # Step 1: Read the file name from the command line
    input_file = args.filename
    if not os.path.isfile(input_file):
        print(f"Error: The file '{input_file}' does not exist.")
        sys.exit(1)

    # Step 2: Preprocess the prompt
    preprocessed_prompt = preprocess(input_file)

    # Step 3: Create the Langchain LCEL template
    prompt_template = ChatPromptTemplate.from_messages([("user", preprocessed_prompt)])
    llm = ChatOpenAI(model="gpt-4o-mini", temperature=0)

    # Step 5: Run the prompt through the model
    print(f"Running the prompt with {len(preprocessed_prompt.split())} tokens...")
    result = prompt_template | llm | StrOutputParser()
    output = result.invoke({"input": "Your input here"})

    # Step 6: Pretty print the result
    console = Console()
    console.print(Markdown(output))

    # Count tokens in the result
    token_count = len(tiktoken.encoding_for_model("gpt-4o-mini").encode(output))
    print(f"Output contains {token_count} tokens.")

    # Step 7: Strip the Python result from the output
    python_code = extract_python_code(output)

    # Step 8: Write the Python code to a file
    output_file = args.output if args.output else f"{os.path.splitext(input_file)[0]}.py"
    
    if os.path.exists(output_file) and not args.force:
        overwrite = input(f"The file '{output_file}' already exists. Overwrite? (y/N): ")
        if overwrite.lower() != 'y':
            print("Operation cancelled.")
            sys.exit(0)

    with open(output_file, 'w') as f:
        f.write(python_code)
    
    print(f"Python code written to '{output_file}'.")

def extract_python_code(output):
    """Extracts the Python code from the output."""
    lines = output.splitlines()
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

if __name__ == "__main__":
    main()