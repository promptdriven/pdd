import os
import sys
import argparse
from rich.console import Console
from rich.markdown import Markdown
from langchain_core.prompts import ChatPromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser
from preprocess import preprocess
import tiktoken

def main():
    # Set up argument parser
    parser = argparse.ArgumentParser(description="Compile a prompt into a Python file using Langchain.")
    parser.add_argument("filename", type=str, help="The prompt file name (without extension).")
    parser.add_argument("-o", "--output", type=str, help="Output file name (with .py extension).")
    parser.add_argument("-force", action="store_true", help="Force overwrite the output file if it exists.")
    
    args = parser.parse_args()

    # Step 1: Handle file extension
    if not args.filename.endswith('.prompt'):
        args.filename += '.prompt'
    
    # Step 2: Preprocess the prompt
    preprocessed_prompt = preprocess(args.filename)

    # Step 3: Create Langchain LCEL template
    prompt_template = ChatPromptTemplate.from_messages([("user", preprocessed_prompt)])
    llm = ChatOpenAI(model="gpt-4o-mini", temperature=0)

    # Step 5: Run the prompt through the model
    console = Console()
    console.print(f"Running the prompt with {len(preprocessed_prompt.split())} tokens...")
    
    chain = prompt_template | llm | StrOutputParser()
    result = chain.invoke({"input": "Your input here"})

    # Step 6: Pretty print the result
    result_markdown = Markdown(result)
    console.print(result_markdown)

    # Count tokens in the result
    result_tokens = len(tiktoken.encoding_for_model("gpt-4o-mini").encode(result))
    console.print(f"Result contains {result_tokens} tokens.")

    # Step 7: Strip Python code from the result
    python_code = extract_python_code(result)

    # Step 8: Write the Python code to a file
    output_filename = args.output if args.output else args.filename.replace('.prompt', '.py')
    
    if os.path.exists(output_filename) and not args.force:
        overwrite = input(f"{output_filename} already exists. Overwrite? (y/n): ")
        if overwrite.lower() != 'y':
            console.print("Operation cancelled.")
            sys.exit(0)

    with open(output_filename, 'w') as f:
        f.write(python_code)
    
    console.print(f"Python code written to {output_filename}.")

def extract_python_code(result):
    """Extracts the Python code from the result."""
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

if __name__ == "__main__":
    main()