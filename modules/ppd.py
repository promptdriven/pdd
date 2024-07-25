import os
import argparse
import tiktoken
from rich.console import Console
from rich.markdown import Markdown
from langchain_core.prompts import ChatPromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser

def main():
    # Set up command line argument parsing
    parser = argparse.ArgumentParser(description="Compile a prompt into a Python file.")
    parser.add_argument("filename", type=str, help="The prompt file name (with .prompt extension).")
    parser.add_argument("-o", "--output", type=str, help="Output file name (without extension).")
    parser.add_argument("-force", action="store_true", help="Force overwrite the output file if it exists.")
    
    args = parser.parse_args()
    
    # Step 1: Handle file name and extension
    if not args.filename.endswith('.prompt'):
        args.filename += '.prompt'
    
    # Check if the prompt file exists
    if not os.path.isfile(args.filename):
        print(f"Error: The file '{args.filename}' does not exist.")
        return
    
    # Step 2: Read the template from the file
    with open(args.filename, 'r') as file:
        template_content = file.read()
    
    # Step 3: Create the LCEL template
    prompt_template = ChatPromptTemplate.from_messages([("user", template_content)])
    llm = ChatOpenAI(model="gpt-4o-mini", temperature=0)
    
    # Step 4: Run the prompt through the model
    token_count = len(tiktoken.encoding_for_model("gpt-4o-mini").encode(template_content))
    print(f"Running the prompt with {token_count} tokens...")
    
    chain = prompt_template | llm | StrOutputParser()
    result = chain.invoke({"input": "Your input here"})
    
    # Step 5: Pretty print the result
    console = Console()
    console.print(Markdown(result))
    
    result_token_count = len(tiktoken.encoding_for_model("gpt-4o-mini").encode(result))
    print(f"Result contains {result_token_count} tokens.")
    
    # Step 6: Strip the Python result from the output
    python_code = extract_python_code(result)
    
    # Step 7: Determine output file name
    output_filename = args.output if args.output else os.path.splitext(args.filename)[0] + '.py'
    
    # Check if the output file exists
    if os.path.isfile(output_filename):
        if not args.force:
            overwrite = input(f"The file '{output_filename}' already exists. Overwrite? (y/n): ")
            if overwrite.lower() != 'y':
                print("Operation cancelled.")
                return
    
    # Write the Python code to the output file
    with open(output_filename, 'w') as output_file:
        output_file.write(python_code)
    
    print(f"Python code written to '{output_filename}'.")

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
    
    return "\n".join(python_code)

if __name__ == "__main__":
    main()