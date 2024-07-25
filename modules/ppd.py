import os
import sys
import argparse
from rich.console import Console
from rich.markdown import Markdown
from langchain_core.prompts import ChatPromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser
import tiktoken

def main():
    # Set up argument parser
    parser = argparse.ArgumentParser(description="Compile a prompt into a Python file using Langchain.")
    parser.add_argument("filename", type=str, help="The prompt file name (with .prompt extension).")
    parser.add_argument("-o", "--output", type=str, help="Output file name (without extension).")
    parser.add_argument("-force", action="store_true", help="Force overwrite the output file if it exists.")
    
    args = parser.parse_args()
    
    # Step 1: Handle file name and extension
    filename = args.filename
    if not filename.endswith('.prompt'):
        filename += '.prompt'
    
    # Step 2: Read the prompt file and process curly brackets
    with open(filename, 'r') as file:
        template_content = file.read()
    
    # Double curly brackets if necessary
    if '{' in template_content and '{{' not in template_content:
        template_content = template_content.replace('{', '{{').replace('}', '}}')
    
    # Step 3: Set up Langchain model
    llm = ChatOpenAI(model="gpt-4o-mini", temperature=0)
    
    # Step 4: Run the prompt through the model
    console = Console()
    token_count = len(tiktoken.encoding_for_model("gpt-4o-mini").encode(template_content))
    console.print(f"Running the prompt with {token_count} tokens...")
    
    prompt_template = ChatPromptTemplate.from_messages([("user", template_content)])
    chain = prompt_template | llm | StrOutputParser()
    
    result = chain.invoke({"input": "Your input here"})
    
    # Step 5: Pretty print the result
    result_markdown = Markdown(result)
    console.print(result_markdown)
    
    # Count tokens in the result
    result_token_count = len(tiktoken.encoding_for_model("gpt-4o-mini").encode(result))
    console.print(f"Result contains {result_token_count} tokens.")
    
    # Step 6: Strip Python code from the result
    python_code = extract_python_code(result)
    
    # Step 7: Write the Python code to a file
    output_filename = args.output if args.output else os.path.splitext(filename)[0] + '.py'
    
    if os.path.exists(output_filename) and not args.force:
        overwrite = input(f"{output_filename} already exists. Overwrite? (y/n) [default: y]: ")
        if overwrite.lower() not in ['y', 'yes', '']:
            console.print("Operation cancelled.")
            sys.exit(0)
    
    with open(output_filename, 'w') as output_file:
        output_file.write(python_code)
    
    console.print(f"Python code written to {output_filename}.")

def extract_python_code(result):
    """Extracts Python code from the result encapsulated in triple backticks."""
    lines = result.splitlines()
    python_code = []
    in_python_block = False
    
    for line in lines:
        if line.strip().startswith("```python"):
            in_python_block = True
            continue
        elif line.strip().startswith("```"):
            in_python_block = False
            continue
        
        if in_python_block:
            python_code.append(line)
    
    return "\n".join(python_code)

if __name__ == "__main__":
    main()