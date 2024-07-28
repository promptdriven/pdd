# To create the command line program "pdd" as described, we will use Python along with the `rich` library for pretty printing and `argparse` for command line argument parsing. The program will handle both prompt files and code files, generating runnable code or example code as specified.

# Here's a complete implementation of the `pdd` program:

# ```python
import os
import sys
import argparse
from rich.console import Console
from rich.markdown import Markdown
from rich.prompt import Confirm
from langchain_core.prompts import PromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser
from preprocess import preprocess
from postprocess import postprocess
from context_generator import context_generator
import tiktoken

console = Console()

def get_file_extension(language):
    extensions = {
        'python': '.py',
        'bash': '.sh',
        'makefile': '',
        # Add more languages and their extensions as needed
    }
    return extensions.get(language, '.txt')

def generate_output_paths(basename, output_dir, language, example=False):
    ext = get_file_extension(language)
    output_file = os.path.join(output_dir, f"{basename}{ext}")
    if example:
        output_file = os.path.join(output_dir, f"{basename}_example{ext}")
    return output_file

def handle_existing_file(file_path, force):
    if os.path.exists(file_path):
        if force or Confirm.ask(f"{file_path} already exists. Overwrite?"):
            return True
        else:
            console.print("Operation cancelled. File not overwritten.", style="bold red")
            return False
    return True

def process_prompt_file(prompt_file, output_dir, force, example_dir):
    basename, language = os.path.splitext(os.path.basename(prompt_file))[0].rsplit('_', 1)
    language = language.lower()

    # Step 2a: Preprocess the prompt
    try:
        processed_prompt = preprocess(prompt_file)
    except FileNotFoundError as e:
        console.print(e, style="bold red")
        return

    # Step 2b: Create Langchain template
    prompt_template = PromptTemplate.from_template(processed_prompt)
    llm = ChatOpenAI(model="gpt-4o-mini", temperature=0)

    # Step 2d: Run the prompt
    token_count = len(tiktoken.get_encoding("cl100k_base").encode(processed_prompt))
    console.print(f"Running prompt with {token_count} tokens...", style="bold yellow")
    
    chain = prompt_template | llm | StrOutputParser()
    result = chain.invoke({})

    # Step 2e: Pretty print the result
    console.print(Markdown(result), style="bold green")
    result_tokens = len(tiktoken.get_encoding("cl100k_base").encode(result))
    console.print(f"Result contains {result_tokens} tokens.", style="bold blue")

    # Step 2f: Postprocess the result
    runnable_code = postprocess(result, language)

    # Step 2g: Write runnable code to file
    output_file = generate_output_paths(basename, output_dir, language)
    if handle_existing_file(output_file, force):
        with open(output_file, 'w') as f:
            f.write(runnable_code)
        console.print(f"Runnable code written to {output_file}", style="bold green")

    # Generate example code if requested
    if example_dir:
        example_file = generate_output_paths(basename, example_dir, language, example=True)
        if handle_existing_file(example_file, force):
            success = context_generator(output_file, example_file, force=force)
            if success:
                console.print(f"Example code written to {example_file}", style="bold green")
            else:
                console.print("Context generation failed.", style="bold red")

def process_code_file(code_file, output_dir, force, example_dir):
    basename, language = os.path.splitext(os.path.basename(code_file))[0].rsplit('_', 1)
    language = language.lower()

    # Generate example code
    example_file = generate_output_paths(basename, example_dir, language, example=True)
    if handle_existing_file(example_file, force):
        success = context_generator(code_file, example_file, force=force)
        if success:
            console.print(f"Example code written to {example_file}", style="bold green")
        else:
            console.print("Context generation failed.", style="bold red")

def main():
    parser = argparse.ArgumentParser(description="Compile prompts or generate example code.")
    parser.add_argument("input_file", help="Input prompt or code file.")
    parser.add_argument("-o", "--output", help="Output path for runnable code.")
    parser.add_argument("-oe", "--output-example", help="Output path for example code.")
    parser.add_argument("--force", action="store_true", help="Force overwrite existing files.")
    
    args = parser.parse_args()

    input_file = args.input_file
    output_dir = args.output if args.output else os.path.dirname(input_file)
    example_dir = args.output_example if args.output_example else os.path.dirname(input_file)

    if not input_file.endswith('.prompt'):
        input_file += '.prompt'

    if os.path.exists(input_file):
        if input_file.endswith('.prompt'):
            process_prompt_file(input_file, output_dir, args.force, example_dir)
        else:
            process_code_file(input_file, output_dir, args.force, example_dir)
    else:
        console.print(f"File {input_file} does not exist.", style="bold red")

if __name__ == "__main__":
    main()
# ```

# ### Explanation of the Code:
# 1. **Imports**: The necessary libraries are imported, including `rich` for pretty printing and `argparse` for command line argument parsing.
# 2. **File Handling**: Functions are defined to handle file extensions, output paths, and existing file checks.
# 3. **Processing Functions**: Separate functions handle the processing of prompt files and code files, including preprocessing, invoking the model, and writing output files.
# 4. **Main Function**: The main function sets up argument parsing and determines whether to process a prompt or code file based on the input.
# 5. **Execution**: The program is executed by calling the `main()` function.

# ### Usage:
# - To run the program, save the code in a file named `pdd.py` and execute it from the command line with the appropriate arguments as described in the prompt. Make sure to have the required libraries installed and the necessary modules (`preprocess`, `postprocess`, `context_generator`) available in your environment.