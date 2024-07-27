import os
import json
from preprocess import preprocess
from langchain_core.prompts import PromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser

def context_generator(python_filename: str, output_filename: str, force: bool = False) -> bool:
    # Step 1: Read the Python file
    if not os.path.exists(python_filename):
        print(f"Error: The file {python_filename} does not exist.")
        return False

    # Step 2: Preprocess the file
    try:
        processed_content = preprocess(python_filename)
    except Exception as e:
        print(f"Error during preprocessing: {e}")
        return False

    # Step 3: Generate a prompt for GPT-4
    prompt_template_str = (
        "Generate a concise Python example on how to use the following module properly:\n\n"
        "Module Content:\n{module_content}\n\n"
        "Filename: {filename}"
    )
    prompt_template = PromptTemplate.from_template(prompt_template_str)

    # Step 4: Create the Langchain LCEL template
    llm = ChatOpenAI(model="gpt-4o-mini", temperature=0)
    chain = prompt_template | llm | StrOutputParser()

    # Step 6: Run the model
    try:
        result = chain.invoke({"module_content": processed_content, "filename": python_filename})
    except Exception as e:
        print(f"Error during model invocation: {e}")
        return False

    # Step 7: Write the output to the specified file
    if os.path.exists(output_filename) and not force:
        overwrite = input(f"The file {output_filename} already exists. Do you want to overwrite it? (y/n): ")
        if overwrite.lower() != 'y':
            print("Operation cancelled. The output file was not overwritten.")
            return False

    try:
        with open(output_filename, 'w') as output_file:
            output_file.write(result)
        print(f"Successfully wrote the example to {output_filename}.")
        return True
    except Exception as e:
        print(f"Error writing to output file: {e}")
        return False