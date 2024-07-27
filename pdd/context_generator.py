import os
import json
from preprocess import preprocess
from langchain_core.prompts import PromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser

def context_generator(python_filename: str, output_filename: str, force: bool = False) -> bool:
    # Step 1: Read the Python file
    if not os.path.isfile(python_filename):
        print(f"Error: The file {python_filename} does not exist.")
        return False
    
    with open(python_filename, 'r') as file:
        python_code = file.read()

    # Step 2: Preprocess the file
    preprocessed_prompt = preprocess(python_filename)

    # Step 3: Create a prompt for GPT-4
    prompt = f"Generate a concise Python example on how to use the following module:\n\n{preprocessed_prompt}"

    # Step 4: Create the LCEL template
    prompt_template = PromptTemplate.from_template(prompt)

    # Step 5: Initialize the model
    llm = ChatOpenAI(model="gpt-4o-mini", temperature=0)

    # Step 6: Combine with a model and parser
    chain = prompt_template | llm | StrOutputParser()

    # Prepare the input for the chain
    input_data = {"python_code": python_code}

    # Run the template
    result = chain.invoke(input_data)

    # Step 7: Write the result to the output file
    if os.path.isfile(output_filename) and not force:
        overwrite = input(f"The file {output_filename} already exists. Do you want to overwrite it? (y/n): ")
        if overwrite.lower() != 'y':
            print("Operation cancelled. The output file was not overwritten.")
            return False

    with open(output_filename, 'w') as output_file:
        output_file.write(result)

    print(f"Successfully wrote the example to {output_filename}.")
    return True