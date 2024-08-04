import os
from langchain_core.prompts import PromptTemplate
from langchain_openai import ChatOpenAI
from langchain_core.output_parsers import StrOutputParser
from preprocess import preprocess
from postprocess import postprocess

def context_generator(python_filename: str, output_filename: str, force: bool = False) -> bool:
    # Step 1: Read the Python file name from input argument.
    if not os.path.isfile(python_filename):
        print(f"Error: The file {python_filename} does not exist.")
        return False

    # Step 2: Preprocess the file using the preprocess function.
    try:
        processed_content = preprocess(python_filename)
    except Exception as e:
        print(f"Error during preprocessing: {e}")
        return False

    # Step 3: Write a prompt suitable for GPT-4.
    prompt = f"""% Generate a concise example of how to use the following module properly:```{processed_content}```

    % Filename: ```{python_filename}```
    
    % Be sure to document what the input and output parameters are and assume the example will be in the same directory as the module."""

    # Step 4: Create a Langchain LCEL template from the generated prompt.
    prompt_template = PromptTemplate.from_template(prompt)

    # Step 5: Use the "gpt-4o-mini" model with a temperature of 0.
    llm = ChatOpenAI(model="gpt-4o-mini", temperature=0)

    # Step 6: Run the Python file through the model using Langchain LCEL chain.
    chain = prompt_template | llm | StrOutputParser()
    
    # Prepare the input for the chain
    input_data = {
        "python_file_text": processed_content,
        "python_filename": python_filename
    }

    # Invoke the chain
    try:
        result = chain.invoke(input_data)
    except Exception as e:
        print(f"Error during invocation: {e}")
        return False

    # Step 7: Postprocess the LCEL output.
    try:
        processed_output = postprocess(result, 'python')
    except Exception as e:
        print(f"Error during postprocessing: {e}")
        return False

    # Step 8: Write the Python example to the output_filename.
    if os.path.isfile(output_filename) and not force:
        overwrite = input(f"The file {output_filename} already exists. Do you want to overwrite it? (y/n): ")
        if overwrite.lower() != 'y':
            print("Operation cancelled.")
            return False

    try:
        with open(output_filename, 'w') as output_file:
            output_file.write(processed_output)
        print(f"Successfully wrote the example to {output_filename}.")
        return True
    except Exception as e:
        print(f"Error writing to file: {e}")
        return False