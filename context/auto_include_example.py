import os
import pandas as pd
from typing import List, Dict, Tuple
from pdd import DEFAULT_STRENGTH
from pdd.auto_include import auto_include

def main() -> None:
    """
    Example usage of the auto_include function.
    """
    # load output.csv
    with open("project_dependencies.csv", 'r') as file:
        csv_file = file.read()

    # Define the parameters for the auto_include function
    input_prompt = """% You are an expert Python Software Engineer. Your goal is to write a Python function, "generate_test", that will create a unit test from a code file.

<include>./context/python_preamble.prompt</include>

% Here are the inputs and outputs of the function:
    Inputs: 
        'prompt' - A string containing the prompt that generated the code file to be processed.
        'code' - A string containing the code to generate a unit test from.
        'strength' - A float between 0 and 1 that is the strength of the LLM model to use.
        'temperature' - A float that is the temperature of the LLM model to use.
        'language' - A string that is the language of the unit test to be generated.
    Outputs: 
        'unit_test'- A string that is the generated unit test code.
        'total_cost' - A float that is the total cost to generate the unit test code.
        'model_name' - A string that is the name of the selected LLM model

% This program will use Langchain to do the following:
    Step 1. use $PDD_PATH environment variable to get the path to the project. Load the '$PDD_PATH/prompts/generate_test_LLM.prompt' file.
    Step 2. Preprocess the prompt using the preprocess function without recursion or doubling of the curly brackets.
    Step 2. Then this will create a Langchain LCEL template from the test generator prompt.
    Step 3. This will use llm_selector for the model.
    Step 4. This will run the inputs through the model using Langchain LCEL. 
        4a. Be sure to pass the following string parameters to the prompt during invoke:
            - 'prompt_that_generated_code': preprocess the prompt using the preprocess function without recursion or doubling of the curly brackets.
            - 'code'
            - 'language'
        4b. Pretty print a message letting the user know it is running and how many tokens (using token_counter from llm_selector) are in the prompt and the cost. The cost from llm_selector is in dollars per million tokens.
    Step 5. This will pretty print the markdown formatting that is present in the result via the rich Markdown function. It will also pretty print the number of tokens in the result and the cost.
    Step 6. Detect if the generation is incomplete using the unfinished_prompt function (strength .7) by passing in the last 600 characters of the output of Step 4.
        - a. If incomplete, call the continue_generation function to complete the generation.
        - b. Else, if complete, postprocess the model output result using the postprocess function from the postprocess module with a strength of 0.7.
    Step 7. Print out the total_cost including the input and output tokens and functions that incur cost (e.g. postprocessing).
    Step 8. Return the unit_test, total_cost and model_name"""
    directory_path = "context/c*.py"
    # read in the file
    with open('project_dependencies.csv', 'r') as file:
        csv_file = file.read()
    strength = DEFAULT_STRENGTH
    temperature = 0.5
    verbose = True

    # Call the auto_include function
    dependencies, csv_output, total_cost, model_name = auto_include(
        input_prompt=input_prompt,
        directory_path=directory_path,
        csv_file=csv_file,
        strength=strength,
        temperature=temperature,
        verbose=verbose
    )

    # Print the results
    print("Dependencies:")
    print(dependencies)

    print("CSV Output:")
    print(csv_output)
    print(f"Total Cost: ${total_cost:.4f} (in dollars per million tokens)")
    print(f"Model Name: {model_name}")

if __name__ == "__main__":
    main()