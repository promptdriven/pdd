import os
import json
from rich import print
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import JsonOutputParser
from langchain_core.runnables import RunnablePassthrough
from langchain_openai import ChatOpenAI
from .llm_selector import llm_selector

def unfinished_prompt(prompt_text: str, strength: float = 0.5, temperature: float = 0.0):
    """
    Process the given prompt text using a language model, calculate token costs, and return the reasoning,
    completion status, total cost, and model name.

    :param prompt_text: The text to be processed by the language model.
    :param strength: The strength parameter for the LLM model selection.
    :param temperature: The temperature parameter for the LLM model selection.
    :return: A tuple containing reasoning, completion status, total cost, and model name.
    """
    # Step 1: Use $PDD_PATH environment variable to get the path to the project
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise ValueError("PDD_PATH environment variable is not set")

    prompt_file_path = os.path.join(pdd_path, 'prompts', 'unfinished_prompt_LLM.prompt')
    try:
        with open(prompt_file_path, 'r') as file:
            unfinished_prompt_template = file.read()
    except FileNotFoundError:
        raise FileNotFoundError(f"Prompt file not found at {prompt_file_path}")

    # Step 2: Create a Langchain LCEL template from unfinished_prompt_LLM prompt
    if not isinstance(unfinished_prompt_template, str):
        raise ValueError("Prompt template must be a string")
    prompt_template = PromptTemplate.from_template(unfinished_prompt_template)
    parser = JsonOutputParser()

    # Step 3: Use the llm_selector function for the LLM model
    try:
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)
    except Exception as e:
        raise RuntimeError(f"Error selecting LLM model: {e}")

    # Step 4: Run the prompt text through the model using Langchain LCEL
    chain = prompt_template | llm | parser

    # 4a: Pass the following string parameters to the prompt during invoke
    input_data = {"PROMPT_TEXT": prompt_text}

    # 4b: Pretty print a message letting the user know it is running
    try:
        token_count = token_counter(prompt_text)
        print(f"Running analysis on the prompt. Token count: {token_count}, Estimated cost: ${(token_count / 1_000) * input_cost:.6f}")
    except Exception as e:
        print(f"Error calculating token count: {e}")
        token_count = 0

    # Invoke the chain
    try:
        result = chain.invoke(input_data)
    except Exception as e:
        raise RuntimeError(f"Error during LLM invocation: {e}")

    # 4c: Access the keys 'reasoning' and 'is_finished'
    reasoning = result.get('reasoning', "No reasoning provided.")
    is_finished = result.get('is_finished', False)

    # 4d: Pretty print the reasoning and completion status
    try:
        output_token_count = token_counter(json.dumps(result))
    except Exception as e:
        print(f"Error calculating output token count: {e}")
        output_token_count = 0

    total_cost = (token_count / 1_000) * input_cost + (output_token_count / 1_000) * output_cost
    print(f"Input tokens: {token_count}, Input cost: ${input_cost}")
    print(f"Output tokens: {output_token_count}, Output cost: ${output_cost}")
    print(f"Reasoning: {reasoning}")
    print(f"Is Finished: {is_finished}")
    print(f"Output Token Count: {output_token_count}, Output Token Cost: ${(output_token_count / 1_000) * output_cost:.6f}")
    print(f"Calculated total cost: ${total_cost:.8f}")

    # Step 5: Return the 'reasoning', 'is_finished', 'total_cost', and 'model_name'
    return reasoning, is_finished, total_cost, model_name

# Example usage
if __name__ == "__main__":
    reasoning, is_finished, total_cost, model_name = unfinished_prompt("This is a test prompt.")
    print(f"Reasoning: {reasoning}, Is Finished: {is_finished}, Total Cost: {total_cost}, Model Name: {model_name}")