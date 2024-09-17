import os
from rich.console import Console
from rich.markdown import Markdown
from pdd.preprocess import preprocess
from pdd.llm_selector import llm_selector
from pdd.unfinished_prompt import unfinished_prompt
from pdd.continue_generation import continue_generation
from pdd.postprocess import postprocess
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser
from langchain_core.runnables import RunnableSequence

console = Console()

def generate_test(current_output: str, desired_output: str, prompt_used_to_generate_the_code: str,
                  code_under_tests: str, program_used_to_run_code_under_tests: str,
                  strength: float, temperature: float, language: str) -> dict:
    """
    Generate a unit test from the provided code and outputs.

    Args:
        current_output (str): The current output of the code.
        desired_output (str): The desired output of the code.
        prompt_used_to_generate_the_code (str): The prompt used to generate the code.
        code_under_tests (str): The code that needs to be tested.
        program_used_to_run_code_under_tests (str): The program used to run the code.
        strength (float): The strength of the LLM model to use (0 to 1).
        temperature (float): The temperature of the LLM model to use (0 to 1).
        language (str): The language of the unit test to be generated.

    Returns:
        dict: A dictionary containing the generated unit test code, total cost, and model name.
    """
    if not (0 <= strength <= 1):
        raise ValueError("Strength must be between 0 and 1.")
    if not (0 <= temperature <= 1):
        raise ValueError("Temperature must be between 0 and 1.")

    # Step 1: Load the prompt
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise EnvironmentError("PDD_PATH environment variable is not set.")
    
    prompt_file_path = os.path.join(pdd_path, 'prompts', 'bug_to_unit_test_LLM.prompt')
    with open(prompt_file_path, 'r') as file:
        prompt_template = file.read()

    # Step 2: Preprocess the prompt
    processed_prompt = preprocess(prompt_template, recursive=False, double_curly_brackets=False)

    # Step 3: Select the LLM model
    llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

    # Step 4: Prepare the input for the model
    input_data = {
        'prompt_that_generated_code': processed_prompt,
        'current_output': current_output,
        'desired_output': desired_output,
        'code_under_tests': code_under_tests,
        'program_used_to_run_code_under_tests': program_used_to_run_code_under_tests,
        'language': language
    }

    # Calculate token cost
    token_count = token_counter(processed_prompt)
    total_input_cost = (input_cost * token_count) / 1_000_000
    console.print(f"[bold yellow]Running model with {token_count} tokens. Estimated cost: ${total_input_cost:.6f}[/bold yellow]")

    # Run the model
    chain = PromptTemplate.from_template(processed_prompt) | llm | StrOutputParser()
    result = chain.invoke(input_data)

    # Step 5: Pretty print the result
    console.print(Markdown(result))
    result_token_count = token_counter(result)
    result_cost = (output_cost * result_token_count) / 1_000_000
    console.print(f"[bold blue]Result contains {result_token_count} tokens. Cost: ${result_cost:.6f}[/bold blue]")

    # Step 6: Check if the generation is complete
    is_finished, total_cost, model_name = unfinished_prompt(result[-600:], strength=0.7)
    if not is_finished:
        final_output, continuation_cost, _ = continue_generation(processed_prompt, result, strength, temperature)
        console.print(f"[bold green]Continuation generated successfully.[/bold green]")
        total_cost += continuation_cost

        # Postprocess the final output
        extracted_code, postprocess_cost = postprocess(final_output, language, strength, temperature)
        total_cost += postprocess_cost
    else:
        extracted_code, postprocess_cost = postprocess(result, language, strength, temperature)
        total_cost += postprocess_cost

    # Step 7: Return the results
    return {
        'unit_test': extracted_code,
        'total_cost': total_cost,
        'model_name': model_name
    }
