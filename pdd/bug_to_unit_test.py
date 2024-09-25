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

def bug_to_unit_test(current_output: int, desired_output: int, prompt_used_to_generate_the_code: str, code_under_tests: str, program_used_to_run_code_under_tests: str, strength: float, temperature: float, language: str) -> tuple[str, float, str]:
    """
    Generates unit test code from a given buggy code snippet using a language model.

    :param current_output: The current output of the code under test.
    :param desired_output: The desired output of the code under test.
    :param prompt_used_to_generate_the_code: The prompt used to generate the code.
    :param code_under_tests: The code snippet that needs unit testing.
    :param program_used_to_run_code_under_tests: The program used to run the code under test.
    :param strength: The strength parameter for the LLM model.
    :param temperature: The temperature parameter for the LLM model.
    :param language: The programming language of the code.
    :return: A tuple containing the final unit test code, total cost, and model name.
    """
    # Step 1: Load the prompt
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise ValueError("The environment variable 'PDD_PATH' is not set.")
    
    prompt_file_path = os.path.join(pdd_path, 'prompts', 'bug_to_unit_test_LLM.prompt')
    try:
        with open(prompt_file_path, 'r') as file:
            prompt_template = file.read()
    except FileNotFoundError:
        raise FileNotFoundError(f"Prompt file not found at {prompt_file_path}")

    # Step 2: Preprocess the prompt
    processed_prompt = preprocess(prompt_template, recursive=False, double_curly_brackets=False)

    # Step 3: Create the Langchain template
    prompt = PromptTemplate.from_template(processed_prompt)
    
    # Step 4: Select the LLM model
    llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

    # Prepare the input for the model
    input_data = {
        'prompt_that_generated_code': preprocess(prompt_used_to_generate_the_code, recursive=False, double_curly_brackets=False),
        'current_output': current_output,
        'desired_output': desired_output,
        'code_under_tests': code_under_tests,
        'program_used_to_run_code_under_tests': program_used_to_run_code_under_tests,
        'language': language
    }

    # Calculate token cost
    token_count = token_counter(processed_prompt)
    total_input_cost = (input_cost + output_cost) * (token_count / 1_000_000)
    console.print(f"[bold yellow]Running the model...[/bold yellow] (Tokens: {token_count}, Cost: ${total_input_cost:.6f})")

    # Step 5: Run the model
    chain = prompt | llm | StrOutputParser()
    result = chain.invoke(input_data)

    # Pretty print the result
    console.print(Markdown(result))
    result_token_count = token_counter(result)
    result_cost = (output_cost * (result_token_count / 1_000_000))
    
    # Step 6: Check if the generation is complete
    reasoning, is_finished, total_cost, model_name = unfinished_prompt(result[-600:], strength=0.7, temperature=temperature)
    
    if not is_finished:
        console.print("[bold red]Generation incomplete, continuing...[/bold red]")
        final_output, continue_cost, _ = continue_generation(processed_prompt, result, strength=strength, temperature=temperature)
        total_cost += continue_cost
    else:
        final_output, postprocess_cost = postprocess(result, language, strength=0.7, temperature=temperature)
        total_cost += postprocess_cost

    # Final output
    console.print(f"[bold green]Final Unit Test Code:[/bold green]")
    console.print(Markdown(final_output))
    console.print(f"[bold blue]Total Cost: ${total_cost:.6f}[/bold blue]")

    return final_output, total_cost, model_name

# Example usage
if __name__ == "__main__":
    unit_test_code, total_cost, model_name = bug_to_unit_test(
        current_output=-1,
        desired_output=5,
        prompt_used_to_generate_the_code="create a function that adds two numbers in python",
        code_under_tests="def add(a, b): return a + b",
        program_used_to_run_code_under_tests="python",
        strength=0.5,
        temperature=0.7,
        language="python"
    )
