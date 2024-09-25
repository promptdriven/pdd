import os
from rich.console import Console
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser
from . import preprocess, llm_selector, unfinished_prompt, continue_generation, postprocess

console = Console()

def bug_to_unit_test(current_output: str, desired_output: str, prompt_used_to_generate_the_code: str, 
                     code_under_test: str, program_used_to_run_code_under_test: str, 
                     strength: float, temperature: float, language: str) -> tuple:
    """
    Generate a unit test from a code file using LangChain and various processing steps.

    Args:
        current_output (str): The current output of the code.
        desired_output (str): The desired output of the code.
        prompt_used_to_generate_the_code (str): The prompt used to generate the code.
        code_under_test (str): The code being tested.
        program_used_to_run_code_under_test (str): The program used to run the code under test.
        strength (float): The strength of the LLM model to use (0 to 1).
        temperature (float): The temperature of the LLM model to use.
        language (str): The programming language of the unit test to be generated.

    Returns:
        tuple: A tuple containing:
            - unit_test (str): The generated unit test code.
            - total_cost (float): The total cost to generate the unit test code.
            - model_name (str): The name of the selected LLM model.
    """
    try:
        # Step 1: Load the prompt file
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set")
        
        prompt_file_path = os.path.join(pdd_path, 'prompts', 'bug_to_unit_test_LLM.prompt')
        with open(prompt_file_path, 'r') as file:
            prompt_template = file.read()

        # Step 2: Preprocess the prompt
        processed_prompt = preprocess.preprocess(prompt_template, recursive=False, double_curly_brackets=False)

        # Create a Langchain LCEL template
        prompt = PromptTemplate.from_template(processed_prompt)

        # Step 3: Use llm_selector for the model
        llm, token_counter, input_cost, output_cost, model_name = llm_selector.llm_selector(strength, temperature)

        # Step 4: Run the inputs through the model using Langchain LCEL
        chain = prompt | llm | StrOutputParser()

        # Preprocess the prompt_used_to_generate_the_code
        processed_prompt_used = preprocess.preprocess(prompt_used_to_generate_the_code, recursive=False, double_curly_brackets=False)

        # Prepare the input for the model
        model_input = {
            "prompt_that_generated_code": processed_prompt_used,
            "current_output": current_output,
            "desired_output": desired_output,
            "code_under_test": code_under_test,
            "program_used_to_run_code_under_test": program_used_to_run_code_under_test,
            "language": language
        }

        # Count tokens and calculate cost
        input_tokens = sum(token_counter(str(value)) for value in model_input.values())
        input_cost_estimate = (input_tokens / 1_000_000) * input_cost

        console.print(f"[bold]Running the model with {input_tokens} input tokens.[/bold]")
        console.print(f"[bold]Estimated input cost: ${input_cost_estimate:.6f}[/bold]")

        # Invoke the chain
        result = chain.invoke(model_input)

        # Step 5: Pretty print the result
        console.print(Markdown(result))

        output_tokens = token_counter(result)
        output_cost_estimate = (output_tokens / 1_000_000) * output_cost
        console.print(f"[bold]Output tokens: {output_tokens}[/bold]")
        console.print(f"[bold]Estimated output cost: ${output_cost_estimate:.6f}[/bold]")

        # Step 6: Detect if the generation is incomplete
        last_600_chars = result[-600:]
        _, is_finished, unfinished_cost, _ = unfinished_prompt.unfinished_prompt(last_600_chars, strength=0.7, temperature=temperature)

        if not is_finished:
            # Step 6a: Continue the generation if incomplete
            final_result, continue_cost, _ = continue_generation.continue_generation(processed_prompt, result, strength, temperature)
        else:
            # Step 6b: Postprocess the result if complete
            final_result, postprocess_cost = postprocess.postprocess(result, language, strength=0.7, temperature=temperature)

        # Step 7: Calculate and print the total cost
        total_cost = input_cost_estimate + output_cost_estimate + unfinished_cost
        if not is_finished:
            total_cost += continue_cost
        else:
            total_cost += postprocess_cost

        console.print(f"[bold green]Total cost: ${total_cost:.6f}[/bold green]")

        return final_result, total_cost, model_name

    except FileNotFoundError as e:
        console.print(f"[bold red]Error: {e}[/bold red]")
        raise
    except ValueError as e:
        console.print(f"[bold red]Error: {e}[/bold red]")
        raise
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred: {e}[/bold red]")
        raise
