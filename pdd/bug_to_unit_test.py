import os
from rich.console import Console
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.outputs import Generation
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

        # Create a LangChain LCEL template
        prompt = PromptTemplate.from_template(processed_prompt)

        # Step 3: Use llm_selector for the model
        llm, token_counter, input_cost, output_cost, model_name = llm_selector.llm_selector(strength, temperature)

        # Step 4: Run the inputs through the model using LangChain LCEL
        chain = prompt | llm

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

        # Count input tokens
        input_tokens = sum(token_counter(str(value)) for value in model_input.values())
        console.print(f"[bold]Running the model with {input_tokens} input tokens.[/bold]")
        console.print(f"[bold]Input tokens: {input_tokens}, cost: ${input_tokens * input_cost / 1_000_000:.6f}[/bold]")

        # Invoke the chain
        result = chain.invoke(model_input)

        # Extract text from the result
        if isinstance(result, list) and len(result) > 0 and isinstance(result[0], Generation):
            result_text = result[0].text
        else:
            result_text = str(result)

        # Debug logging
        console.print(f"[bold]LLM output type: {type(result)}[/bold]")
        console.print(f"[bold]LLM output content: {result}[/bold]")
        console.print(f"[bold]Extracted text: {result_text}[/bold]")

        # Step 5: Pretty print the result
        console.print(Markdown(result_text))

        # Count output tokens
        output_tokens = token_counter(result_text)
        console.print(f"[bold]Output tokens: {output_tokens}, cost: ${output_tokens * output_cost / 1_000_000:.6f}[/bold]")

        # Calculate base cost
        base_cost = (input_tokens * input_cost + output_tokens * output_cost) / 1_000_000
        console.print(f"[bold]Base cost: ${base_cost:.6f}[/bold]")

        # Step 6: Detect if the generation is incomplete
        last_600_chars = result_text[-600:]
        reasoning, is_finished, unfinished_cost, _ = unfinished_prompt.unfinished_prompt(last_600_chars, strength=0.7, temperature=temperature)
        console.print(f"[bold]Unfinished cost: ${unfinished_cost:.6f}[/bold]")

        additional_cost = unfinished_cost
        if not is_finished:
            # Step 6a: Continue the generation if incomplete
            final_result, continue_cost, _ = continue_generation.continue_generation(processed_prompt, result_text, strength, temperature)
            additional_cost += continue_cost
        else:
            # Step 6b: Postprocess the result if complete
            final_result, postprocess_cost = postprocess.postprocess(result_text, language, strength=0.7, temperature=temperature)
            additional_cost += postprocess_cost

        console.print(f"[bold]Additional costs: ${additional_cost:.6f}[/bold]")

        # Calculate total cost
        total_cost = base_cost + additional_cost

        # Round the total cost to 6 decimal places
        total_cost = round(total_cost, 6)

        console.print(f"[bold green]Total cost: ${total_cost:.6f}[/bold green]")

        return final_result, total_cost, model_name

    except FileNotFoundError as e:
        console.print(f"[bold red]Error: {e}")
        raise
    except ValueError as e:
        console.print(f"[bold red]Error: {e}")
        raise
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred: {e}")
        raise
