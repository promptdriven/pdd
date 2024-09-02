import os
from typing import Tuple
from rich import print
from rich.markdown import Markdown
from rich.console import Console
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser

from .preprocess import preprocess
from .llm_selector import llm_selector
from .unfinished_prompt import unfinished_prompt
from .continue_generation import continue_generation
from .postprocess import postprocess

console = Console()

def generate_test(prompt: str, code: str, strength: float, temperature: float, language: str) -> Tuple[str, float, str]:
    """
    Generate a unit test from a code file using Langchain and LLMs.

    Args:
        prompt (str): The prompt that generated the code file to be processed.
        code (str): The code to generate a unit test from.
        strength (float): The strength of the LLM model to use (between 0 and 1).
        temperature (float): The temperature of the LLM model to use.
        language (str): The language of the unit test to be generated.

    Returns:
        Tuple[str, float, str]: A tuple containing the generated unit test code,
                                the total cost, and the name of the selected LLM model.
    """
    try:
        # Step 1: Load the prompt file
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set")
        
        prompt_file_path = os.path.join(pdd_path, 'prompts', 'generate_test_LLM.prompt')
        with open(prompt_file_path, 'r') as file:
            test_generator_prompt = file.read()

        # Step 2: Preprocess the prompt
        processed_prompt = preprocess(test_generator_prompt, recursive=False, double_curly_brackets=False)

        # Create Langchain LCEL template
        prompt_template = PromptTemplate.from_template(processed_prompt)

        # Step 3: Use llm_selector for the model
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        # Step 4: Run inputs through the model using Langchain LCEL
        chain = prompt_template | llm | StrOutputParser()

        # Calculate and display token count and cost
        input_tokens = token_counter(processed_prompt + prompt + code + language)
        input_cost_estimate = (input_cost / 1_000_000) * input_tokens

        console.print(f"[bold]Running test generation...[/bold]")
        console.print(f"Input tokens: {input_tokens}")
        console.print(f"Estimated input cost: ${input_cost_estimate:.6f}")

        # Invoke the chain
        result = chain.invoke({
            "prompt_that_generated_code": prompt,
            "code": code,
            "language": language
        })

        # Step 5: Pretty print the result
        console.print(Markdown(result))

        output_tokens = token_counter(result)
        output_cost_estimate = (output_cost / 1_000_000) * output_tokens
        console.print(f"Output tokens: {output_tokens}")
        console.print(f"Estimated output cost: ${output_cost_estimate:.6f}")

        # Step 6: Detect if the generation is incomplete
        last_200_chars = result[-600:]
        _, is_finished, unfinished_cost, _ = unfinished_prompt(last_200_chars, 0.9, temperature)

        if not is_finished:
            console.print("[bold yellow]Generation incomplete. Continuing...[/bold yellow]")
            final_result, continue_cost, _ = continue_generation(processed_prompt, result, strength, temperature)
        else:
            console.print("[bold green]Generation complete. Postprocessing...[/bold green]")
            final_result, postprocess_cost = postprocess(result, language, 0.9, temperature)

        # Step 7: Calculate and print total cost
        total_cost = input_cost_estimate + output_cost_estimate
        if not is_finished:
            total_cost += continue_cost
        else:
            total_cost += unfinished_cost + postprocess_cost

        console.print(f"[bold]Total cost: ${total_cost:.6f}[/bold]")

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
