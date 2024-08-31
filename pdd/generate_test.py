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
    Generate a unit test from a code file using LangChain and various processing steps.

    Args:
        prompt (str): The prompt that generated the code file to be processed.
        code (str): The code to generate a unit test from.
        strength (float): The strength of the LLM model to use (between 0 and 1).
        temperature (float): The temperature of the LLM model to use.
        language (str): The language of the unit test to be generated.

    Returns:
        Tuple[str, float, str]: A tuple containing the generated unit test code, total cost, and model name.
    """
    try:
        # Step 1: Load the prompt template
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set")
        
        prompt_path = os.path.join(pdd_path, 'prompts', 'generate_test_LLM.prompt')
        with open(prompt_path, 'r') as file:
            prompt_template = file.read()

        # Step 2: Preprocess the prompt
        processed_prompt = preprocess(prompt_template, recursive=False, double_curly_brackets=False)

        # Create LangChain LCEL template
        lcel_template = PromptTemplate.from_template(processed_prompt)

        # Step 3: Use llm_selector for the model
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        # Step 4: Run inputs through the model using LangChain LCEL
        chain = lcel_template | llm | StrOutputParser()

        # Calculate input tokens and cost
        input_tokens = token_counter(processed_prompt + prompt + code + language)
        input_cost_actual = (input_tokens / 1_000_000) * input_cost

        console.print(f"[bold]Generating unit test...[/bold]")
        console.print(f"Input tokens: {input_tokens}")
        console.print(f"Estimated input cost: ${input_cost_actual:.6f}")

        result = chain.invoke({
            "prompt_that_generated_code": prompt,
            "code": code,
            "language": language
        })

        # Calculate output tokens and cost
        output_tokens = token_counter(result)
        output_cost_actual = (output_tokens / 1_000_000) * output_cost

        console.print(Markdown(result))
        console.print(f"Output tokens: {output_tokens}")
        console.print(f"Estimated output cost: ${output_cost_actual:.6f}")

        # Step 6: Detect if the generation is incomplete
        last_200_chars = result[-200:]
        _, is_finished, unfinished_cost, _ = unfinished_prompt(last_200_chars, 0.5, temperature)

        if not is_finished:
            # Step 6a: Continue the generation if incomplete
            final_result, continue_cost, _ = continue_generation(processed_prompt, result, strength, temperature)
        else:
            # Step 6b: Postprocess the result if complete
            final_result, postprocess_cost = postprocess(result, language, 0.9, temperature)

        # Step 7: Calculate and print total cost
        total_cost = input_cost_actual + output_cost_actual + (unfinished_cost if not is_finished else 0) + (continue_cost if not is_finished else postprocess_cost)

        console.print(f"[bold]Total cost: ${total_cost:.6f}[/bold]")
        console.print(f"[bold]Model used: {model_name}[/bold]")

        return final_result, total_cost, model_name

    except FileNotFoundError as e:
        console.print(f"[bold red]Error: Prompt file not found. {str(e)}[/bold red]")
        raise
    except ValueError as e:
        console.print(f"[bold red]Error: {str(e)}[/bold red]")
        raise
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred: {str(e)}[/bold red]")
        raise