import os
from typing import Tuple
from rich.console import Console
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser
from .preprocess import preprocess
from .llm_selector import llm_selector
from .unfinished_prompt import unfinished_prompt
from .continue_generation import continue_generation
from .postprocess import postprocess

console = Console()

def context_generator(code_module: str, prompt: str, language: str = "python", strength: float = 0.5, temperature: float = 0) -> Tuple[str, float, str]:
    """
    Generate a concise example on how to use code_module properly.

    Args:
        code_module (str): The code module to generate an example for.
        prompt (str): The prompt used to generate the code_module.
        language (str, optional): The language of the code module. Defaults to "python".
        strength (float, optional): The strength of the LLM model to use. Defaults to 0.5.
        temperature (float, optional): The temperature of the LLM model to use. Defaults to 0.

    Returns:
        Tuple[str, float, str]: A tuple containing the example code, total cost, and model name.
    """
    try:
        # Step 1: Load the example_generator prompt
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set")
        
        with open(f"{pdd_path}/prompts/example_generator_LLM.prompt", "r") as file:
            example_generator_prompt = file.read()

        # Step 2: Preprocess the example_generator prompt
        processed_example_generator = preprocess(example_generator_prompt, recursive=False, double_curly_brackets=False)

        # Step 3: Create a Langchain LCEL template
        prompt_template = PromptTemplate.from_template(processed_example_generator)

        # Step 4: Use llm_selector for the model
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        # Step 5: Preprocess the prompt
        processed_prompt = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Step 6: Invoke the code through the model using Langchain LCEL
        chain = prompt_template | llm | StrOutputParser()

        # Calculate token count and cost
        total_tokens = token_counter(processed_example_generator + code_module + processed_prompt + language)
        estimated_cost = (total_tokens / 1_000_000) * input_cost

        console.print(f"[bold]Generating example for {code_module}...[/bold]")
        console.print(f"Estimated input tokens: {total_tokens}")
        console.print(f"Estimated input cost: ${estimated_cost:.6f}")

        result = chain.invoke({
            "code_module": code_module,
            "processed_prompt": processed_prompt,
            "language": language
        })

        # Step 7: Detect if the generation is incomplete
        last_600_chars = result[-600:]
        _, is_finished, unfinished_cost, _ = unfinished_prompt(last_600_chars, strength=0.5, temperature=temperature)

        if not is_finished:
            # Step 7a: Continue the generation if incomplete
            result, continue_cost, _ = continue_generation(processed_example_generator, result, strength, temperature)
        else:
            continue_cost = 0

        # Step 7b: Postprocess the result
        example_code, postprocess_cost = postprocess(result, language, strength=0.9, temperature=temperature)

        # Step 8: Calculate and print the total cost
        output_tokens = token_counter(example_code)
        output_cost_value = (output_tokens / 1_000_000) * output_cost
        total_cost = estimated_cost + output_cost_value + unfinished_cost + continue_cost + postprocess_cost

        console.print(f"[bold green]Example generation complete![/bold green]")
        console.print(f"Total cost: ${total_cost:.6f}")

        # Step 9: Return the results
        return example_code, total_cost, model_name

    except FileNotFoundError as e:
        console.print(f"[bold red]Error: {e}[/bold red]")
        raise
    except ValueError as e:
        console.print(f"[bold red]Error: {e}[/bold red]")
        raise
    except Exception as e:
        console.print(f"[bold red]An unexpected error occurred: {e}[/bold red]")
        raise
