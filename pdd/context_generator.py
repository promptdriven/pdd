import os
from typing import Tuple
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser
from .preprocess import preprocess
from .llm_selector import llm_selector
from .postprocess import postprocess
from rich.console import Console

console = Console()

def context_generator(code_module: str, prompt: str, language: str = "python", strength: float = 0.5, temperature: float = 0.0) -> Tuple[str, float]:
    """
    Generates example code using a specified code module and prompt.

    Args:
        code_module (str): The code module to generate examples for.
        prompt (str): The prompt to guide the example generation.
        language (str): The programming language for the example.
        strength (float): The strength parameter for model selection.
        temperature (float): The temperature parameter for model selection.

    Returns:
        Tuple[str, float]: The generated example code and the total cost.
    """
    if not isinstance(code_module, str):
        raise TypeError("code_module must be a string")
    if not isinstance(prompt, str):
        raise TypeError("prompt must be a string")
    
    # Step 1: Load the prompt file
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise ValueError("PDD_PATH environment variable is not set")
    
    try:
        with open(f"{pdd_path}/prompts/example_generator_LLM.prompt", 'r') as file:
            example_generator_prompt = file.read()
    except FileNotFoundError:
        raise FileNotFoundError("Prompt file not found at the specified path")

    # Step 2: Create Langchain LCEL template
    prompt_template = PromptTemplate.from_template(example_generator_prompt)

    # Step 3: Use llm_selector for the model
    llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

    # Step 4: Preprocess the prompt
    processed_prompt = preprocess(prompt, recursive=False, double_curly_brackets=False)

    # Step 5: Run the code through the model using Langchain LCEL
    chain = prompt_template | llm | StrOutputParser()

    # Step 5a: Prepare parameters for invoke
    params = {
        "code_module": code_module,
        "processed_prompt": processed_prompt,
        "language": language
    }

    # Step 5b: Pretty print message with token count and cost
    full_prompt = prompt_template.format(**params)
    token_count = token_counter(full_prompt)
    prompt_cost = (token_count / 1_000_000) * input_cost

    console.print(f"[bold green]Running example generator...[/bold green]")
    console.print(f"Prompt tokens: {token_count}")
    console.print(f"Estimated prompt cost: ${prompt_cost:.6f}")

    # Run the chain
    result = chain.invoke(params)

    # Step 6: Postprocess the output
    example_code, postprocess_cost = postprocess(result, language, strength, temperature)

    # Calculate total cost
    output_tokens = token_counter(result)
    output_cost_value = (output_tokens / 1_000_000) * output_cost
    total_cost = prompt_cost + output_cost_value + postprocess_cost

    console.print(f"[bold green]Generation complete![/bold green]")
    console.print(f"Output tokens: {output_tokens}")
    console.print(f"Total cost: ${total_cost:.6f}")

    # Step 7: Return the example_code and total_cost
    return example_code, total_cost