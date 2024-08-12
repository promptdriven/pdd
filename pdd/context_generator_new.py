import os
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser
from rich.console import Console
import tiktoken
from llm_selector import llm_selector
from preprocess import preprocess
from postprocess import postprocess


def context_generator(
    code_module: str, 
    prompt: str, 
    language: str = "python", 
    strength: float = 0.5, 
    temperature: float = 0
) -> tuple[str, float]:
    """
    Generates example code using a language model based on the provided prompt and parameters.

    :param code_module: The code module to be used in the example.
    :param prompt: The prompt to guide the example generation.
    :param language: The programming language for the example code.
    :param strength: The strength parameter for model selection.
    :param temperature: The temperature parameter for model selection.
    :return: A tuple containing the generated example code and the total cost.
    """
    console = Console()

    # Step 1: Load the prompt file
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise ValueError("PDD_PATH environment variable is not set")
    
    prompt_file_path = os.path.join(pdd_path, 'prompts', 'example_generator_LLM.prompt')
    try:
        with open(prompt_file_path, 'r') as file:
            example_generator_prompt = file.read()
    except FileNotFoundError:
        raise FileNotFoundError(f"Prompt file not found at {prompt_file_path}")

    # Step 2: Create Langchain LCEL template
    prompt_template = PromptTemplate.from_template(example_generator_prompt)

    # Step 3: Use llm_selector for the model
    llm, input_cost, output_cost = llm_selector(strength, temperature)

    # Step 4: Preprocess the prompt
    processed_prompt = preprocess(prompt, recursive=False, double_curly_brackets=True)

    # Step 5: Run the code through the model using Langchain LCEL
    chain = prompt_template | llm | StrOutputParser()

    # Step 5a: Prepare parameters for invoke
    params = {
        "code_module": code_module,
        "processed_prompt": processed_prompt,
        "language": language
    }

    # Step 5b: Calculate and print token count and cost
    encoding = tiktoken.get_encoding("cl100k_base")
    token_count = len(encoding.encode(str(params)))
    estimated_cost = (token_count / 1_000_000) * input_cost

    console.print(f"[bold]Running example generator...[/bold]")
    console.print(f"Token count: {token_count}")
    console.print(f"Estimated input cost: ${estimated_cost:.6f}")

    # Run the chain
    try:
        result = chain.invoke(params)
    except Exception as e:
        raise RuntimeError(f"Error during model invocation: {e}")

    # Step 6: Postprocess the output
    example_code, postprocess_cost = postprocess(result, language, strength, temperature)

    # Calculate total cost
    output_token_count = len(encoding.encode(example_code))
    output_cost_value = (output_token_count / 1_000_000) * output_cost
    total_cost = estimated_cost + output_cost_value + postprocess_cost

    console.print(f"[bold]Total cost: ${total_cost:.6f}[/bold]")

    # Step 7: Return the example_code and total_cost
    return example_code, total_cost