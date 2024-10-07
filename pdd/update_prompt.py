import os
from typing import Tuple
from rich.console import Console
from rich.markdown import Markdown
from .preprocess import preprocess
from .llm_selector import llm_selector
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser, JsonOutputParser

console = Console()

def update_prompt(input_prompt: str, input_code: str, modified_code: str, strength: float, temperature: float) -> Tuple[str, float, str]:
    """
    Updates a given prompt using a language model and calculates the cost of the operation.

    Args:
        input_prompt (str): The initial prompt to be processed.
        input_code (str): The original code associated with the prompt.
        modified_code (str): The modified version of the code.
        strength (float): The strength parameter for the LLM.
        temperature (float): The temperature parameter for the LLM.

    Returns:
        Tuple[str, float, str]: A tuple containing the modified prompt, total cost, and model name.
    """
    try:
        # Step 1: Load prompts
        pdd_path = os.getenv('PDD_PATH', '')
        with open(f'{pdd_path}/prompts/update_prompt_LLM.prompt', 'r') as file:
            update_prompt_llm = file.read()
        with open(f'{pdd_path}/prompts/extract_prompt_update_LLM.prompt', 'r') as file:
            extract_prompt_update_llm = file.read()

        # Step 2: Preprocess update_prompt_LLM
        processed_update_prompt = preprocess(update_prompt_llm, recursive=False, double_curly_brackets=False)
        
        print(processed_update_prompt)

        # Step 3: Create Langchain LCEL template for update_prompt_LLM
        update_prompt_template = PromptTemplate.from_template(processed_update_prompt)

        # Step 4: Use llm_selector for LLM model and token counting
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        # Step 5: Run input_prompt through the model
        update_chain = update_prompt_template | llm | StrOutputParser()
        update_result = update_chain.invoke({
            "input_prompt": input_prompt,
            "input_code": input_code,
            "modified_code": modified_code
        })

        # Calculate and print token count and cost
        input_tokens = token_counter(processed_update_prompt)
        output_tokens = token_counter(update_result)
        update_cost = (input_tokens * input_cost + output_tokens * output_cost) / 1_000_000

        console.print(f"[bold]Update Prompt Output:[/bold]")
        console.print(update_result)
        console.print(f"Input tokens: {input_tokens}, Output tokens: {output_tokens}")
        console.print(f"Estimated cost: ${update_cost:.6f}")

        # Step 6: Create Langchain LCEL template for extract_prompt_update_LLM
        llm, token_counter, input_cost, output_cost, _ = llm_selector(.5, temperature)
        extract_prompt_template = PromptTemplate.from_template(extract_prompt_update_llm)
        extract_chain = extract_prompt_template | llm | JsonOutputParser()

        # Run extraction
        extract_result = extract_chain.invoke({"llm_output": update_result})

        # Calculate and print token count and cost for extraction
        extract_input_tokens = token_counter(extract_prompt_update_llm + update_result)
        extract_output_tokens = token_counter(str(extract_result))
        extract_cost = (extract_input_tokens * input_cost + extract_output_tokens * output_cost) / 1_000_000

        console.print(f"[bold]Extraction Output:[/bold]")
        console.print(extract_result)
        console.print(f"Input tokens: {extract_input_tokens}, Output tokens: {extract_output_tokens}")
        console.print(f"Estimated cost: ${extract_cost:.6f}")

        # Step 7: Extract modified_prompt and print using Rich Markdown
        modified_prompt = extract_result.get('modified_prompt', '')
        console.print(Markdown(f"# Modified Prompt\n\n{modified_prompt}"))

        # Calculate total cost
        total_cost = update_cost + extract_cost

        return modified_prompt, total_cost, model_name

    except Exception as e:
        console.print(f"[bold red]Error:[/bold red] {str(e)}")