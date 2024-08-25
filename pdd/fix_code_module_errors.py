import os
from pathlib import Path
from typing import Tuple
import tiktoken
from rich import print
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser
from .llm_selector import llm_selector
from .postprocess import postprocess

def fix_code_module_errors(program: str, prompt: str, code: str, errors: str, strength: float) -> Tuple[str, float]:
    """
    Fixes errors in a code module by leveraging a language model.

    Args:
        program (str): The name of the program.
        prompt (str): The prompt to be used.
        code (str): The code containing errors.
        errors (str): The errors to be fixed.
        strength (float): The strength parameter for model selection.

    Returns:
        Tuple[str, float]: A tuple containing the fixed code and the total cost.
    """
    try:
        # Step 1: Load the prompt file
        pdd_path = os.getenv('PDD_PATH')
        if not pdd_path:
            raise ValueError("PDD_PATH environment variable is not set")
        
        prompt_path = Path(pdd_path) / "prompts" / "fix_code_module_errors_LLM.prompt"
        with open(prompt_path, 'r') as file:
            prompt_template = file.read()

        # Step 2: Create Langchain LCEL template
        lcel_template = PromptTemplate.from_template(prompt_template)

        # Step 3: Use llm_selector
        temperature = 0
        llm, input_cost, output_cost = llm_selector(strength, temperature)

        # Step 4: Run the code through the model
        chain = lcel_template | llm | StrOutputParser()

        # Calculate token count and cost
        encoding = tiktoken.get_encoding("cl100k_base")
        preprocessed_prompt = lcel_template.format(program=program, prompt=prompt, code=code, errors=errors)
        token_count = len(encoding.encode(preprocessed_prompt))
        prompt_cost = (token_count / 1_000_000) * input_cost

        print(Markdown(f"Running LLM with {token_count} tokens. Estimated cost: ${prompt_cost:.6f}"))

        # Invoke the chain
        result = chain.invoke({"program": program, "prompt": prompt, "code": code, "errors": errors})

        # Step 5: Pretty print the result
        print(Markdown(result))
        result_token_count = len(encoding.encode(result))
        result_cost = (result_token_count / 1_000_000) * output_cost
        print(Markdown(f"Result contains {result_token_count} tokens. Estimated cost: ${result_cost:.6f}"))

        # Step 6: Extract corrected code
        fixed_code, postprocess_cost = postprocess(result, "python", strength=strength, temperature=temperature)

        # Step 7: Calculate and print total cost
        total_cost = prompt_cost + result_cost + postprocess_cost
        print(Markdown(f"Total cost of the run: ${total_cost:.6f}"))

        return fixed_code, total_cost

    except Exception as e:
        print(f"An error occurred: {str(e)}")
        return "", 0.0
