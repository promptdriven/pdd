import os
import json
from typing import Tuple
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import JsonOutputParser
from pydantic import BaseModel, Field
from rich.console import Console
from rich.markdown import Markdown
from .postprocess_0 import postprocess_0
from .llm_selector import llm_selector
import logging

console = Console()
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

class ExtractedCode(BaseModel):
    extracted_code: str = Field(description="The extracted and processed code")

# Create chain as a module-level variable
prompt = None
parser = None
chain = None

def initialize_chain():
    global prompt, parser, chain
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise ValueError("PDD_PATH environment variable is not set")
    
    prompt_path = os.path.join(pdd_path, 'prompts', 'extract_code_LLM.prompt')
    with open(prompt_path, 'r') as file:
        prompt_template = file.read()

    prompt = PromptTemplate(
        template=prompt_template,
        input_variables=["llm_output", "language"]
    )
    parser = JsonOutputParser(pydantic_object=ExtractedCode)
    llm, _, _, _, _ = llm_selector(0.7, 0)  # Default values
    chain = prompt | llm | parser

def postprocess(llm_output: str, language: str, strength: float = 0.9, temperature: float = 0) -> Tuple[str, float]:
    """
    Post-process the string output of an LLM to extract and format code.

    Args:
    llm_output (str): A string containing a mix of text and code sections.
    language (str): The programming language of the code to be extracted.
    strength (float): The strength of the LLM model to use. Default is 0.9.
    temperature (float): The temperature of the LLM model to use. Default is 0.

    Returns:
    Tuple[str, float]: A tuple containing the extracted code as a string and the total cost as a float.
    """
    try:
        # Step 1: If strength is 0, use postprocess_0
        if strength == 0:
            return postprocess_0(llm_output, language), 0.0

        # Step 2: Check for PDD_PATH
        if not os.getenv('PDD_PATH'):
            raise ValueError("PDD_PATH environment variable is not set")

        # Step 3 and 4: Use llm_selector for the LLM model
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        # Update chain with new LLM
        global chain
        if chain is None:
            logger.info("Initializing chain in postprocess function")
            initialize_chain()

        if chain is None:
            raise ValueError("Failed to initialize chain")

        input_text = prompt.format(llm_output=llm_output, language=language)
        input_tokens = token_counter(input_text)
        input_cost_estimate = (input_tokens / 1_000_000) * input_cost

        logger.info(f"Running post-processing on {input_tokens} tokens")
        logger.info(f"Estimated input cost: ${input_cost_estimate:.6f}")

        # Run the chain
        result = chain.invoke({"llm_output": llm_output, "language": language})
        logger.info(f"Chain invocation result: {result}")
        # Step 5c: Extract the code from the result
        extracted_code = result.get('extracted_code', "")

        # Remove backticks first
        lines = extracted_code.split('\n')
        if lines and lines[0].startswith('```'):
            lines = lines[1:-1]
        extracted_code = '\n'.join(lines)

        if not extracted_code:
            extracted_code = "Error: No extracted code found in the output"

        # Step 5e: Print the result and cost information
        console.print(Markdown(f"```{language}\n{extracted_code}\n```"))
        output_tokens = token_counter(extracted_code)
        output_cost_estimate = (output_tokens / 1_000_000) * output_cost
        total_cost = input_cost_estimate + output_cost_estimate

        logger.info(f"Output tokens: {output_tokens}")
        logger.info(f"Estimated output cost: ${output_cost_estimate:.6f}")

        return extracted_code, total_cost
    except ValueError as ve:
        logger.error(f"ValueError: {ve}")
        raise
    except Exception as e:
        logger.error(f"Error during post-processing: {e}")
        return "", 0.0

# Initialize the chain when the module is loaded
initialize_chain()
