import os
from pathlib import Path
from typing import Tuple, Union
import logging
from rich import print as rprint
from rich.markdown import Markdown
from rich.console import Console
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import JsonOutputParser
from .summarize_directory import summarize_directory
from .llm_selector import llm_selector

console = Console()
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

def load_prompt_file(filename: str) -> str:
    """Load prompt from file in PDD_PATH/prompts directory."""
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise ValueError("PDD_PATH environment variable not set")
    
    prompt_path = Path(pdd_path) / 'prompts' / filename
    if not prompt_path.exists():
        raise FileNotFoundError(f"Prompt file not found: {prompt_path}")
    
    return prompt_path.read_text()

def calculate_token_cost(token_count: Union[int, float, str], cost_per_million: Union[float, int]) -> float:
    """
    Calculate token cost with robust type handling.
    
    Args:
        token_count: Number of tokens
        cost_per_million: Cost per million tokens
    
    Returns:
        Total cost of tokens
    """
    try:
        # Convert to numeric, with fallback to 0
        token_count = float(token_count) if token_count is not None else 0
        cost_per_million = float(cost_per_million) if cost_per_million is not None else 0
        
        return (token_count * cost_per_million) / 1_000_000
    except (TypeError, ValueError) as e:
        logger.error(f"Token cost calculation error: {e}")
        logger.error(f"token_count: {token_count}, type: {type(token_count)}")
        logger.error(f"cost_per_million: {cost_per_million}, type: {type(cost_per_million)}")
        return 0.0

def auto_include(
    input_prompt: str,
    directory_path: str,
    csv_file: str,
    strength: float = 0.7,
    temperature: float = 0.0,
    verbose: bool = False
) -> Tuple[str, str, float, str]:
    """
    Automatically find and insert proper dependencies into the prompt.
    
    Enhanced with more robust error handling and logging.
    """
    try:
        # Step 1: Load prompt templates
        auto_include_template = load_prompt_file('auto_include_LLM.prompt')
        extract_template = load_prompt_file('extract_auto_include_LLM.prompt')

        # Step 2: Get available includes from directory
        csv_output, dir_cost, _ = summarize_directory(
            directory_path=directory_path,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            csv_file=csv_file
        )

        # Robust CSV parsing
        available_includes = []
        for line in csv_output.split('\n')[1:]:  # Skip header
            line = line.strip()
            if line:  # Only process non-empty lines
                parts = line.split(',', 2)
                if len(parts) >= 2:
                    path = parts[0]
                    summary = parts[1] if len(parts) > 1 else ""
                    available_includes.append(f"File: {path}\nSummary: {summary}")

        # Step 3: Select LLM model with explicit type conversion
        model_result = llm_selector(
            strength=strength, 
            temperature=temperature
        )
        
        # Safely unpack model results with type conversion
        model, input_tokens, output_tokens, cost_per_input_million, cost_per_output_million = [
            val if val is not None else 0 for val in model_result
        ]

        # Step 4: Create LangChain templates
        auto_include_prompt = PromptTemplate(
            template=auto_include_template,
            input_variables=['input_prompt', 'available_includes']
        )

        extract_prompt = PromptTemplate(
            template=extract_template,
            input_variables=['llm_output']
        )

        # Step 5: Invoke LLM for auto-include
        auto_include_chain = auto_include_prompt | model
        auto_include_result = auto_include_chain.invoke({
            'input_prompt': input_prompt,
            'available_includes': '\n'.join(available_includes)
        })

        # Step 6: Invoke LLM for extracting includes
        extract_chain = extract_prompt | model | JsonOutputParser()
        extract_result = extract_chain.invoke({
            'llm_output': auto_include_result
        })

        # Step 7: Calculate total cost with robust type handling
        input_cost = calculate_token_cost(input_tokens, cost_per_input_million)
        output_cost = calculate_token_cost(output_tokens, cost_per_output_million)
        total_cost = input_cost + output_cost + dir_cost

        # Step 8: Construct output prompt
        output_prompt = extract_result.get('string_of_includes', '') + input_prompt

        return output_prompt, csv_output, total_cost, model.model_name

    except Exception as e:
        logger.error(f"Error in auto_include: {e}")
        console.print(f"[bold red]Error:[/bold red] {str(e)}")
        raise
