import os
from pathlib import Path
from typing import Tuple, List
from rich import print as rprint
from rich.markdown import Markdown
from rich.console import Console
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import JsonOutputParser
from pydantic import BaseModel, Field

from .llm_selector import llm_selector

console = Console()

class ExtractedIncludes(BaseModel):
    string_of_includes: str = Field(description="The string of includes to be added to the prompt")

def load_prompt_template(filename: str) -> str:
    """Load prompt template from file."""
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise ValueError("PDD_PATH environment variable not set")
    
    prompt_path = Path(pdd_path) / 'prompts' / filename
    if not prompt_path.exists():
        raise FileNotFoundError(f"Prompt file not found: {prompt_path}")
    
    return prompt_path.read_text()

def calculate_cost(num_tokens: int, cost_per_million: float) -> float:
    """Calculate cost for given number of tokens."""
    return (num_tokens / 1_000_000) * cost_per_million

def auto_include(
    input_prompt: str,
    available_includes: List[str],
    strength: float,
    temperature: float
) -> Tuple[str, float, str]:
    """
    Automatically find and insert proper dependencies into the prompt.
    
    Args:
        input_prompt: The prompt requiring includes
        available_includes: List of available include file paths
        strength: LLM model strength (0-1)
        temperature: LLM temperature setting
        
    Returns:
        Tuple containing:
        - output_prompt: Prompt with includes inserted
        - total_cost: Total cost of generation
        - model_name: Name of selected LLM model
    """
    try:
        # Step 1: Load prompt templates
        auto_include_template = load_prompt_template('auto_include_LLM.prompt')
        extract_template = load_prompt_template('extract_auto_include_LLM.prompt')

        # Step 2-3: Create LCEL template and get LLM
        auto_include_prompt = PromptTemplate.from_template(auto_include_template)
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)

        # Step 4: Run first prompt
        input_vars = {
            "input_prompt": input_prompt,
            "available_includes": str(available_includes)
        }
        
        input_tokens = token_counter(auto_include_prompt.format(**input_vars))
        input_cost_amount = calculate_cost(input_tokens, input_cost)
        
        console.print(f"[bold blue]Running auto-include analysis...[/]")
        console.print(f"Input tokens: {input_tokens}")
        console.print(f"Estimated input cost: ${input_cost_amount:.6f}")

        chain = auto_include_prompt | llm
        first_result = chain.invoke(input_vars)

        # Step 5: Pretty print results
        console.print(Markdown(str(first_result)))
        output_tokens = token_counter(str(first_result))
        output_cost_amount = calculate_cost(output_tokens, output_cost)
        console.print(f"Output tokens: {output_tokens}")
        console.print(f"Estimated output cost: ${output_cost_amount:.6f}")

        # Step 6-7: Create extract template and parser
        extract_prompt = PromptTemplate.from_template(extract_template)
        parser = JsonOutputParser(pydantic_object=ExtractedIncludes)

        # Step 8: Run extraction
        extract_vars = {"llm_output": str(first_result)}
        extract_tokens = token_counter(extract_prompt.format(**extract_vars))
        extract_cost_amount = calculate_cost(extract_tokens, input_cost)
        
        console.print(f"[bold blue]Extracting includes...[/]")
        console.print(f"Extract input tokens: {extract_tokens}")
        console.print(f"Estimated extract cost: ${extract_cost_amount:.6f}")

        extract_chain = extract_prompt | llm | parser
        extracted_result = extract_chain.invoke(extract_vars)

        # Step 10-12: Prepare final output
        includes_str = extracted_result.get('string_of_includes')
        output_prompt = f"{includes_str}\n{input_prompt}"
        
        total_cost = (
            input_cost_amount + 
            output_cost_amount + 
            extract_cost_amount + 
            calculate_cost(token_counter(str(extracted_result)), output_cost)
        )

        return output_prompt, total_cost, model_name

    except Exception as e:
        console.print(f"[bold red]Error in auto_include:[/] {str(e)}")
        raise
