import os
from pathlib import Path
from typing import Tuple, List
from rich import print as rprint
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import JsonOutputParser
from pydantic import BaseModel, Field
from .llm_selector import llm_selector

class ExtractedIncludes(BaseModel):
    string_of_includes: str = Field(description="The string of includes to be added to the prompt")

def load_prompt_file(filename: str) -> str:
    """Load prompt from file in the prompts directory."""
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
    strength: float = 0.5,
    temperature: float = 1.0
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
        - model_name: Name of selected model
    """
    try:
        # Step 1-3: Load prompt and setup LLM
        auto_include_prompt = load_prompt_file('auto_include_LLM.prompt')
        llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)
        
        # Create prompt template
        prompt_template = PromptTemplate.from_template(auto_include_prompt)
        
        # Step 4: Run through model
        chain = prompt_template | llm
        
        # Calculate and display initial tokens/cost
        prompt_tokens = token_counter(str({"input_prompt": input_prompt, "available_includes": available_includes}))
        prompt_cost = calculate_cost(prompt_tokens, input_cost)
        
        rprint(f"[bold blue]Running auto-include analysis...[/bold blue]")
        rprint(f"Prompt tokens: {prompt_tokens}")
        rprint(f"Estimated prompt cost: ${prompt_cost:.6f}")
        
        # Run the chain
        result = chain.invoke({
            "input_prompt": input_prompt,
            "available_includes": available_includes
        })
        
        # Step 5: Pretty print results
        rprint(Markdown(str(result)))
        result_tokens = token_counter(str(result))
        result_cost = calculate_cost(result_tokens, output_cost)
        rprint(f"Result tokens: {result_tokens}")
        rprint(f"Result cost: ${result_cost:.6f}")
        
        # Step 6-8: Extract includes
        extract_prompt = load_prompt_file('extract_auto_include_LLM.prompt')
        extract_template = PromptTemplate.from_template(extract_prompt)
        
        # Setup JSON parser
        parser = JsonOutputParser(pydantic_object=ExtractedIncludes)
        extract_chain = extract_template | llm | parser
        
        # Step 9: Run extraction
        extract_tokens = token_counter(str(result))
        extract_prompt_cost = calculate_cost(extract_tokens, input_cost)
        
        rprint(f"[bold blue]Extracting includes...[/bold blue]")
        rprint(f"Extract prompt tokens: {extract_tokens}")
        rprint(f"Estimated extract cost: ${extract_prompt_cost:.6f}")
        
        extracted = extract_chain.invoke({"llm_output": str(result)})
        
        # Step 10-12: Prepare final output
        output_prompt = extracted.string_of_includes + "\n" + input_prompt
        total_cost = prompt_cost + result_cost + extract_prompt_cost
        
        return output_prompt, total_cost, model_name
        
    except Exception as e:
        rprint(f"[bold red]Error in auto_include:[/bold red] {str(e)}")
        raise
