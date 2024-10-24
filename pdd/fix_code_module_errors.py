import os
from pathlib import Path
from typing import Tuple, Any
from rich.console import Console
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import JsonOutputParser
from langchain_core.output_parsers import StrOutputParser
from pydantic import BaseModel
from .llm_selector import llm_selector

console = Console()

def fix_code_module_errors(
    program: str,
    prompt: str,
    code: str,
    errors: str,
    strength: float,
    temperature: float = 0.0
) -> Tuple[bool, bool, str, str, float, str]:
    """
    Fix errors in a code module using LLMs.
    
    Args:
        program (str): The program code that was running the module
        prompt (str): The prompt that generated the code module
        code (str): The code module that caused the crash
        errors (str): The errors from the program run
        strength (float): The strength of the LLM model (0-1)
        temperature (float): The temperature of the LLM model
        
    Returns:
        Tuple containing:
        - update_program (bool): Whether the program needs updating
        - update_code (bool): Whether the code module needs updating
        - fixed_program (str): The fixed program code
        - fixed_code (str): The fixed code module
        - total_cost (float): Total cost of the LLM runs
        - model_name (str): Name of the selected model
    """
    
    # Validate inputs
    if not (0 <= strength <= 1):
        raise ValueError("Strength must be between 0 and 1")
    if not (0 <= temperature <= 1):
        raise ValueError("Temperature must be between 0 and 1")
    
    # Step 1: Load prompts
    pdd_path = os.getenv('PDD_PATH')
    if not pdd_path:
        raise ValueError("PDD_PATH environment variable not set")
        
    prompts_dir = Path(pdd_path) / "prompts"
    
    with open(prompts_dir / "fix_code_module_errors_LLM.prompt") as f:
        fix_prompt_template = f.read()
        
    with open(prompts_dir / "extract_program_code_fix_LLM.prompt") as f:
        extract_prompt_template = f.read()

    # Step 2 & 3: Create first LCEL template and get LLM
    llm, token_counter, input_cost, output_cost, model_name = llm_selector(strength, temperature)
    
    fix_prompt = PromptTemplate.from_template(fix_prompt_template)
    fix_chain = fix_prompt | llm | StrOutputParser()

    # Step 4: Run first chain
    input_vars = {
        "program": program,
        "prompt": prompt,
        "code": code,
        "errors": errors
    }
    
    prompt_tokens = token_counter(fix_prompt.format(**input_vars))
    prompt_cost = (prompt_tokens / 1_000_000) * input_cost
    
    console.print(f"[bold blue]Running fix analysis...[/bold blue]")
    console.print(f"Input tokens: {prompt_tokens}")
    console.print(f"Estimated input cost: ${prompt_cost:.4f}")
    
    fix_result = fix_chain.invoke(input_vars)

    # Step 5: Print results
    result_tokens = token_counter(fix_result)
    result_cost = (result_tokens / 1_000_000) * output_cost
    
    console.print("[bold green]Fix Analysis Results:[/bold green]")
    console.print(Markdown(fix_result))
    console.print(f"Output tokens: {result_tokens}")
    console.print(f"Output cost: ${result_cost:.4f}")

    # Step 6 & 7: Create second LCEL template with JSON parser
    extract_llm, token_counter, extract_input_cost, extract_output_cost, _ = llm_selector(0.8, temperature)
    
    class FixOutput(BaseModel):
        update_program: bool
        update_code: bool
        fixed_program: str
        fixed_code: str
    
    json_parser = JsonOutputParser(pydantic_object=FixOutput)
    
    extract_prompt = PromptTemplate(
        template=extract_prompt_template,
        partial_variables={"format_instructions": json_parser.get_format_instructions()}
    )
    
    extract_chain = extract_prompt | extract_llm | json_parser

    # Step 8: Run second chain
    extract_input = {
        "program_code_fix": fix_result,
        "program": program,
        "code": code
    }
    
    extract_prompt_tokens = token_counter(extract_prompt.format(**extract_input))
    extract_prompt_cost = (extract_prompt_tokens / 1_000_000) * extract_input_cost
    
    console.print(f"[bold blue]Extracting fixes...[/bold blue]")
    console.print(f"Input tokens: {extract_prompt_tokens}")
    console.print(f"Estimated input cost: ${extract_prompt_cost:.4f}")
    
    extract_result = extract_chain.invoke(extract_input)
    
    # Step 9: Calculate total cost
    total_cost = prompt_cost + result_cost + extract_prompt_cost

    # Step 10: Return results
    return (
        extract_result.get("update_program"),
        extract_result.get("update_code"),
        extract_result.get("fixed_program"),
        extract_result.get("fixed_code"),
        total_cost,
        model_name
    )