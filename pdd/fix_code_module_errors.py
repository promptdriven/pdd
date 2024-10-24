import os
from pathlib import Path
from typing import Tuple, Any
from rich.console import Console
from rich.markdown import Markdown
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import JsonOutputParser
from langchain_core.output_parsers import StrOutputParser
from pydantic import BaseModel, Field
from .llm_selector import llm_selector

console = Console()

class CodeFix(BaseModel):
    update_program: bool = Field(description="Whether the program needs to be updated")
    update_code: bool = Field(description="Whether the code module needs to be updated")
    fixed_program: str = Field(description="The fixed program code")
    fixed_code: str = Field(description="The fixed code module")

def fix_code_module_errors(
    program: str,
    prompt: str,
    code: str,
    errors: str,
    strength: float,
    temperature: float = 0
) -> Tuple[bool, bool, str, str, float, str]:
    """
    Fix errors in a code module that caused a program to crash.
    
    Args:
        program (str): The program code that was running the code module
        prompt (str): The prompt that generated the code module
        code (str): The code module that caused the crash
        errors (str): The errors from the program run
        strength (float): The strength of the LLM model to use (0-1)
        temperature (float): The temperature of the LLM model to use
        
    Returns:
        Tuple containing:
        - update_program (bool): Whether the program needs to be updated
        - update_code (bool): Whether the code module needs to be updated
        - fixed_program (str): The fixed program
        - fixed_code (str): The fixed code module
        - total_cost (float): The total cost of the run
        - model_name (str): The name of the selected LLM model
    """
    
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
    
    input_tokens = token_counter(fix_prompt.format(**input_vars))
    input_cost_dollars = (input_tokens * input_cost) / 1_000_000
    
    console.print(f"[bold blue]Running fix analysis...[/bold blue]")
    console.print(f"Input tokens: {input_tokens}")
    console.print(f"Estimated input cost: ${input_cost_dollars:.4f}")
    
    fix_result = fix_chain.invoke(input_vars)

    # Step 5: Print results
    output_tokens = token_counter(fix_result)
    output_cost_dollars = (output_tokens * output_cost) / 1_000_000
    
    console.print(Markdown(fix_result))
    console.print(f"Output tokens: {output_tokens}")
    console.print(f"Output cost: ${output_cost_dollars:.4f}")

    # Step 6 & 7: Create second LCEL template with JSON parser
    extract_llm, token_counter2, input_cost2, output_cost2, _ = llm_selector(0.8, temperature)
    
    parser = JsonOutputParser(pydantic_object=CodeFix)
    extract_prompt = PromptTemplate(
        template=extract_prompt_template,
        partial_variables={"format_instructions": parser.get_format_instructions()}
    )
    
    extract_chain = extract_prompt | extract_llm | parser

    # Step 8: Run second chain
    input_vars2 = {
        "program_code_fix": fix_result,
        "program": program,
        "code": code
    }
    
    input_tokens2 = token_counter2(extract_prompt.format(**input_vars2))
    input_cost_dollars2 = (input_tokens2 * input_cost2) / 1_000_000
    
    console.print(f"\n[bold blue]Extracting fixes...[/bold blue]")
    console.print(f"Input tokens: {input_tokens2}")
    console.print(f"Estimated input cost: ${input_cost_dollars2:.4f}")
    
    result = extract_chain.invoke(input_vars2)
    
    output_tokens2 = token_counter2(str(result))
    output_cost_dollars2 = (output_tokens2 * output_cost2) / 1_000_000

    # Step 9 & 10: Calculate total cost and return results
    total_cost = (input_cost_dollars + output_cost_dollars + 
                 input_cost_dollars2 + output_cost_dollars2)
    
    console.print(f"\n[bold green]Total cost: ${total_cost:.4f}[/bold green]")
    
    return (
        result.update_program,
        result.update_code,
        result.fixed_program,
        result.fixed_code,
        total_cost,
        model_name
    )