from typing import Tuple
from pydantic import BaseModel, Field
from rich import print
from rich.markdown import Markdown
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke

class CodeFix(BaseModel):
    update_program: bool = Field(description="Indicates if the program needs updating")
    update_code: bool = Field(description="Indicates if the code module needs updating")
    fixed_program: str = Field(description="The fixed program code")
    fixed_code: str = Field(description="The fixed code module")

def fix_code_module_errors(
    program: str,
    prompt: str,
    code: str,
    errors: str,
    strength: float,
    temperature: float = 0,
    verbose: bool = False
) -> Tuple[bool, bool, str, str, float, str]:
    """
    Fix errors in a code module that caused a program to crash and/or have errors.

    Args:
        program (str): The program code that was running the code module
        prompt (str): The prompt that generated the code module
        code (str): The code module that caused the crash
        errors (str): The errors from the program run
        strength (float): The strength of the LLM model to use (0-1)
        temperature (float, optional): The temperature of the LLM model. Defaults to 0.
        verbose (bool, optional): Whether to print detailed information. Defaults to False.

    Returns:
        Tuple[bool, bool, str, str, float, str]: Returns update flags, fixed code, cost, and model name
    """
    try:
        # Step 1: Load prompt templates
        fix_prompt = load_prompt_template("fix_code_module_errors_LLM")
        extract_prompt = load_prompt_template("extract_program_code_fix_LLM")
        
        if not all([fix_prompt, extract_prompt]):
            raise ValueError("Failed to load one or more prompt templates")

        total_cost = 0
        model_name = ""

        # Step 2: First LLM invoke for error analysis
        input_json = {
            "program": program,
            "prompt": prompt,
            "code": code,
            "errors": errors
        }

        if verbose:
            print("[blue]Running initial error analysis...[/blue]")

        first_response = llm_invoke(
            prompt=fix_prompt,
            input_json=input_json,
            strength=strength,
            temperature=temperature,
            verbose=verbose
        )

        total_cost += first_response['cost']
        model_name = first_response['model_name']

        if verbose:
            print("[green]Error analysis complete[/green]")
            print(Markdown(first_response['result']))
            print(f"[yellow]Current cost: ${total_cost:.6f}[/yellow]")

        # Step 4: Second LLM invoke for code extraction
        extract_input = {
            "program_code_fix": first_response['result'],
            "program": program,
            "code": code
        }

        if verbose:
            print("[blue]Extracting code fixes...[/blue]")

        second_response = llm_invoke(
            prompt=extract_prompt,
            input_json=extract_input,
            strength=0.89,  # Fixed strength as specified
            temperature=temperature,
            verbose=verbose,
            output_pydantic=CodeFix
        )

        total_cost += second_response['cost']

        # Step 5: Extract values from Pydantic result
        result: CodeFix = second_response['result']
        
        if verbose:
            print("[green]Code extraction complete[/green]")
            print(f"[yellow]Total cost: ${total_cost:.6f}[/yellow]")
            print(f"[blue]Model used: {model_name}[/blue]")

        # Step 7: Return results
        return (
            result.update_program,
            result.update_code,
            result.fixed_program,
            result.fixed_code,
            total_cost,
            model_name
        )

    except ValueError as ve:
        print(f"[red]Value Error: {str(ve)}[/red]")
        raise
    except Exception as e:
        print(f"[red]Unexpected error: {str(e)}[/red]")
        raise

def validate_inputs(
    program: str,
    prompt: str,
    code: str,
    errors: str,
    strength: float
) -> None:
    """Validate input parameters."""
    if not all([program, prompt, code, errors]):
        raise ValueError("All string inputs (program, prompt, code, errors) must be non-empty")
    
    if not isinstance(strength, (int, float)):
        raise ValueError("Strength must be a number")
    
    if not 0 <= strength <= 1:
        raise ValueError("Strength must be between 0 and 1")