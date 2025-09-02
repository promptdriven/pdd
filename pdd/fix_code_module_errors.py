from typing import Tuple
from pydantic import BaseModel, Field, ValidationError
from rich import print
from rich.markdown import Markdown
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke
from . import EXTRACTION_STRENGTH, DEFAULT_TIME, DEFAULT_STRENGTH
import json

class CodeFix(BaseModel):
    update_program: bool = Field(description="Indicates if the program needs updating")
    update_code: bool = Field(description="Indicates if the code module needs updating")
    fixed_program: str = Field(description="The fixed program code")
    fixed_code: str = Field(description="The fixed code module")

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

def fix_code_module_errors(
    program: str,
    prompt: str,
    code: str,
    errors: str,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0,
    time: float = DEFAULT_TIME,
    verbose: bool = False
) -> Tuple[bool, bool, str, str, str, float, str]:
    """
    Fix errors in a code module that caused a program to crash and/or have errors.
    """
    try:
        # Validate inputs
        validate_inputs(program, prompt, code, errors, strength)

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
            time=time,
            verbose=verbose
        )

        total_cost += first_response.get('cost', 0)
        model_name = first_response.get('model_name', '')
        program_code_fix = first_response['result']

        # Check if the LLM response is None or an error string
        if program_code_fix is None:
            error_msg = "LLM returned None result during error analysis"
            if verbose:
                print(f"[red]{error_msg}[/red]")
            raise RuntimeError(error_msg)
        elif isinstance(program_code_fix, str) and program_code_fix.startswith("ERROR:"):
            error_msg = f"LLM failed to analyze errors: {program_code_fix}"
            if verbose:
                print(f"[red]{error_msg}[/red]")
            raise RuntimeError(error_msg)

        if verbose:
            print("[green]Error analysis complete[/green]")
            print(Markdown(program_code_fix))
            print(f"[yellow]Current cost: ${total_cost:.6f}[/yellow]")

        # Step 4: Second LLM invoke for code extraction
        extract_input = {
            "program_code_fix": program_code_fix,
            "program": program,
            "code": code
        }

        if verbose:
            print("[blue]Extracting code fixes...[/blue]")

        second_response = llm_invoke(
            prompt=extract_prompt,
            input_json=extract_input,
            strength=EXTRACTION_STRENGTH,  # Fixed strength for extraction
            temperature=temperature,
            time=time,
            verbose=verbose,
            output_pydantic=CodeFix
        )

        total_cost += second_response.get('cost', 0)

        # Step 5: Extract values from Pydantic result
        result = second_response['result']

        if isinstance(result, str):
            try:
                result_dict = json.loads(result)
            except json.JSONDecodeError:
                result_dict = {"result": result}
            result = CodeFix.model_validate(result_dict)
        elif isinstance(result, dict):
            result = CodeFix.model_validate(result)
        elif not isinstance(result, CodeFix):
            result = CodeFix.model_validate({"result": str(result)})

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
            program_code_fix,
            total_cost,
            model_name
        )

    except ValueError as ve:
        print(f"[red]Value Error: {str(ve)}[/red]")
        raise
    except ValidationError:
        print("[red]Validation Error: Invalid result format[/red]")
        raise
    except Exception as e:
        print(f"[red]Unexpected error: {str(e)}[/red]")
        raise