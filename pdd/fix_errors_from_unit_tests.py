import os
import tempfile  # Added missing import
from datetime import datetime
from typing import Tuple, Optional
from pydantic import BaseModel, Field, ValidationError
from rich import print as rprint
from rich.markdown import Markdown
from rich.console import Console
from rich.panel import Panel
from tempfile import NamedTemporaryFile

from . import DEFAULT_STRENGTH
from . import DEFAULT_TIME, EXTRACTION_STRENGTH
from .preprocess import preprocess
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke

console = Console()

class CodeFix(BaseModel):
    update_unit_test: bool = Field(description="Whether the unit test needs to be updated")
    update_code: bool = Field(description="Whether the code needs to be updated")
    fixed_unit_test: str = Field(description="The fixed unit test code")
    fixed_code: str = Field(description="The fixed code under test")

def validate_inputs(strength: float, temperature: float) -> None:
    """Validate strength and temperature parameters."""
    if not 0 <= strength <= 1:
        raise ValueError("Strength must be between 0 and 1")
    if not 0 <= temperature <= 1:
        raise ValueError("Temperature must be between 0 and 1")

def write_to_error_file(file_path: str, content: str) -> None:
    """Write content to error file with timestamp and separator."""
    try:
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        separator = f"\n{'='*80}\n{timestamp}\n{'='*80}\n"
        
        # Ensure parent directory exists
        parent_dir = os.path.dirname(file_path)
        use_fallback = False
        
        if parent_dir:
            try:
                os.makedirs(parent_dir, exist_ok=True)
            except Exception as e:
                console.print(f"[yellow]Warning: Could not create directory {parent_dir}: {str(e)}[/yellow]")
                # Fallback to system temp directory
                use_fallback = True
                parent_dir = None
        
        # Use atomic write with temporary file
        try:
            # First read existing content if file exists
            existing_content = ""
            if os.path.exists(file_path):
                try:
                    with open(file_path, 'r') as f:
                        existing_content = f.read()
                except Exception as e:
                    console.print(f"[yellow]Warning: Could not read existing file {file_path}: {str(e)}[/yellow]")

            # Write both existing and new content to temp file
            with NamedTemporaryFile(mode='w', dir=parent_dir, delete=False) as tmp_file:
                if existing_content:
                    tmp_file.write(existing_content)
                tmp_file.write(f"{separator}{content}\n")
                tmp_path = tmp_file.name
            
            # Only attempt atomic move if not using fallback
            if not use_fallback:
                try:
                    os.replace(tmp_path, file_path)
                except Exception as e:
                    console.print(f"[yellow]Warning: Could not move file to {file_path}: {str(e)}[/yellow]")
                    use_fallback = True
            
            if use_fallback:
                # Write to fallback location in system temp directory
                fallback_path = os.path.join(tempfile.gettempdir(), os.path.basename(file_path))
                try:
                    os.replace(tmp_path, fallback_path)
                    console.print(f"[yellow]Warning: Using fallback location: {fallback_path}[/yellow]")
                except Exception as e:
                    console.print(f"[red]Error writing to fallback location: {str(e)}[/red]")
                    try:
                        os.unlink(tmp_path)
                    except:
                        pass
                    raise
        except Exception as e:
            console.print(f"[red]Error writing to error file: {str(e)}[/red]")
            try:
                os.unlink(tmp_path)
            except:
                pass
            raise
    except Exception as e:
        console.print(f"[red]Error in write_to_error_file: {str(e)}[/red]")
        raise

def fix_errors_from_unit_tests(
    unit_test: str,
    code: str,
    prompt: str,
    error: str,
    error_file: str,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    verbose: bool = False,
    time: float = DEFAULT_TIME
) -> Tuple[bool, bool, str, str, str, float, str]:
    """
    Fix errors in unit tests using LLM models and log the process.

    Args:
        unit_test (str): The unit test code, potentially multiple files concatenated
                         with <file name="filename.py">...</file> tags.
        code (str): The code under test
        prompt (str): The prompt that generated the code
        error (str): The error message
        error_file (str): Path to error log file
        strength (float): LLM model strength (0-1)
        temperature (float): LLM temperature (0-1)
        verbose (bool): Whether to print detailed output
        time (float): Time parameter for llm_invoke

    Returns:
        Tuple containing update flags, fixed code/tests, total cost, and model name
    """
    # Input validation
    if not all([unit_test, code, prompt, error, error_file]):
        raise ValueError("All input parameters must be non-empty")
    
    validate_inputs(strength, temperature)

    total_cost = 0.0
    model_name = ""

    try:
        # Step 1: Load prompt templates
        fix_errors_prompt = load_prompt_template("fix_errors_from_unit_tests_LLM")
        extract_fix_prompt = load_prompt_template("extract_unit_code_fix_LLM")
        
        if not fix_errors_prompt or not extract_fix_prompt:
            raise ValueError("Failed to load prompt templates")

        # Step 2: Read error file content
        existing_errors = ""
        try:
            if os.path.exists(error_file):
                with open(error_file, 'r', encoding='utf-8') as f:
                    existing_errors = f.read()
        except Exception as e:
            if verbose:
                console.print(f"[yellow]Warning: Could not read error file: {str(e)}[/yellow]")

        # Step 3: Run first prompt through llm_invoke
        processed_prompt = preprocess(
            prompt,
            recursive=False,
            double_curly_brackets=True
        )
        
        processed_fix_errors_prompt = preprocess(
            fix_errors_prompt,
            recursive=False,
            double_curly_brackets=True,
            exclude_keys=['unit_test', 'code', 'errors', 'prompt']
        )

        if verbose:
            console.print(Panel("[bold green]Running fix_errors_from_unit_tests...[/bold green]"))

        response1 = llm_invoke(
            prompt=processed_fix_errors_prompt,
            input_json={
                "unit_test": unit_test,
                "code": code,
                "prompt": processed_prompt,
                "errors": error
            },
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            time=time
        )

        total_cost += response1['cost']
        model_name = response1['model_name']
        result1 = response1['result']

        # Step 4: Pretty print results and log to error file
        if verbose:
            console.print(Markdown(result1))
            console.print(f"Cost of first run: ${response1['cost']:.6f}")

        write_to_error_file(error_file, f"Model: {model_name}\nResult:\n{result1}")

        # Step 5: Preprocess extract_fix prompt
        processed_extract_prompt = preprocess(
            extract_fix_prompt,
            recursive=False,
            double_curly_brackets=True,
            exclude_keys=['unit_test', 'code', 'unit_test_fix']
        )

        # Step 6: Run second prompt through llm_invoke with fixed strength
        if verbose:
            console.print(Panel("[bold green]Running extract_unit_code_fix...[/bold green]"))

        response2 = llm_invoke(
            prompt=processed_extract_prompt,
            input_json={
                "unit_test_fix": result1,
                "unit_test": unit_test,
                "code": code
            },
            strength=EXTRACTION_STRENGTH,  # Fixed strength as per requirements
            temperature=temperature,
            output_pydantic=CodeFix,
            verbose=verbose,
            time=time
        )

        total_cost += response2['cost']
        result2: CodeFix = response2['result']

        if verbose:
            console.print(f"Total cost: ${total_cost:.6f}")
            console.print(f"Model used: {model_name}")

        return (
            result2.update_unit_test,
            result2.update_code,
            result2.fixed_unit_test,
            result2.fixed_code,
            result1,
            total_cost,
            model_name
        )

    except ValidationError as e:
        error_msg = f"Validation error in fix_errors_from_unit_tests: {str(e)}"
        if verbose:
            console.print(f"[bold red]{error_msg}[/bold red]")
        write_to_error_file(error_file, error_msg)
        return False, False, "", "", "", 0.0, f"Error: ValidationError - {str(e)[:100]}"
    except Exception as e:
        error_msg = f"Error in fix_errors_from_unit_tests: {str(e)}"
        if verbose:
            console.print(f"[bold red]{error_msg}[/bold red]")
        write_to_error_file(error_file, error_msg)
        return False, False, "", "", "", 0.0, f"Error: {type(e).__name__}"