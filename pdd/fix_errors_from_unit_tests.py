import os
import re
import json
import asyncio
import tempfile
from datetime import datetime
from typing import Dict, Tuple, Any, Optional, List, Union
import psutil  # Add psutil import for process management

from rich.console import Console
from rich.markdown import Markdown
from rich.panel import Panel
from rich.text import Text

from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke
from .preprocess import preprocess
from .edit_file import edit_file, run_edit_in_subprocess
from langchain_mcp_adapters.client import MultiServerMCPClient

console = Console()

async def _fix_errors_from_unit_tests_async(
    unit_test: str,
    code: str,
    prompt: str,
    error: str,
    error_file: str,
    strength: float,
    temperature: float = 0.0,
    verbose: bool = False
) -> Tuple[bool, bool, str, str, str, float, str]:
    """
    Fix unit test errors and warnings in code files.
    
    Args:
        unit_test: The unit test code as a string
        code: The code under test as a string
        prompt: The prompt that generated the code under test
        error: Errors and warnings that need to be fixed
        error_file: Path to the file where error logs will be appended
        strength: Strength of the LLM model to use (0-1)
        temperature: Temperature for LLM output (0-1)
        verbose: Whether to print detailed information
        
    Returns:
        Tuple containing:
            - update_unit_test: Boolean indicating if unit test was updated
            - update_code: Boolean indicating if code was updated
            - fixed_unit_test: The fixed unit test code
            - fixed_code: The fixed code under test
            - analysis_results: The raw output of the LLM analysis
            - total_cost: Total cost of LLM invocations
            - model_name: Name of the LLM model used
    """
    # Initialize variables to track costs and model
    total_cost = 0.0
    model_name = ""
    
    # Step 1: Load the prompt template
    if verbose:
        console.print("[bold blue]Step 1: Loading prompt template...[/bold blue]")
    
    console.print("[bold yellow]DEBUG: About to load prompt template[/bold yellow]")
    prompt_template = load_prompt_template("fix_errors_from_unit_tests_LLM")
    console.print(f"[bold yellow]DEBUG: Prompt template loaded: {'Success' if prompt_template else 'Failed'}[/bold yellow]")
    
    if not prompt_template:
        error_msg = "Failed to load prompt template 'fix_errors_from_unit_tests_LLM'"
        if verbose:
            console.print(f"[bold red]{error_msg}[/bold red]")
        raise ValueError(error_msg)
        
    if verbose:
        console.print("[bold green]Prompt template loaded successfully[/bold green]")
    
    # Step 2: Read contents of error_file and parse any previous fix attempts
    if verbose:
        console.print("[bold blue]Step 2: Reading error file for previous fixes...[/bold blue]")
    
    prior_fixes = ""
    try:
        if os.path.exists(error_file):
            console.print("[bold yellow]DEBUG: Reading error file[/bold yellow]")
            with open(error_file, 'r') as f:
                prior_fixes = f.read()
            
            if verbose:
                console.print(f"[bold green]Found existing error file: {error_file}[/bold green]")
        else:
            if verbose:
                console.print(f"[bold yellow]Creating new error file: {error_file}[/bold yellow]")
                
            # Ensure directory exists
            os.makedirs(os.path.dirname(os.path.abspath(error_file)), exist_ok=True)
    except Exception as e:
        if verbose:
            console.print(f"[bold red]Error reading error file: {str(e)}[/bold red]")
        prior_fixes = f"Error reading prior fixes: {str(e)}"
    
    # Step 3: Run the LLM analysis prompt through llm_invoke
    if verbose:
        console.print("[bold blue]Step 3: Running LLM analysis...[/bold blue]")
    
    # Preprocess the prompt
    try:
        console.print("[bold yellow]DEBUG: Preprocessing prompt[/bold yellow]")
        processed_prompt = preprocess(
            prompt,
            recursive=False,
            double_curly_brackets=True,
            exclude_keys=['unit_test', 'code', 'unit_test_fix']
        )
        console.print("[bold yellow]DEBUG: Prompt preprocessed successfully[/bold yellow]")
    except Exception as e:
        processed_prompt = prompt
        if verbose:
            console.print(f"[bold yellow]Error during prompt preprocessing, using original prompt: {str(e)}[/bold yellow]")
    
    # Prepare input for LLM
    llm_input = {
        'unit_test': unit_test,
        'code': code,
        'prompt': processed_prompt,
        'errors': error,
        'prior_fixes': prior_fixes
    }
    
    # Log to console if verbose
    if verbose:
        console.print(Panel(
            Text("Running LLM analysis", style="bold white"),
            subtitle=f"Strength: {strength}, Temperature: {temperature}"
        ))
        console.print(f"Input tokens: {len(unit_test.split()) + len(code.split()) + len(processed_prompt.split()) + len(error.split())}")
    
    # Run the LLM analysis
    try:
        console.print("[bold yellow]DEBUG: About to invoke LLM[/bold yellow]")
        llm_response = llm_invoke(
            prompt=prompt_template,
            input_json=llm_input,
            strength=strength,
            temperature=temperature,
            verbose=verbose
        )
        console.print("[bold yellow]DEBUG: LLM invocation completed[/bold yellow]")
        
        # Update tracking variables
        total_cost += llm_response['cost']
        model_name = llm_response['model_name']
        
        # Extract response
        analysis_results = llm_response['result']
        
        # Display response if verbose
        if verbose:
            console.print("\n[bold green]LLM Analysis Complete[/bold green]")
            console.print(Markdown(analysis_results))
            console.print(f"[bold]Output tokens: {llm_response.get('output_tokens', 'unknown')}[/bold]")
            console.print(f"[bold]Cost: ${llm_response['cost']:.6f}[/bold]")
    
    except Exception as e:
        error_msg = f"Error during LLM analysis: {str(e)}"
        if verbose:
            console.print(f"[bold red]{error_msg}[/bold red]")
        
        # Log the error to the error file
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        error_log = f"\n\n{'='*50}\nERROR LOG - {timestamp}\n{'='*50}\n{error_msg}\n"
        
        try:
            with open(error_file, 'a') as f:
                f.write(error_log)
        except Exception as file_err:
            if verbose:
                console.print(f"[bold red]Failed to write to error file: {str(file_err)}[/bold red]")
        
        # Return default values
        return False, False, unit_test, code, "", total_cost, model_name
    
    # Extract corrected code sections using regex
    if verbose:
        console.print("[bold blue]Step 3d: Extracting code sections...[/bold blue]")
    
    # Extract sections using regex
    corrected_code_match = re.search(r'<corrected_code_under_test>(.*?)</corrected_code_under_test>', analysis_results, re.DOTALL)
    corrected_unit_test_match = re.search(r'<corrected_unit_test>(.*?)</corrected_unit_test>', analysis_results, re.DOTALL)
    
    # Extract corrected code sections from the regex matches
    corrected_code_text = ""
    corrected_unit_test_text = ""
    
    if corrected_code_match:
        corrected_code_text = corrected_code_match.group(1).strip()
    
    if corrected_unit_test_match:
        corrected_unit_test_text = corrected_unit_test_match.group(1).strip()
        
    if verbose:
        console.print(f"[bold yellow]Extracted code text: {bool(corrected_code_text)}[/bold yellow]")
        console.print(f"[bold yellow]Extracted test text: {bool(corrected_unit_test_text)}[/bold yellow]")
    
    # Step 3c: Append the output to error_file
    if verbose:
        console.print("[bold blue]Step 3c: Logging analysis results...[/bold blue]")
    
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    log_entry = f"\n\n{'='*50}\nANALYSIS LOG - {timestamp}\n{'='*50}\n{analysis_results}\n"
    
    try:
        with open(error_file, 'a') as f:
            f.write(log_entry)
        
        if verbose:
            console.print(f"[bold green]Analysis logged to {error_file}[/bold green]")
    except Exception as e:
        if verbose:
            console.print(f"[bold red]Failed to write to error file: {str(e)}[/bold red]")
    
    # Step 4: Pretty print the analysis results if verbose
    if verbose:
        console.print("[bold blue]Step 4: Displaying analysis results...[/bold blue]")
        console.print(Panel(
            Markdown(analysis_results),
            title="Analysis Results",
            expand=False
        ))
    
    # Initialize variables for return values
    update_unit_test = False
    update_code = False
    fixed_unit_test = unit_test
    fixed_code = code
    
    # Step 5: Use edit_file to apply the fixes
    if verbose:
        console.print("[bold blue]Step 5: Applying fixes...[/bold blue]")
    
    # Step 5a: Apply unit test fixes if available
    if corrected_unit_test_text:
        try:
            # Create a temporary file for the unit test
            with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as temp_file:
                temp_test_file = temp_file.name
                temp_file.write(unit_test)
            
            if verbose:
                console.print(f"[bold]Applying unit test fixes...[/bold]")
            
            # Apply fixes using run_edit_in_subprocess for process isolation
            test_success, test_error = run_edit_in_subprocess(
                file_path=temp_test_file,
                edit_instructions=corrected_unit_test_text
            )
            
            # Read the modified file
            if test_success and os.path.exists(temp_test_file):
                with open(temp_test_file, 'r') as f:
                    fixed_unit_test = f.read()
                update_unit_test = True
                
                if verbose:
                    console.print(f"[bold green]Unit test fixes applied successfully[/bold green]")
            else:
                if verbose:
                    console.print(f"[bold red]Failed to apply unit test fixes: {test_error}[/bold red]")
            
            # Clean up
            if os.path.exists(temp_test_file):
                os.remove(temp_test_file)
            
        except Exception as e:
            if verbose:
                console.print(f"[bold red]Error applying unit test fixes: {str(e)}[/bold red]")
    else:
        if verbose:
            console.print("[bold yellow]No unit test fixes required or provided[/bold yellow]")
    
    # Step 5b: Apply code fixes if available
    if corrected_code_text:
        try:
            # Create a temporary file for the code
            with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as temp_file:
                temp_code_file = temp_file.name
                temp_file.write(code)
            
            if verbose:
                console.print(f"[bold]Applying code fixes...[/bold]")
            
            # Apply fixes using run_edit_in_subprocess for process isolation
            code_success, code_error = run_edit_in_subprocess(
                file_path=temp_code_file,
                edit_instructions=corrected_code_text
            )
            
            # Read the modified file
            if code_success and os.path.exists(temp_code_file):
                with open(temp_code_file, 'r') as f:
                    fixed_code = f.read()
                update_code = True
                
                if verbose:
                    console.print(f"[bold green]Code fixes applied successfully[/bold green]")
            else:
                if verbose:
                    console.print(f"[bold red]Failed to apply code fixes: {code_error}[/bold red]")
            
            # Clean up
            if os.path.exists(temp_code_file):
                os.remove(temp_code_file)
            
        except Exception as e:
            if verbose:
                console.print(f"[bold red]Error applying code fixes: {str(e)}[/bold red]")
    else:
        if verbose:
            console.print("[bold yellow]No code fixes required or provided[/bold yellow]")
    
    # Step 6: Return the results
    if verbose:
        console.print("[bold blue]Step 6: Returning results...[/bold blue]")
        console.print(f"[bold green]Fix process completed[/bold green]")
        console.print(f"[bold]Update unit test: {update_unit_test}[/bold]")
        console.print(f"[bold]Update code: {update_code}[/bold]")
        console.print(f"[bold]Total cost: ${total_cost:.6f}[/bold]")
        console.print(f"[bold]Model used: {model_name}[/bold]")
    
    # One final cleanup of any lingering processes before returning
    # terminate_mcp_processes()  # Removed as this function doesn't exist in edit_file.py
    
    return (
        update_unit_test,
        update_code,
        fixed_unit_test,
        fixed_code,
        analysis_results,
        total_cost,
        model_name
    )

def fix_errors_from_unit_tests(
    unit_test: str,
    code: str,
    prompt: str,
    error: str,
    error_file: str,
    strength: float,
    temperature: float = 0.0,
    verbose: bool = False
) -> Tuple[bool, bool, str, str, str, float, str]:
    """
    Synchronous wrapper for fixing unit test errors and warnings in code files.
    
    Args:
        unit_test: The unit test code as a string
        code: The code under test as a string
        prompt: The prompt that generated the code under test
        error: Errors and warnings that need to be fixed
        error_file: Path to the file where error logs will be appended
        strength: Strength of the LLM model to use (0-1)
        temperature: Temperature for LLM output (0-1)
        verbose: Whether to print detailed information
        
    Returns:
        Tuple containing:
            - update_unit_test: Boolean indicating if unit test was updated
            - update_code: Boolean indicating if code was updated
            - fixed_unit_test: The fixed unit test code
            - fixed_code: The fixed code under test
            - analysis_results: The raw output of the LLM analysis
            - total_cost: Total cost of LLM invocations
            - model_name: Name of the LLM model used
    """
    # Input validation
    if not isinstance(unit_test, str) or not isinstance(code, str) or not isinstance(prompt, str) or not isinstance(error, str):
        raise ValueError("Input parameters must be strings")
    
    if not isinstance(error_file, str) or not error_file:
        raise ValueError("error_file must be a non-empty string")
    
    if not isinstance(strength, float) or strength < 0 or strength > 1:
        strength = max(0, min(strength, 1))  # Clamp to 0-1 range instead of raising error
    
    if not isinstance(temperature, float) or temperature < 0 or temperature > 1:
        temperature = max(0, min(temperature, 1))  # Clamp to 0-1 range instead of raising error
    
    # Create and use new event loop instead of trying to get the current one (which causes deprecation warning)
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    
    try:
        # Run the async function and return results
        return loop.run_until_complete(_fix_errors_from_unit_tests_async(
            unit_test=unit_test,
            code=code,
            prompt=prompt,
            error=error,
            error_file=error_file,
            strength=strength,
            temperature=temperature,
            verbose=verbose
        ))
    finally:
        # Clean up the loop
        loop.close()