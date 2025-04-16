# -*- coding: utf-8 -*-
"""
Function to fix verification errors in a code module using LLMs.
"""

import re
from typing import Dict, Tuple, Optional

from pydantic import BaseModel, Field
from rich import print as rprint
from rich.markdown import Markdown

# Use relative imports for internal modules within the package
try:
    from .load_prompt_template import load_prompt_template
    from .llm_invoke import llm_invoke
except ImportError:
    # Handle cases where the script might be run directly
    from load_prompt_template import load_prompt_template # type: ignore
    from llm_invoke import llm_invoke # type: ignore

def fix_verification_errors(
    program: str,
    prompt: str,
    code: str,
    output: str,
    strength: float,
    temperature: float = 0.0,
    verbose: bool = False,
) -> Dict[str, any]:
    """
    Fixes issues in a code module identified during verification using LLMs.

    Args:
        program: The program code that was running the code module.
        prompt: The prompt that generated the code module.
        code: The code module to be fixed.
        output: The output logs from the program run containing verification details.
        strength: The strength of the LLM model to use (0 to 1).
        temperature: The temperature for the LLM model (default: 0).
        verbose: Whether to print detailed output (default: False).

    Returns:
        A dictionary containing:
        'issues_found': Boolean indicating if issues were found.
        'update_program': Boolean indicating if the program needs updating.
        'update_code': Boolean indicating if the code module needs updating.
        'fixed_program': The fixed program code.
        'fixed_code': The fixed code module.
        'total_cost': The total cost of the LLM calls.
        'model_name': The name of the LLM model used.

    Raises:
        ValueError: If required inputs are missing or invalid.
        FileNotFoundError: If prompt templates cannot be loaded.
        Exception: For errors during LLM invocation or processing.
    """
    if not all([program, prompt, code, output]):
        raise ValueError("Missing required inputs: 'program', 'prompt', 'code', or 'output'.")
    if not 0.0 <= strength <= 1.0:
        raise ValueError("'strength' must be between 0.0 and 1.0.")

    total_cost: float = 0.0
    model_name: Optional[str] = None
    issues_found: bool = False
    update_program: bool = False
    update_code: bool = False
    fixed_program: str = program
    fixed_code: str = code

    try:
        # Step 1: Load prompt templates
        if verbose:
            rprint("[bold blue]Step 1: Loading prompt templates...[/bold blue]")
        try:
            find_issues_prompt_template = load_prompt_template("find_verification_errors_LLM")
            fix_issues_prompt_template = load_prompt_template("fix_verification_errors_LLM")
            if verbose:
                rprint("[green]Prompt templates loaded successfully.[/green]")
        except FileNotFoundError as e:
            rprint(f"[bold red]Error loading prompt template: {e}[/bold red]")
            raise
        except Exception as e:
            rprint(f"[bold red]An unexpected error occurred loading prompts: {e}[/bold red]")
            raise

        # Step 2: Run LLM to find verification issues
        if verbose:
            rprint(f"\n[bold blue]Step 2: Running 'find_verification_errors_LLM' (Strength: {strength}, Temp: {temperature})...[/bold blue]")

        find_issues_input = {
            "program": program,
            "prompt": prompt,
            "code": code,
            "output": output,
        }

        try:
            verification_response = llm_invoke(
                prompt=find_issues_prompt_template,
                input_json=find_issues_input,
                strength=strength,
                temperature=temperature,
                verbose=verbose, # Pass verbose to llm_invoke for its internal printing
                output_pydantic=None # No structured output needed for this step
            )
            total_cost += verification_response.get('cost', 0.0)
            if model_name is None: # Capture model name from the first call
                 model_name = verification_response.get('model_name')
            verification_result_text = verification_response['result']

            # Step 3: Verbose output for verification result
            if verbose:
                rprint("[bold blue]Verification Result:[/bold blue]")
                rprint(Markdown(verification_result_text))
                rprint(f"Cost for verification step: ${verification_response.get('cost', 0.0):.6f}")

        except Exception as e:
            rprint(f"[bold red]Error during 'find_verification_errors_LLM' invocation: {e}[/bold red]")
            # Return default values indicating no fix was applied due to error
            return {
                'issues_found': False,
                'update_program': False,
                'update_code': False,
                'fixed_program': program,
                'fixed_code': code,
                'total_cost': total_cost,
                'model_name': model_name or "N/A",
            }

        # Step 4: Analyze verification result
        if verbose:
            rprint("\n[bold blue]Step 4: Analyzing verification result...[/bold blue]")

        issues_found_match = re.search(r"<issues_found>(true|false)</issues_found>", verification_result_text, re.IGNORECASE)

        if issues_found_match:
            issues_found = issues_found_match.group(1).lower() == "true"
            if verbose:
                rprint(f"Issues found based on <issues_found> tag: {issues_found}")
        else:
            issues_found = False # Default to false if tag is missing or malformed
            if verbose:
                rprint("[yellow]Warning: Could not find or parse <issues_found> tag. Assuming no issues found.[/yellow]")

        if not issues_found:
            if verbose:
                rprint("[green]No verification issues identified that require fixing.[/green]")
            # Return early as no fixes are needed
            return {
                'issues_found': False,
                'update_program': False,
                'update_code': False,
                'fixed_program': program,
                'fixed_code': code,
                'total_cost': total_cost,
                'model_name': model_name or "N/A",
            }

        # Extract details if issues were found
        details_match = re.search(r"<details>(.*?)</details>", verification_result_text, re.DOTALL | re.IGNORECASE)
        if details_match:
            issues_details = details_match.group(1).strip()
            if verbose:
                rprint("[cyan]Extracted Issue Details:[/cyan]")
                rprint(issues_details)
        else:
            issues_details = "No specific details extracted, but issues were indicated."
            if verbose:
                rprint("[yellow]Warning: <issues_found> was true, but could not find or parse <details> tag.[/yellow]")

        # Step 5: Run LLM to fix verification issues
        if verbose:
            rprint(f"\n[bold blue]Step 5: Running 'fix_verification_errors_LLM' (Strength: {strength}, Temp: {temperature})...[/bold blue]") # Using same strength/temp as find

        fix_issues_input = {
            "program": program,
            "prompt": prompt,
            "code": code,
            "output": output,
            "issues": issues_details,
        }

        try:
            fix_response = llm_invoke(
                prompt=fix_issues_prompt_template,
                input_json=fix_issues_input,
                strength=strength, # Use the same strength for consistency or adjust if needed
                temperature=temperature,
                verbose=verbose, # Pass verbose to llm_invoke
                output_pydantic=None # Expecting tagged text output, not Pydantic model
            )
            total_cost += fix_response.get('cost', 0.0)
            # Update model_name if it changed (unlikely if strength is same, but possible)
            model_name = fix_response.get('model_name', model_name)
            fix_result_text = fix_response['result']

            if verbose:
                rprint("[bold blue]Fix Result:[/bold blue]")
                # Use Markdown for potentially formatted LLM output
                rprint(Markdown(fix_result_text))
                rprint(f"Cost for fix step: ${fix_response.get('cost', 0.0):.6f}")

        except Exception as e:
            rprint(f"[bold red]Error during 'fix_verification_errors_LLM' invocation: {e}[/bold red]")
            # Return indicating issues were found but fixing failed
            return {
                'issues_found': True,
                'update_program': False,
                'update_code': False,
                'fixed_program': program,
                'fixed_code': code,
                'total_cost': total_cost,
                'model_name': model_name or "N/A",
            }

        # Step 6: Extract fixes and determine updates
        if verbose:
            rprint("\n[bold blue]Step 6: Extracting fixes and determining updates...[/bold blue]")

        # Extract fixed program
        fixed_program_match = re.search(r"<fixed_program>(.*?)</fixed_program>", fix_result_text, re.DOTALL | re.IGNORECASE)
        if fixed_program_match:
            fixed_program = fixed_program_match.group(1).strip()
            if verbose:
                rprint("[green]Successfully extracted fixed program.[/green]")
        else:
            fixed_program = program # Fallback to original
            if verbose:
                rprint("[yellow]Warning: Could not find or parse <fixed_program> tag. Using original program.[/yellow]")

        # Extract fixed code module
        fixed_code_match = re.search(r"<fixed_code>(.*?)</fixed_code>", fix_result_text, re.DOTALL | re.IGNORECASE)
        if fixed_code_match:
            fixed_code = fixed_code_match.group(1).strip()
            if verbose:
                rprint("[green]Successfully extracted fixed code module.[/green]")
        else:
            fixed_code = code # Fallback to original
            if verbose:
                rprint("[yellow]Warning: Could not find or parse <fixed_code> tag. Using original code module.[/yellow]")

        # Determine if updates occurred
        update_program = fixed_program != program
        update_code = fixed_code != code

        if verbose:
            rprint(f"Program needs update: {update_program}")
            rprint(f"Code module needs update: {update_code}")

        # Step 7: Verbose output for total cost
        if verbose:
            rprint(f"\n[bold blue]Step 7: Total Cost[/bold blue]")
            rprint(f"Total cost for the run: ${total_cost:.6f}")

        # Step 8: Return results
        return {
            'issues_found': True, # Issues were found and fixing was attempted
            'update_program': update_program,
            'update_code': update_code,
            'fixed_program': fixed_program,
            'fixed_code': fixed_code,
            'total_cost': total_cost,
            'model_name': model_name or "N/A",
        }

    except Exception as e:
        rprint(f"[bold red]An unexpected error occurred in fix_verification_errors: {e}[/bold red]")
        # Return default/error state
        return {
            'issues_found': False,
            'update_program': False,
            'update_code': False,
            'fixed_program': program,
            'fixed_code': code,
            'total_cost': total_cost,
            'model_name': model_name or "N/A",
        }