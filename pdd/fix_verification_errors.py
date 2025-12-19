from typing import Dict, Any, Optional
from rich import print as rprint
from rich.markdown import Markdown
from pydantic import BaseModel, Field
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke
from . import DEFAULT_TIME, DEFAULT_STRENGTH # Import defaults

# Define Pydantic model for structured LLM output for VERIFICATION
class VerificationOutput(BaseModel):
    issues_count: int = Field(description="The number of issues found during verification.")
    details: Optional[str] = Field(description="Detailed explanation of any discrepancies or issues found. Can be null or empty if issues_count is 0.", default=None)

# Define Pydantic model for structured LLM output for FIXES
class FixerOutput(BaseModel):
    explanation: str = Field(description="Detailed explanation of the analysis and fixes applied.")
    fixed_code: str = Field(description="The complete, runnable, and fixed code module.")
    fixed_program: str = Field(description="The complete, runnable, and fixed program that uses the code module.")

def fix_verification_errors(
    program: str,
    prompt: str,
    code: str,
    output: str,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    verbose: bool = False,
    time: float = DEFAULT_TIME
) -> Dict[str, Any]:
    """
    Identifies and fixes issues in a code module based on verification output.

    Args:
        program: The program code that ran the code module.
        prompt: The prompt used to generate the code module.
        code: The code module to be fixed.
        output: The output logs from the program run during verification.
        strength: The strength (0-1) for the LLM model selection.
        temperature: The temperature for the LLM model. Defaults to 0.
        verbose: If True, prints detailed execution information. Defaults to False.
        time: The time for the LLM model. Defaults to DEFAULT_TIME.

    Returns:
        A dictionary containing:
        - 'explanation': A string with verification details and fix explanation
                         in XML format, or None if no issues were found.
        - 'fixed_program': The potentially fixed program code string.
        - 'fixed_code': The potentially fixed code module string.
        - 'total_cost': The total cost incurred from LLM calls.
        - 'model_name': The name of the LLM model used.
        - 'verification_issues_count': The number of issues found during verification.
    """
    total_cost = 0.0
    model_name = None
    verification_issues_count = 0
    verification_details = None
    fix_explanation = None
    fixed_program = program # Initialize with original program
    fixed_code = code       # Initialize with original code
    final_explanation = None

    # Check only essential inputs, allow empty output
    if not all([program, prompt, code]):
        rprint("[bold red]Error:[/bold red] Missing one or more required inputs (program, prompt, code).")
        return {
            "explanation": None,
            "fixed_program": program,
            "fixed_code": code,
            "total_cost": 0.0,
            "model_name": None,
            "verification_issues_count": 0,
        }
    if not (0.0 <= strength <= 1.0):
        rprint(f"[bold red]Error:[/bold red] Strength must be between 0.0 and 1.0, got {strength}.")
        return {
            "explanation": None,
            "fixed_program": program,
            "fixed_code": code,
            "total_cost": 0.0,
            "model_name": None,
            "verification_issues_count": 0,
        }

    if verbose:
        rprint("[blue]Loading prompt templates...[/blue]")
    try:
        find_errors_prompt_template = load_prompt_template("find_verification_errors_LLM")
        fix_errors_prompt_template = load_prompt_template("fix_verification_errors_LLM")
        if not find_errors_prompt_template or not fix_errors_prompt_template:
            raise ValueError("One or both prompt templates could not be loaded.")
    except Exception as e:
        rprint(f"[bold red]Error loading prompt templates:[/bold red] {e}")
        return {
            "explanation": None,
            "fixed_program": program,
            "fixed_code": code,
            "total_cost": total_cost,
            "model_name": model_name,
            "verification_issues_count": verification_issues_count,
        }
    if verbose:
        rprint("[green]Prompt templates loaded successfully.[/green]")

    if verbose:
        rprint(f"\n[blue]Step 2: Running verification check (Strength: {strength}, Temp: {temperature})...[/blue]")

    verification_input_json = {
        "program": program,
        "prompt": prompt,
        "code": code,
        "output": output,
    }

    try:
        verification_response = llm_invoke(
            prompt=find_errors_prompt_template,
            input_json=verification_input_json,
            strength=strength,
            temperature=temperature,
            verbose=False,
            output_pydantic=VerificationOutput,
            time=time
        )
        total_cost += verification_response.get('cost', 0.0)
        model_name = verification_response.get('model_name', model_name)

        if verbose:
            rprint("[cyan]Verification LLM call complete.[/cyan]")
            rprint(f"  [dim]Model Used:[/dim] {verification_response.get('model_name', 'N/A')}")
            rprint(f"  [dim]Cost:[/dim] ${verification_response.get('cost', 0.0):.6f}")

    except Exception as e:
        rprint(f"[bold red]Error during verification LLM call:[/bold red] {e}")
        return {
            "explanation": None,
            "fixed_program": program,
            "fixed_code": code,
            "total_cost": total_cost,
            "model_name": model_name,
            "verification_issues_count": 0, # Reset on LLM call error
        }

    issues_found = False
    verification_result_obj = verification_response.get('result')

    if isinstance(verification_result_obj, VerificationOutput):
        # llm_invoke handles all parsing when output_pydantic is specified
        verification_issues_count = verification_result_obj.issues_count
        verification_details = verification_result_obj.details
        if verbose:
            rprint("[green]Successfully parsed structured output from verification LLM.[/green]")
            rprint("\n[blue]Verification Result (parsed):[/blue]")
            rprint(f"  Issues Count: {verification_issues_count}")
            if verification_details:
                rprint(Markdown(f"**Details:**\n{verification_details}"))
            else:
                rprint("  Details: None provided or no issues found.")

        if verification_issues_count > 0:
            if verification_details and verification_details.strip():
                issues_found = True
                if verbose:
                    rprint(f"\n[yellow]Found {verification_issues_count} potential issues. Proceeding to fix step.[/yellow]")
            else:
                rprint(f"[yellow]Warning:[/yellow] issues_count is {verification_issues_count}, but details field is empty or missing. Treating as no actionable issues found.")
                verification_issues_count = 0
        else:
            if verbose:
                rprint("\n[green]No issues found during verification based on structured output.[/green]")
    else:
        # llm_invoke should always return VerificationOutput when output_pydantic is specified
        rprint("[bold red]Error:[/bold red] Verification LLM call did not return the expected structured output.")
        rprint(f"  [dim]Expected type:[/dim] {VerificationOutput}")
        rprint(f"  [dim]Received type:[/dim] {type(verification_result_obj)}")
        content_str = str(verification_result_obj)
        rprint(f"  [dim]Received content:[/dim] {content_str[:500]}{'...' if len(content_str) > 500 else ''}")
        return {
            "explanation": None,
            "fixed_program": program,
            "fixed_code": code,
            "total_cost": total_cost,
            "model_name": model_name,
            "verification_issues_count": 0,
        }

    if issues_found and verification_details:
        if verbose:
            rprint(f"\n[blue]Step 5: Running fix generation (Strength: {strength}, Temp: {temperature})...[/blue]")

        fix_input_json = {
            "program": program,
            "prompt": prompt,
            "code": code,
            "output": output,
            "issues": verification_details,
        }

        try:
            fix_response = llm_invoke(
                prompt=fix_errors_prompt_template,
                input_json=fix_input_json,
                strength=strength,
                temperature=temperature,
                verbose=False,
                output_pydantic=FixerOutput,
                time=time
            )
            total_cost += fix_response.get('cost', 0.0)
            model_name = fix_response.get('model_name', model_name)

            if verbose:
                rprint(f"[cyan]Fix LLM call complete.[/cyan]")
                rprint(f"  [dim]Model Used:[/dim] {fix_response.get('model_name', 'N/A')}")
                rprint(f"  [dim]Cost:[/dim] ${fix_response.get('cost', 0.0):.6f}")

            fix_result_obj = fix_response.get('result')

            if isinstance(fix_result_obj, FixerOutput):
                # llm_invoke handles all parsing and unescaping via _unescape_code_newlines
                fixed_program = fix_result_obj.fixed_program
                fixed_code = fix_result_obj.fixed_code
                fix_explanation = fix_result_obj.explanation

                if verbose:
                    rprint("[green]Successfully parsed structured output for fix.[/green]")
                    rprint(Markdown(f"**Explanation from LLM:**\n{fix_explanation}"))
            else:
                # llm_invoke should always return FixerOutput when output_pydantic is specified
                rprint(f"[bold red]Error:[/bold red] Fix generation LLM call did not return the expected structured output.")
                rprint(f"  [dim]Expected type:[/dim] {FixerOutput}")
                rprint(f"  [dim]Received type:[/dim] {type(fix_result_obj)}")
                content_str = str(fix_result_obj)
                rprint(f"  [dim]Received content:[/dim] {content_str[:500]}{'...' if len(content_str) > 500 else ''}")
                fix_explanation = "[Error: Failed to parse structured output from LLM for fix explanation]"
                # fixed_program and fixed_code remain original (already initialized)

        except Exception as e:
            rprint(f"[bold red]Error during fix LLM call or processing structured output:[/bold red] {e}")
            fix_explanation = f"[Error during fix generation: {e}]"
            # fixed_program and fixed_code remain original

    if issues_found:
        final_explanation = (
            f"<verification_details>{verification_details}</verification_details>\n"
            f"<fix_explanation>{fix_explanation}</fix_explanation>"
        )
    else:
        final_explanation = None # Or "" if an empty list/None is preferred per prompt for "no issues"

    if verbose:
        rprint(f"\n[bold blue]Total Cost for fix_verification_errors run:[/bold blue] ${total_cost:.6f}")

    return {
        "explanation": final_explanation,
        "fixed_program": fixed_program,
        "fixed_code": fixed_code,
        "total_cost": total_cost,
        "model_name": model_name,
        "verification_issues_count": verification_issues_count,
    }
