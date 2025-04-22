import re
from typing import Dict, Any
from rich import print as rprint
from rich.markdown import Markdown
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke

def fix_verification_errors(
    program: str,
    prompt: str,
    code: str,
    output: str,
    strength: float,
    temperature: float = 0.0,
    verbose: bool = False,
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
    fixed_program = program
    fixed_code = code
    final_explanation = None

    # Check only essential inputs, allow empty output
    if not all([program, prompt, code]):
        # Keep the error print for program, prompt, code missing
        rprint("[bold red]Error:[/bold red] Missing one or more required inputs (program, prompt, code).")
        return {
            "explanation": None,
            "fixed_program": program, # Return original if possible
            "fixed_code": code,       # Return original if possible
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
            verbose=False, # Keep internal llm_invoke verbose off unless needed
        )
        total_cost += verification_response.get('cost', 0.0)
        model_name = verification_response.get('model_name', model_name)
        verification_result = verification_response.get('result', '')

        if verbose:
            rprint(f"[cyan]Verification LLM call complete.[/cyan]")
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
            "verification_issues_count": verification_issues_count,
        }

    if verbose:
        rprint("\n[blue]Verification Result:[/blue]")
        # Markdown object handles its own rendering, no extra needed here
        rprint(Markdown(verification_result))

    issues_found = False
    try:
        # Attempt to match and extract digits directly
        count_match = re.search(r"<issues_count>(\d+)</issues_count>", verification_result)
        if count_match:
            verification_issues_count = int(count_match.group(1)) # Safe due to \d+
        else:
            # Specific match failed, check if tag exists with invalid content or is missing
            generic_count_match = re.search(r"<issues_count>(.*?)</issues_count>", verification_result, re.DOTALL)
            if generic_count_match:
                # Tag found, but content is not \d+ -> Parsing Error
                rprint("[bold red]Error:[/bold red] Could not parse integer value from <issues_count> tag.")
                # Return the specific error structure for parsing errors after verification call
                return {
                    "explanation": None,
                    "fixed_program": program,
                    "fixed_code": code,
                    "total_cost": total_cost, # Cost incurred so far
                    "model_name": model_name, # Model used so far
                    "verification_issues_count": 0, # Reset count on parsing error
                }
            else:
                # Tag truly not found -> Warning
                rprint("[yellow]Warning:[/yellow] Could not find <issues_count> tag in verification result. Assuming 0 issues.")
                verification_issues_count = 0

        # Proceed to check for details tag if count > 0
        if verification_issues_count > 0:
            details_match = re.search(r"<details>(.*?)</details>", verification_result, re.DOTALL)
            if details_match:
                verification_details = details_match.group(1).strip()
                if verification_details:
                    issues_found = True
                    if verbose:
                        rprint(f"\n[yellow]Found {verification_issues_count} potential issues. Proceeding to fix step.[/yellow]")
                else:
                    # Count > 0, but details empty -> Warning
                    rprint("[yellow]Warning:[/yellow] <issues_count> is > 0, but <details> tag is empty. Treating as no issues found.")
                    verification_issues_count = 0 # Reset count
            else:
                # Count > 0, but no details tag -> Warning
                rprint("[yellow]Warning:[/yellow] <issues_count> is > 0, but could not find <details> tag. Treating as no issues found.")
                verification_issues_count = 0 # Reset count
        else:
            # verification_issues_count is 0 (either parsed as 0 or defaulted after warning)
            if verbose:
                rprint("\n[green]No issues found during verification.[/green]")

    # Removed ValueError catch as it's handled by the logic above
    except Exception as e:
        # Generic catch for other potential parsing issues
        rprint(f"[bold red]Error parsing verification result:[/bold red] {e}")
        return {
            "explanation": None,
            "fixed_program": program,
            "fixed_code": code,
            "total_cost": total_cost,
            "model_name": model_name,
            "verification_issues_count": 0, # Reset count on parsing error
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
                verbose=False, # Keep internal llm_invoke verbose off unless needed
            )
            total_cost += fix_response.get('cost', 0.0)
            model_name = fix_response.get('model_name', model_name) # Update model name to the last one used
            fix_result = fix_response.get('result', '')

            if verbose:
                rprint(f"[cyan]Fix LLM call complete.[/cyan]")
                rprint(f"  [dim]Model Used:[/dim] {fix_response.get('model_name', 'N/A')}")
                rprint(f"  [dim]Cost:[/dim] ${fix_response.get('cost', 0.0):.6f}")
                rprint("\n[blue]Fix Result:[/blue]")
                # Markdown object handles its own rendering, no extra needed here
                rprint(Markdown(fix_result))

            fixed_program_match = re.search(r"<fixed_program>(.*?)</fixed_program>", fix_result, re.DOTALL)
            fixed_code_match = re.search(r"<fixed_code>(.*?)</fixed_code>", fix_result, re.DOTALL)
            explanation_match = re.search(r"<explanation>(.*?)</explanation>", fix_result, re.DOTALL)

            if fixed_program_match:
                fixed_program = fixed_program_match.group(1).strip()
                if verbose: rprint("[green]Extracted fixed program.[/green]")
            else:
                if verbose: rprint("[yellow]Warning:[/yellow] Could not find <fixed_program> tag in fix result. Using original program.")

            if fixed_code_match:
                fixed_code = fixed_code_match.group(1).strip()
                if verbose: rprint("[green]Extracted fixed code module.[/green]")
            else:
                if verbose: rprint("[yellow]Warning:[/yellow] Could not find <fixed_code> tag in fix result. Using original code module.")

            if explanation_match:
                fix_explanation = explanation_match.group(1).strip()
                if verbose: rprint("[green]Extracted fix explanation.[/green]")
            else:
                if verbose: rprint("[yellow]Warning:[/yellow] Could not find <explanation> tag in fix result.")
                fix_explanation = "[Fix explanation not provided by LLM]"

        except Exception as e:
            rprint(f"[bold red]Error during fix LLM call or extraction:[/bold red] {e}")
            # Combine verification details with the error message if fix failed
            final_explanation = f"<error>Error during fix generation: {str(e)}</error>\n"
            if verification_details:
                fix_explanation = f"[Error during fix generation: {e}]"
            # Note: verification_issues_count should retain its value from the verification step

    if verbose:
        rprint(f"\n[bold blue]Total Cost for fix_verification_errors run:[/bold blue] ${total_cost:.6f}")

    # Construct final explanation only if issues were initially found and processed
    if verification_details:
        if fix_explanation:
             final_explanation = (
                 f"<verification_details>{verification_details}</verification_details>\n"
                 f"<fix_explanation>{fix_explanation}</fix_explanation>"
             )
        else:
             # This case might occur if fix step wasn't run due to parsing issues after verification,
             # or if fix_explanation extraction failed silently (though we added a default).
             # Let's ensure we always provide some context if details were found.
             final_explanation = (
                 f"<verification_details>{verification_details}</verification_details>\n"
                 f"<fix_explanation>[Fix explanation not available or fix step skipped]</fix_explanation>"
             )
    # If no issues were found initially (verification_details is None), final_explanation remains None

    return {
        "explanation": final_explanation,
        "fixed_program": fixed_program,
        "fixed_code": fixed_code,
        "total_cost": total_cost,
        "model_name": model_name,
        "verification_issues_count": verification_issues_count,
    }