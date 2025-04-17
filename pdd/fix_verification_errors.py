import os
import re
import tempfile
import traceback
from typing import Dict, Any, Tuple, Optional, List

from pydantic import BaseModel, Field
from rich import print
from rich.markdown import Markdown

# Use relative imports for internal modules within the package
try:
    from .load_prompt_template import load_prompt_template
    from .llm_invoke import llm_invoke
    # Assuming edit_file provides run_edit_in_subprocess
    from .edit_file import run_edit_in_subprocess
except ImportError:
    # Handle cases where the script might be run directly or package structure is different
    # This is less ideal for package structure but provides fallback for testing
    print("[yellow]Warning:[/yellow] Could not perform relative imports. Trying absolute imports.")
    from load_prompt_template import load_prompt_template
    from llm_invoke import llm_invoke
    from edit_file import run_edit_in_subprocess

# Define Pydantic model for structured output from the fixing LLM call
class VerificationFixOutput(BaseModel):
    """Structure for the output of the fix_verification_errors_LLM."""
    explanation: List[str] = Field(
        description="List of issues found and explanations/fixes applied. Empty list if no changes were made."
    )
    edit_instructions_program: str = Field(
        description="Natural language instructions for editing the program file. Empty string if no changes needed."
    )
    edit_instructions_code: str = Field(
        description="Natural language instructions for editing the code module file. Empty string if no changes needed."
    )

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
    Fixes issues in a code module identified during verification using LLMs.

    Args:
        program: The program code that was running the code module.
        prompt: The prompt that generated the code module.
        code: The code module to be fixed.
        output: The output logs from the program run containing verification details.
        strength: The strength of the LLM model to use (0 to 1).
        temperature: The temperature for the LLM model (default 0.0).
        verbose: Whether to print detailed execution information (default False).

    Returns:
        A dictionary containing:
        'explanation': List of issues found and their explanations (if any).
        'fixed_program': The fixed program code (or original if no changes/errors).
        'fixed_code': The fixed code module (or original if no changes/errors).
        'total_cost': The total cost of the LLM calls.
        'model_name': The name of the LLM model used for fixing (or identification if no fix needed).
    """
    total_cost = 0.0
    model_name_identify = None
    model_name_fix = None
    explanation: List[str] = []
    fixed_program = program # Default to original
    fixed_code = code       # Default to original
    issues_details = ""
    issues_found = False

    # --- Input Validation ---
    if not all([program, prompt, code, output]):
        raise ValueError("Missing one or more required string inputs: 'program', 'prompt', 'code', 'output'.")
    if not (0 <= strength <= 1):
        raise ValueError("'strength' must be between 0 and 1.")

    try:
        # --- Step 1: Load Prompt Templates ---
        if verbose:
            print("[cyan]Step 1: Loading prompt templates...[/cyan]")
        find_issues_prompt_template = load_prompt_template("find_verification_errors_LLM")
        fix_issues_prompt_template = load_prompt_template("fix_verification_errors_LLM")
        if not find_issues_prompt_template or not fix_issues_prompt_template:
            raise FileNotFoundError("Could not load required prompt templates.")
        if verbose:
            print("[green]Prompt templates loaded successfully.[/green]")

        # --- Step 2: Identify Issues (First LLM Call) ---
        if verbose:
            print(f"\n[cyan]Step 2: Running 'find_verification_errors_LLM' (Strength: {strength}, Temp: {temperature})...[/cyan]")

        identify_input_json = {
            "program": program,
            "prompt": prompt,
            "code": code,
            "output": output,
        }

        identify_response = llm_invoke(
            prompt=find_issues_prompt_template,
            input_json=identify_input_json,
            strength=strength,
            temperature=temperature,
            verbose=verbose  # Pass verbose to llm_invoke for its internal printing
        )
        total_cost += identify_response.get('cost', 0.0)
        model_name_identify = identify_response.get('model_name', 'unknown')
        verification_result = identify_response.get('result', '')

        if not verification_result:
             raise ValueError("LLM invocation for finding issues returned an empty result.")

        # --- Step 3: Verbose Output (First LLM Call Result) ---
        if verbose:
            print("\n[blue]Verification Result (Markdown):[/blue]")
            print(Markdown(verification_result))
            # llm_invoke already prints cost/tokens if verbose is True

        # --- Step 4: Analyze Verification Result ---
        if verbose:
            print("\n[cyan]Step 4: Analyzing verification result...[/cyan]")

        # Extract <issues_found> tag
        issues_found_match = re.search(r"<issues_found>(.*?)</issues_found>", verification_result, re.IGNORECASE | re.DOTALL)
        if issues_found_match:
            issues_found_val = issues_found_match.group(1).strip().lower()
            if issues_found_val == "true":
                issues_found = True
                if verbose:
                    print("[yellow]Issues found based on verification output.[/yellow]")
                # Extract <details> tag only if issues were found
                details_match = re.search(r"<details>(.*?)</details>", verification_result, re.IGNORECASE | re.DOTALL)
                if details_match:
                    issues_details = details_match.group(1).strip()
                    if verbose:
                        print("[blue]Extracted Issue Details:[/blue]")
                        print(f"[dim]{issues_details}[/dim]")
                else:
                    if verbose:
                        print("[yellow]Warning:[/yellow] <issues_found> was true, but <details> tag was not found in the result.")
                    # Proceed without details, the next LLM might still work or fail gracefully
                    issues_details = "Issues were indicated, but details could not be extracted."
            elif issues_found_val == "false":
                issues_found = False
                if verbose:
                    print("[green]No issues found based on verification output.[/green]")
                explanation = ["No issues found during verification."]
                # Return early as per Step 4b
                return {
                    "explanation": explanation,
                    "fixed_program": fixed_program, # Original program
                    "fixed_code": fixed_code,       # Original code
                    "total_cost": total_cost,
                    "model_name": model_name_identify,
                }
            else:
                if verbose:
                    print(f"[yellow]Warning:[/yellow] Unexpected value in <issues_found> tag: '{issues_found_val}'. Assuming no issues found.")
                issues_found = False
                explanation = [f"Could not determine if issues were found (unexpected tag value: {issues_found_val}). Assuming no issues."]

        else:
            if verbose:
                print("[yellow]Warning:[/yellow] <issues_found> tag not found in the verification result. Assuming no issues found.")
            issues_found = False
            explanation = ["Could not determine if issues were found (<issues_found> tag missing). Assuming no issues."]
            # Optionally return early here too, or proceed cautiously
            return {
                "explanation": explanation,
                "fixed_program": fixed_program, # Original program
                "fixed_code": fixed_code,       # Original code
                "total_cost": total_cost,
                "model_name": model_name_identify,
            }


        # --- Step 5: Generate Fixes (Second LLM Call - Conditional) ---
        if issues_found:
            if verbose:
                print(f"\n[cyan]Step 5: Running 'fix_verification_errors_LLM' to generate fixes (Strength: {strength}, Temp: {temperature})...[/cyan]")

            fix_input_json = {
                "program": program,
                "prompt": prompt,
                "code": code,
                "output": output,
                "issues": issues_details, # Pass the extracted details
            }

            # We expect structured output (Pydantic model) for the fix
            fix_response = llm_invoke(
                prompt=fix_issues_prompt_template,
                input_json=fix_input_json,
                strength=strength, # Use the same strength as identification, per prompt interpretation
                temperature=temperature,
                verbose=verbose, # Pass verbose to llm_invoke
                output_pydantic=VerificationFixOutput
            )
            total_cost += fix_response.get('cost', 0.0)
            model_name_fix = fix_response.get('model_name', model_name_identify) # Use fix model name if available

            fix_result_data: Optional[VerificationFixOutput] = fix_response.get('result')

            if not fix_result_data or not isinstance(fix_result_data, VerificationFixOutput):
                 raise ValueError("LLM invocation for fixing issues did not return the expected structured output.")

            # --- Step 6: Extract Fixes (Instructions) ---
            if verbose:
                print("\n[cyan]Step 6: Extracting fix instructions from LLM result...[/cyan]")

            explanation = fix_result_data.explanation
            edit_instructions_program = fix_result_data.edit_instructions_program
            edit_instructions_code = fix_result_data.edit_instructions_code

            if verbose:
                print("[blue]Extracted Explanation:[/blue]")
                for line in explanation:
                    print(f"- {line}")
                print("[blue]Extracted Program Edit Instructions:[/blue]")
                print(f"[dim]{edit_instructions_program or 'None'}[/dim]")
                print("[blue]Extracted Code Module Edit Instructions:[/blue]")
                print(f"[dim]{edit_instructions_code or 'None'}[/dim]")


            # --- Step 8: Apply Edits using edit_file ---
            if verbose:
                print("\n[cyan]Step 8: Applying edits using edit_file...[/cyan]")

            # Create temporary files to hold the original content
            temp_files_to_clean = []
            edit_errors = []

            try:
                # Edit Program
                if edit_instructions_program:
                    with tempfile.NamedTemporaryFile(mode='w+', delete=False, suffix=".py") as temp_prog_file:
                        temp_prog_file.write(program)
                        temp_prog_file.flush()
                        temp_prog_path = temp_prog_file.name
                        temp_files_to_clean.append(temp_prog_path)

                    if verbose:
                        print(f"Attempting to edit program file: {temp_prog_path}")
                    prog_success, prog_error_msg = run_edit_in_subprocess(
                        file_path=temp_prog_path,
                        edit_instructions=edit_instructions_program
                    )
                    if prog_success:
                        if verbose:
                            print("[green]Program edit successful.[/green]")
                        with open(temp_prog_path, 'r') as f:
                            fixed_program = f.read()
                    else:
                        error_msg = f"Failed to apply edits to program: {prog_error_msg or 'Unknown error'}"
                        if verbose:
                            print(f"[red]Error:[/red] {error_msg}")
                        edit_errors.append(error_msg)
                        # Keep original program content if edit failed
                        fixed_program = program
                else:
                     if verbose:
                        print("[yellow]No edit instructions provided for the program.[/yellow]")

                # Edit Code Module
                if edit_instructions_code:
                    with tempfile.NamedTemporaryFile(mode='w+', delete=False, suffix=".py") as temp_code_file:
                        temp_code_file.write(code)
                        temp_code_file.flush()
                        temp_code_path = temp_code_file.name
                        temp_files_to_clean.append(temp_code_path)

                    if verbose:
                        print(f"Attempting to edit code module file: {temp_code_path}")
                    code_success, code_error_msg = run_edit_in_subprocess(
                        file_path=temp_code_path,
                        edit_instructions=edit_instructions_code
                    )
                    if code_success:
                        if verbose:
                            print("[green]Code module edit successful.[/green]")
                        with open(temp_code_path, 'r') as f:
                            fixed_code = f.read()
                    else:
                        error_msg = f"Failed to apply edits to code module: {code_error_msg or 'Unknown error'}"
                        if verbose:
                            print(f"[red]Error:[/red] {error_msg}")
                        edit_errors.append(error_msg)
                        # Keep original code content if edit failed
                        fixed_code = code
                else:
                     if verbose:
                        print("[yellow]No edit instructions provided for the code module.[/yellow]")

            finally:
                # Clean up temporary files
                for temp_path in temp_files_to_clean:
                    try:
                        os.remove(temp_path)
                        if verbose:
                            print(f"Cleaned up temporary file: {temp_path}")
                    except OSError as e:
                        if verbose:
                            print(f"[yellow]Warning:[/yellow] Could not remove temporary file {temp_path}: {e}")

            # Append any edit errors to the explanation
            if edit_errors:
                explanation.append("--- Edit Errors ---")
                explanation.extend(edit_errors)

        # If no issues were found initially, steps 5, 6, 8 were skipped.
        # explanation, fixed_program, fixed_code retain their initial values.

    except FileNotFoundError as e:
        print(f"[bold red]Error:[/bold red] Prompt template file not found: {e}")
        raise
    except ValueError as e:
        print(f"[bold red]Error:[/bold red] Input validation or LLM result processing error: {e}")
        raise
    except ImportError as e:
         print(f"[bold red]Error:[/bold red] Failed to import internal modules: {e}")
         print("Please ensure the package structure is correct and dependencies are installed.")
         raise
    except Exception as e:
        print(f"[bold red]An unexpected error occurred:[/bold red] {e}")
        print(traceback.format_exc())
        # Return potentially partial results or raise
        explanation.append(f"An unexpected error occurred during processing: {e}")
        # Depending on where the error occurred, fixed_program/code might be original or partially updated
        # Returning original state is safer if unsure
        return {
            "explanation": explanation,
            "fixed_program": program,
            "fixed_code": code,
            "total_cost": total_cost,
            "model_name": model_name_fix or model_name_identify or "unknown",
        }


    # --- Step 7: Verbose Output (Total Cost) ---
    if verbose:
        print(f"\n[cyan]Step 7: Calculation Complete.[/cyan]")
        print(f"Total Cost: ${total_cost:.6f}")

    # --- Step 9: Return Results ---
    final_model_name = model_name_fix or model_name_identify # Prefer fix model name if fix ran

    return {
        "explanation": explanation,
        "fixed_program": fixed_program,
        "fixed_code": fixed_code,
        "total_cost": total_cost,
        "model_name": final_model_name,
    }