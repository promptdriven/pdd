from typing import Optional, Tuple
from pydantic import BaseModel, Field
from rich.console import Console
from rich.markdown import Markdown

from .llm_invoke import llm_invoke
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from . import DEFAULT_STRENGTH # Removed unused EXTRACTION_STRENGTH

console = Console()

# Pydantic models for structured output
class DiffAnalysis(BaseModel):
    is_big_change: bool = Field(description="Whether the change is considered significant enough to require full regeneration")
    change_description: str = Field(description="A description of the changes between the original and new prompts")
    analysis: str = Field(description="Detailed analysis of the differences and recommendation")

class CodePatchResult(BaseModel):
    patched_code: str = Field(description="The updated code with incremental patches applied")
    analysis: str = Field(description="Analysis of the patching process")
    planned_modifications: str = Field(description="Description of the modifications planned and applied")

def incremental_code_generator(
    original_prompt: str,
    new_prompt: str,
    existing_code: str,
    language: str,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time: float = 0.25,
    force_incremental: bool = False,
    verbose: bool = False,
    preprocess_prompt: bool = True
) -> Tuple[Optional[str], bool, float, str]:
    """
    Analyzes changes to a prompt and either incrementally patches existing code or suggests full regeneration.
    
    Args:
        original_prompt (str): The original prompt used to generate the existing code.
        new_prompt (str): The updated prompt that needs to be processed.
        existing_code (str): The existing code generated from the original prompt.
        language (str): The programming language of the output code (e.g., 'python', 'bash').
        strength (float): Strength parameter for the LLM model (0 to 1). Defaults to DEFAULT_STRENGTH.
        temperature (float): Temperature parameter for randomness in LLM output (0 to 1). Defaults to 0.0.
        time (float): Thinking time or reasoning effort for the LLM model (0 to 1). Defaults to 0.25.
        force_incremental (bool): Forces incremental patching even if full regeneration is suggested. Defaults to False.
        verbose (bool): If True, prints detailed information about the process. Defaults to False.
        preprocess_prompt (bool): If True, preprocesses the prompt before invocation. Defaults to True.
    
    Returns:
        Tuple[Optional[str], bool, float, str]: A tuple containing:
            - updated_code (Optional[str]): The updated code if incremental patching is applied, None if full regeneration is needed.
            - is_incremental (bool): True if incremental patching was applied, False if full regeneration is needed.
            - total_cost (float): The total cost of all LLM invocations.
            - model_name (str): The name of the LLM model used for the main operation.
    """
    # Validate inputs (moved outside the main try-except block)
    if not original_prompt or not new_prompt or not existing_code or not language:
        raise ValueError("All required inputs (original_prompt, new_prompt, existing_code, language) must be provided.")

    if not 0 <= strength <= 1 or not 0 <= temperature <= 2 or not 0 <= time <= 1:
        raise ValueError("Strength and time must be between 0 and 1. Temperature must be between 0 and 2.")

    try:
        total_cost = 0.0
        model_name = ""

        # Step 1: Load and preprocess the diff_analyzer_LLM prompt template
        diff_analyzer_template = load_prompt_template("diff_analyzer_LLM")
        if preprocess_prompt:
            diff_analyzer_template = preprocess(
                diff_analyzer_template,
                recursive=False,
                double_curly_brackets=True,
                exclude_keys=["ORIGINAL_PROMPT", "NEW_PROMPT", "EXISTING_CODE"]
            )

        if verbose:
            console.print("[bold cyan]Step 1: Loaded diff_analyzer_LLM template[/bold cyan]")

        # Step 2: Run diff_analyzer_LLM through llm_invoke
        input_json = {
            "ORIGINAL_PROMPT": original_prompt,
            "NEW_PROMPT": new_prompt,
            "EXISTING_CODE": existing_code
        }
        diff_response = llm_invoke(
            prompt=diff_analyzer_template,
            input_json=input_json,
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
            output_pydantic=DiffAnalysis
        )
        diff_result: DiffAnalysis = diff_response['result']
        total_cost += diff_response['cost']
        model_name = diff_response['model_name'] # Initial model name

        if verbose:
            console.print("[bold green]Diff Analyzer Results:[/bold green]")
            console.print(f"Is Big Change: {diff_result.is_big_change}")
            console.print(Markdown(f"**Analysis:**\n{diff_result.analysis}"))
            console.print(f"Cost so far: ${total_cost:.6f}")

        # Step 3: Determine whether to use incremental patching or full regeneration
        should_regenerate = not force_incremental and diff_result.is_big_change

        if verbose and force_incremental and diff_result.is_big_change:
            console.print("[bold yellow]Forcing incremental patching despite major change detection[/bold yellow]")

        # Step 4: Handle regeneration or incremental patching
        if should_regenerate:
            if verbose:
                console.print("[bold red]Major change detected. Recommending full regeneration.[/bold red]")
            return None, False, total_cost, model_name
        else:
            # Load and preprocess the code_patcher_LLM prompt template
            patcher_template = load_prompt_template("code_patcher_LLM")
            if preprocess_prompt:
                patcher_template = preprocess(
                    patcher_template,
                    recursive=False,
                    double_curly_brackets=True,
                    exclude_keys=["ORIGINAL_PROMPT", "NEW_PROMPT", "EXISTING_CODE", "CHANGE_DESCRIPTION"]
                )

            if verbose:
                console.print("[bold cyan]Step 4: Loaded code_patcher_LLM template for incremental patching[/bold cyan]")

            # Run code_patcher_LLM through llm_invoke
            patch_input_json = {
                "ORIGINAL_PROMPT": original_prompt,
                "NEW_PROMPT": new_prompt,
                "EXISTING_CODE": existing_code,
                "CHANGE_DESCRIPTION": diff_result.change_description
            }
            patch_response = llm_invoke(
                prompt=patcher_template,
                input_json=patch_input_json,
                strength=strength,
                temperature=temperature,
                time=time,
                verbose=verbose,
                output_pydantic=CodePatchResult
            )
            patch_result: CodePatchResult = patch_response['result']
            total_cost += patch_response['cost']
            model_name = patch_response['model_name'] # Update model_name to patcher's model

            if verbose:
                console.print("[bold green]Code Patcher Results:[/bold green]")
                console.print(Markdown(f"**Analysis:**\n{patch_result.analysis}"))
                console.print(Markdown(f"**Planned Modifications:**\n{patch_result.planned_modifications}"))
                console.print(f"Total Cost: ${total_cost:.6f}")

            return patch_result.patched_code, True, total_cost, model_name

    except Exception as e:
        # This will now catch errors from LLM calls or other unexpected runtime issues,
        # not the initial input validation ValueErrors.
        console.print(f"[bold red]Error in incremental_code_generator: {str(e)}[/bold red]")
        raise RuntimeError(f"Failed to process incremental code generation: {str(e)}")

if __name__ == "__main__":
    # Example usage for testing purposes
    try:
        original_prompt = "Write a Python function to calculate the factorial of a number."
        new_prompt = "Write a Python function to calculate the factorial of a number with input validation."
        existing_code = """
def factorial(n):
    if n == 0 or n == 1:
        return 1
    return n * factorial(n - 1)
"""
        language = "python"
        updated_code, is_incremental, total_cost, model_name = incremental_code_generator(
            original_prompt=original_prompt,
            new_prompt=new_prompt,
            existing_code=existing_code,
            language=language,
            strength=DEFAULT_STRENGTH,
            temperature=0.0,
            time=0.25,
            force_incremental=False,
            verbose=True
        )
        console.print("[bold magenta]Final Results:[/bold magenta]")
        if is_incremental:
            console.print("[bold green]Incremental Patch Applied[/bold green]")
            console.print(Markdown(f"**Updated Code:**\n```python\n{updated_code}\n```"))
        else:
            console.print("[bold red]Full Regeneration Recommended[/bold red]")
        console.print(f"Total Cost: ${total_cost:.6f}")
        console.print(f"Model Used: {model_name}")
    except Exception as e:
        console.print(f"[bold red]Test Error: {str(e)}[/bold red]")
