from typing import Tuple
from pydantic import BaseModel, Field
from rich.console import Console
from rich.markdown import Markdown

from . import EXTRACTION_STRENGTH, DEFAULT_STRENGTH
from .preprocess import preprocess
from .postprocess import postprocess
from .llm_invoke import llm_invoke
from .load_prompt_template import load_prompt_template
from .code_generator import code_generator

console = Console()

class DiffAnalysis(BaseModel):
    is_big_change: bool = Field(description="Whether the change is considered significant enough to warrant full regeneration")
    change_description: str = Field(description="A description of the changes between the original and new prompts")
    analysis: str = Field(description="Detailed analysis of the differences and recommendation")

class PatchResult(BaseModel):
    patched_code: str = Field(description="The updated code after applying the patch")
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
) -> Tuple[str, bool, float, str]:
    """
    Analyzes changes to a prompt and either incrementally patches existing code or regenerates it from scratch.
    
    Args:
        original_prompt (str): The original prompt used to generate the existing code.
        new_prompt (str): The updated prompt that needs to be processed.
        existing_code (str): The existing code generated from the original prompt.
        language (str): The programming language of the output code (e.g., 'python', 'bash').
        strength (float): Strength parameter for the LLM model (0 to 1). Defaults to DEFAULT_STRENGTH.
        temperature (float): Temperature parameter for randomness in LLM output (0 to 1). Defaults to 0.0.
        time (float): Thinking time or reasoning effort for the LLM model (0 to 1). Defaults to 0.25.
        force_incremental (bool): Forces incremental patching even if full regeneration is suggested. Defaults to False.
        verbose (bool): Whether to print detailed information about the process. Defaults to False.
        preprocess_prompt (bool): Whether to preprocess the prompt. Defaults to True.
    
    Returns:
        Tuple[str, bool, float, str]: A tuple containing:
            - updated_code (str): The updated runnable code.
            - is_incremental (bool): Whether the update was incremental (True) or full regeneration (False).
            - total_cost (float): Total cost of all LLM invocations.
            - model_name (str): Name of the selected LLM model for the main operation.
    """
    try:
        # Validate inputs
        if not original_prompt or not new_prompt or not existing_code or not language:
            raise ValueError("All required inputs (original_prompt, new_prompt, existing_code, language) must be provided.")

        if not 0 <= strength <= 1 or not 0 <= temperature <= 1 or not 0 <= time <= 1:
            raise ValueError("Strength, temperature, and time must be between 0 and 1.")

        total_cost = 0.0
        main_model_name = ""

        # Step 1: Load and preprocess the diff_analyzer_LLM prompt template
        diff_prompt_template = load_prompt_template("diff_analyzer_LLM")
        if not diff_prompt_template:
            raise ValueError("Failed to load diff_analyzer_LLM prompt template.")
        diff_prompt = preprocess(
            diff_prompt_template,
            recursive=False,
            double_curly_brackets=True,
            exclude_keys=["ORIGINAL_PROMPT", "NEW_PROMPT", "EXISTING_CODE"]
        )

        # Step 2: Run diff_analyzer_LLM through llm_invoke
        diff_input_json = {
            "ORIGINAL_PROMPT": original_prompt,
            "NEW_PROMPT": new_prompt,
            "EXISTING_CODE": existing_code
        }
        diff_response = llm_invoke(
            prompt=diff_prompt,
            input_json=diff_input_json,
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose,
            output_pydantic=DiffAnalysis
        )
        diff_result: DiffAnalysis = diff_response['result']
        total_cost += diff_response['cost']
        main_model_name = diff_response['model_name']

        if verbose:
            console.print("[bold green]Diff Analysis:[/bold green]")
            console.print(Markdown(f"**Change Description:** {diff_result.change_description}"))
            console.print(Markdown(f"**Analysis:** {diff_result.analysis}"))
            console.print(f"[bold blue]Is Big Change: {diff_result.is_big_change}[/bold blue]")

        # Step 3: Determine whether to use incremental patching or full regeneration
        should_regenerate = not force_incremental and diff_result.is_big_change
        if verbose and force_incremental and diff_result.is_big_change:
            console.print("[bold yellow]Forcing incremental patching despite significant changes detected.[/bold yellow]")

        # Step 4: Based on should_regenerate decision
        updated_code = ""
        is_incremental = not should_regenerate

        if should_regenerate:
            # Full regeneration using code_generator
            if verbose:
                console.print("[bold cyan]Regenerating code from scratch due to significant changes.[/bold cyan]")
            runnable_code, gen_cost, gen_model_name = code_generator(
                prompt=new_prompt,
                language=language,
                strength=strength,
                temperature=temperature,
                time=time,
                verbose=verbose,
                preprocess_prompt=preprocess_prompt
            )
            total_cost += gen_cost
            updated_code = runnable_code
            main_model_name = gen_model_name if not main_model_name else main_model_name
        else:
            # Incremental patching using code_patcher_LLM
            if verbose:
                console.print("[bold cyan]Applying incremental patch to existing code.[/bold cyan]")
            patch_prompt_template = load_prompt_template("code_patcher_LLM")
            if not patch_prompt_template:
                raise ValueError("Failed to load code_patcher_LLM prompt template.")
            patch_prompt = preprocess(
                patch_prompt_template,
                recursive=False,
                double_curly_brackets=True,
                exclude_keys=["ORIGINAL_PROMPT", "NEW_PROMPT", "EXISTING_CODE", "CHANGE_DESCRIPTION"]
            )

            patch_input_json = {
                "ORIGINAL_PROMPT": original_prompt,
                "NEW_PROMPT": new_prompt,
                "EXISTING_CODE": existing_code,
                "CHANGE_DESCRIPTION": diff_result.change_description
            }
            patch_response = llm_invoke(
                prompt=patch_prompt,
                input_json=patch_input_json,
                strength=strength,
                temperature=temperature,
                time=time,
                verbose=verbose,
                output_pydantic=PatchResult
            )
            patch_result: PatchResult = patch_response['result']
            total_cost += patch_response['cost']
            main_model_name = patch_response['model_name'] if not main_model_name else main_model_name

            if verbose:
                console.print("[bold green]Patch Analysis:[/bold green]")
                console.print(Markdown(f"**Analysis:** {patch_result.analysis}"))
                console.print(Markdown(f"**Planned Modifications:** {patch_result.planned_modifications}"))

            updated_code = patch_result.patched_code

        # Step 5: Return the results
        return updated_code, is_incremental, total_cost, main_model_name

    except Exception as e:
        console.print(f"[bold red]Error in incremental_code_generator: {str(e)}[/bold red]")
        raise