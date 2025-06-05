from typing import List, Tuple
from pydantic import BaseModel, Field
from rich import print as rprint
from rich.markdown import Markdown
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke
from . import EXTRACTION_STRENGTH, DEFAULT_STRENGTH, DEFAULT_TIME

class ConflictChange(BaseModel):
    prompt_name: str = Field(description="Name of the prompt that needs to be changed")
    change_instructions: str = Field(description="Detailed instructions on how to change the prompt")

class ConflictResponse(BaseModel):
    changes_list: List[ConflictChange] = Field(description="List of changes needed to resolve conflicts")

def conflicts_in_prompts(
    prompt1: str,
    prompt2: str,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0,
    time: float = DEFAULT_TIME,
    verbose: bool = False
) -> Tuple[List[dict], float, str]:
    """
    Analyze two prompts for conflicts and suggest resolutions.

    Args:
        prompt1 (str): First prompt to compare
        prompt2 (str): Second prompt to compare
        strength (float): Model strength (0-1)
        temperature (float): Model temperature (0-1)
        time (float): Time budget for LLM calls.
        verbose (bool): Whether to print detailed information

    Returns:
        Tuple[List[dict], float, str]: (changes list, total cost, model name)
    """
    # Input validation - let these raise ValueError directly
    if not prompt1 or not prompt2:
        raise ValueError("Both prompts must be provided")
    if not (0 <= strength <= 1):
        raise ValueError("Strength must be between 0 and 1")
    if not (0 <= temperature <= 1):
        raise ValueError("Temperature must be between 0 and 1")

    total_cost = 0.0
    model_name = ""

    try:
        # Step 1: Load prompt templates
        conflict_prompt = load_prompt_template("conflict_LLM")
        extract_prompt = load_prompt_template("extract_conflict_LLM")

        if not conflict_prompt or not extract_prompt:
            raise ValueError("Failed to load prompt templates")

        # Step 2: First LLM call to analyze conflicts
        input_json = {
            "PROMPT1": prompt1,
            "PROMPT2": prompt2
        }

        if verbose:
            rprint("[blue]Analyzing prompts for conflicts...[/blue]")

        conflict_response = llm_invoke(
            prompt=conflict_prompt,
            input_json=input_json,
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose
        )

        total_cost += conflict_response['cost']
        model_name = conflict_response['model_name']

        if verbose:
            rprint(Markdown(conflict_response['result']))

        # Step 3: Second LLM call to extract structured conflicts
        extract_input = {
            "llm_output": conflict_response['result']
        }

        if verbose:
            rprint("[blue]Extracting structured conflict information...[/blue]")

        extract_response = llm_invoke(
            prompt=extract_prompt,
            input_json=extract_input,
            strength=EXTRACTION_STRENGTH,
            temperature=temperature,
            time=time,
            output_pydantic=ConflictResponse,
            verbose=verbose
        )

        total_cost += extract_response['cost']
        
        # Get the changes list from the Pydantic model
        changes_list = [
            change.dict() 
            for change in extract_response['result'].changes_list
        ]

        # Step 4: Return results
        return changes_list, total_cost, model_name

    except Exception as e:
        error_msg = f"Error in conflicts_in_prompts: {str(e)}"
        if verbose:
            rprint(f"[red]{error_msg}[/red]")
        if isinstance(e, ValueError):
            raise e
        raise RuntimeError(error_msg)

def main():
    """
    Example usage of the conflicts_in_prompts function.
    """
    # Example prompts
    prompt1 = "Write a formal business email in a serious tone."
    prompt2 = "Write a casual, funny email with jokes."

    try:
        changes_list, total_cost, model_name = conflicts_in_prompts(
            prompt1=prompt1,
            prompt2=prompt2,
            strength=0.7,
            temperature=0,
            time=DEFAULT_TIME,
            verbose=True
        )

        rprint("\n[green]Results:[/green]")
        rprint(f"[blue]Model Used:[/blue] {model_name}")
        rprint(f"[blue]Total Cost:[/blue] ${total_cost:.6f}")
        
        rprint("\n[blue]Suggested Changes:[/blue]")
        for change in changes_list:
            rprint(f"[yellow]Prompt:[/yellow] {change['prompt_name']}")
            rprint(f"[yellow]Instructions:[/yellow] {change['change_instructions']}\n")

    except Exception as e:
        rprint(f"[red]Error in main: {str(e)}[/red]")

if __name__ == "__main__":
    main()