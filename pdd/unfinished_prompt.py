from typing import Tuple
from pydantic import BaseModel, Field
from rich import print as rprint
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke

class PromptAnalysis(BaseModel):
    reasoning: str = Field(description="Structured reasoning for the completeness assessment")
    is_finished: bool = Field(description="Boolean indicating whether the prompt is complete")

def unfinished_prompt(
    prompt_text: str,
    strength: float = 0.5,
    temperature: float = 0,
    verbose: bool = False
) -> Tuple[str, bool, float, str]:
    """
    Analyze whether a given prompt is complete or needs to continue.

    Args:
        prompt_text (str): The prompt text to analyze
        strength (float, optional): Strength of the LLM model. Defaults to 0.5.
        temperature (float, optional): Temperature of the LLM model. Defaults to 0.
        verbose (bool, optional): Whether to print detailed information. Defaults to False.

    Returns:
        Tuple[str, bool, float, str]: Contains:
            - reasoning: Structured reasoning for the completeness assessment
            - is_finished: Boolean indicating whether the prompt is complete
            - total_cost: Total cost of the analysis
            - model_name: Name of the LLM model used

    Raises:
        ValueError: If input parameters are invalid
        Exception: If there's an error loading the prompt template or invoking the LLM
    """
    try:
        # Input validation
        if not isinstance(prompt_text, str) or not prompt_text.strip():
            raise ValueError("Prompt text must be a non-empty string")
        
        if not 0 <= strength <= 1:
            raise ValueError("Strength must be between 0 and 1")
        
        if not 0 <= temperature <= 1:
            raise ValueError("Temperature must be between 0 and 1")

        # Step 1: Load the prompt template
        if verbose:
           rprint("[blue]Loading prompt template...[/blue]")
        
        prompt_template = load_prompt_template("unfinished_prompt_LLM")
        if not prompt_template:
            raise Exception("Failed to load prompt template")

        # Step 2: Prepare input and invoke LLM
        input_json = {"PROMPT_TEXT": prompt_text}
        
        if verbose:
            rprint("[blue]Invoking LLM model...[/blue]")
            try:
                rprint(f"Input text: {prompt_text}")
            except:
                print(f"Input text: {prompt_text}")
            rprint(f"Model strength: {strength}")
            rprint(f"Temperature: {temperature}")

        response = llm_invoke(
            prompt=prompt_template,
            input_json=input_json,
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            output_pydantic=PromptAnalysis
        )

        # Step 3: Extract and return results
        result: PromptAnalysis = response['result']
        total_cost = response['cost']
        model_name = response['model_name']

        if verbose:
           rprint("[green]Analysis complete![/green]")
           rprint(f"Reasoning: {result.reasoning}")
           rprint(f"Is finished: {result.is_finished}")
           rprint(f"Total cost: ${total_cost:.6f}")
           rprint(f"Model used: {model_name}")

        return (
            result.reasoning,
            result.is_finished,
            total_cost,
            model_name
        )

    except Exception as e:
        rprint("[red]Error in unfinished_prompt:[/red]", str(e))
        raise

# Example usage
if __name__ == "__main__":
    sample_prompt = "Write a function that"
    try:
        reasoning, is_finished, cost, model = unfinished_prompt(
            prompt_text=sample_prompt,
            verbose=True
        )
        rprint("\n[blue]Results:[/blue]")
        rprint(f"Complete? {'Yes' if is_finished else 'No'}")
        rprint(f"Reasoning: {reasoning}")
        rprint(f"Cost: ${cost:.6f}")
        rprint(f"Model: {model}")
    except Exception as e:
        rprint("[red]Error in example:[/red]", str(e))