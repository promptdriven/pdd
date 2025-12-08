from typing import Tuple
from rich.console import Console
from rich.markdown import Markdown
from pydantic import BaseModel, Field
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .llm_invoke import llm_invoke
from . import DEFAULT_TIME
class PromptUpdate(BaseModel):
    modified_prompt: str = Field(
        description="The updated prompt that will generate the modified code",
        min_length=10  # Reject empty or too-short prompts from LLM
    )

def update_prompt(
    input_prompt: str,
    input_code: str,
    modified_code: str,
    strength: float,
    temperature: float,
    verbose: bool = False,
    time: float = DEFAULT_TIME
) -> Tuple[str, float, str]:
    """
    Update a prompt based on the original and modified code.

    Args:
        input_prompt (str): The original prompt that generated the code
        input_code (str): The original generated code
        modified_code (str): The modified code
        strength (float): The strength parameter for the LLM model (0-1)
        temperature (float): The temperature parameter for the LLM model (0-1)
        verbose (bool, optional): Whether to print detailed output. Defaults to False.
        time (float, optional): The time parameter for the LLM model. Defaults to 0.25.

    Returns:
        Tuple[str, float, str]: (modified_prompt, total_cost, model_name)

    Raises:
        ValueError: If input parameters are invalid
        RuntimeError: If there's an error in LLM processing
    """
    console = Console()

    # Input validation
    is_new_prompt_generation = (input_prompt.strip() == "no prompt exists yet, create a new one")

    if not is_new_prompt_generation:
        # For updating an existing prompt, input_code must be non-empty.
        if not input_code.strip():
            raise ValueError("For updating an existing prompt, input_code must be non-empty.")

    if not (0 <= strength <= 1 and 0 <= temperature <= 1):
        raise ValueError("Strength and temperature must be between 0 and 1")

    try:
        # Step 1: Load and preprocess prompt templates
        update_prompt_template = load_prompt_template("update_prompt_LLM")
        extract_prompt_template = load_prompt_template("extract_prompt_update_LLM")

        if not update_prompt_template or not extract_prompt_template:
            raise RuntimeError("Failed to load prompt templates")

        update_prompt_processed = preprocess(update_prompt_template, False, False)
        extract_prompt_processed = preprocess(extract_prompt_template, False, False)

        # Step 2: First LLM invocation
        if verbose:
            console.print("[bold blue]Running first LLM invocation...[/bold blue]")

        first_response = llm_invoke(
            prompt=update_prompt_processed,
            input_json={
                "input_prompt": input_prompt,
                "input_code": input_code,
                "modified_code": modified_code
            },
            strength=strength,
            temperature=temperature,
            verbose=verbose,
            time=time
        )

        if not first_response or not isinstance(first_response, dict) or 'result' not in first_response:
            raise RuntimeError("First LLM invocation failed")

        # Step 3: Second LLM invocation
        if verbose:
            console.print("[bold blue]Running second LLM invocation...[/bold blue]")

        second_response = llm_invoke(
            prompt=extract_prompt_processed,
            input_json={"llm_output": first_response['result']},
            strength=0.5,
            temperature=temperature,
            output_pydantic=PromptUpdate,
            verbose=verbose,
            time=time
        )

        if not second_response or not isinstance(second_response, dict) or 'result' not in second_response:
            raise RuntimeError("Second LLM invocation failed")

        # Validate that modified_prompt is not empty or whitespace-only
        modified_prompt_text = second_response['result'].modified_prompt
        if not modified_prompt_text or not modified_prompt_text.strip():
            raise RuntimeError(
                "LLM returned an empty modified prompt. The extraction may have failed. "
                "Try running with --verbose to see the first LLM's output."
            )

        # Step 4: Print modified prompt if verbose
        if verbose:
            console.print("\n[bold green]Modified Prompt:[/bold green]")
            console.print(Markdown(second_response['result'].modified_prompt))

        # Step 5: Calculate total cost
        total_cost = first_response['cost'] + second_response['cost']

        if verbose:
            console.print(f"\n[bold yellow]Total Cost: ${total_cost:.6f}[/bold yellow]")
            console.print(f"[bold cyan]Model Used: {first_response['model_name']}[/bold cyan]")

        # Step 6: Return results
        return (
            second_response['result'].modified_prompt,
            total_cost,
            first_response['model_name']
        )

    except Exception as e:
        error_msg = f"Error in update_prompt: {str(e)}"
        console.print(f"[bold red]{error_msg}[/bold red]")
        raise RuntimeError(error_msg)