from typing import Tuple, Optional
from rich import print
from rich.markdown import Markdown
from rich.console import Console
from . import EXTRACTION_STRENGTH
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .llm_invoke import llm_invoke
from .unfinished_prompt import unfinished_prompt
from .continue_generation import continue_generation
from .postprocess import postprocess

console = Console()

def generate_test(
    prompt: str,
    code: str,
    strength: float,
    temperature: float,
    language: str,
    verbose: bool = False
) -> Tuple[str, float, str]:
    """
    Generate a unit test from a code file using LLM.

    Args:
        prompt (str): The prompt that generated the code file.
        code (str): The code to generate a unit test from.
        strength (float): The strength of the LLM model (0-1).
        temperature (float): The temperature of the LLM model.
        language (str): The programming language for the unit test.
        verbose (bool): Whether to print detailed information.

    Returns:
        Tuple[str, float, str]: (unit_test, total_cost, model_name)
    """
    total_cost = 0.0
    model_name = ""

    try:
        # Step 1: Load prompt template
        template = load_prompt_template("generate_test_LLM")
        if not template:
            raise ValueError("Failed to load generate_test_LLM prompt template")

        # Step 2: Preprocess template
        processed_template = preprocess(template, recursive=False, double_curly_brackets=False)
        processed_prompt = preprocess(prompt, recursive=False, double_curly_brackets=False)

        # Step 3: Run through LLM
        input_json = {
            "prompt_that_generated_code": processed_prompt,
            "code": code,
            "language": language
        }

        if verbose:
            console.print("[bold blue]Generating unit test...[/bold blue]")

        response = llm_invoke(
            prompt=processed_template,
            input_json=input_json,
            strength=strength,
            temperature=temperature,
            verbose=verbose
        )

        total_cost += response['cost']
        model_name = response['model_name']
        result = response['result']

        if verbose:
            console.print(Markdown(result))
            console.print(f"[bold green]Initial generation cost: ${total_cost:.6f}[/bold green]")

        # Step 4: Check if generation is complete
        last_600_chars = result[-600:] if len(result) > 600 else result
        reasoning, is_finished, check_cost, check_model = unfinished_prompt(
            prompt_text=last_600_chars,
            strength=strength,
            temperature=temperature,
            verbose=verbose
        )
        total_cost += check_cost

        if not is_finished:
            if verbose:
                console.print("[bold yellow]Generation incomplete. Continuing...[/bold yellow]")
            
            continued_result, continue_cost, continue_model = continue_generation(
                formatted_input_prompt=processed_template,
                llm_output=result,
                strength=strength,
                temperature=temperature,
                verbose=verbose
            )
            total_cost += continue_cost
            result = continued_result
            model_name = continue_model

        # Process the final result
        processed_result, post_cost, post_model = postprocess(
            result,
            language=language,
            strength=EXTRACTION_STRENGTH,
            temperature=temperature,
            verbose=verbose
        )
        total_cost += post_cost

        # Step 5: Print total cost if verbose
        if verbose:
            console.print(f"[bold green]Total cost: ${total_cost:.6f}[/bold green]")
            console.print(f"[bold blue]Final model used: {model_name}[/bold blue]")

        # Step 6: Return results
        return processed_result, total_cost, model_name

    except Exception as e:
        console.print(f"[bold red]Error: {str(e)}[/bold red]")
        raise


def _validate_inputs(
    prompt: str,
    code: str,
    strength: float,
    temperature: float,
    language: str
) -> None:
    """Validate input parameters."""
    if not prompt or not isinstance(prompt, str):
        raise ValueError("Prompt must be a non-empty string")
    if not code or not isinstance(code, str):
        raise ValueError("Code must be a non-empty string")
    if not isinstance(strength, float) or not 0 <= strength <= 1:
        raise ValueError("Strength must be a float between 0 and 1")
    if not isinstance(temperature, float):
        raise ValueError("Temperature must be a float")
    if not language or not isinstance(language, str):
        raise ValueError("Language must be a non-empty string")