from typing import Tuple, Optional
from rich.console import Console
from . import EXTRACTION_STRENGTH, DEFAULT_TIME
from .llm_invoke import llm_invoke
from .load_prompt_template import load_prompt_template
from .preprocess import preprocess
from .postprocess import postprocess

def merge_with_existing_test(
    existing_tests: str,
    new_tests: str,
    language: str,
    strength: float,
    temperature: float,
    time_budget: Optional[float] = DEFAULT_TIME,
    verbose: bool = False
) -> Tuple[str, float, str]:
    """
    Merges a new test case into an existing test file using an LLM.

    Args:
        existing_tests (str): The content of the existing test file.
        new_tests (str): The new test case to be merged.
        language (str): The programming language of the tests.
        strength (float): LLM model strength (0.0 to 1.0).
        temperature (float): LLM model temperature.
        time_budget (Optional[float]): Time allocation for the LLM. Defaults to DEFAULT_TIME.
        verbose (bool, optional): If True, enables detailed logging. Defaults to False.

    Returns:
        Tuple[str, float, str]: A tuple containing the merged test code, the cost of the operation,
                                and the name of the model used.
    """
    console = Console()

    # 1. Input Validation
    if not all([existing_tests, new_tests, language]):
        raise ValueError("existing_tests, new_tests, and language must be non-empty strings.")
    if not (0.0 <= strength <= 1.0):
        raise ValueError("Strength must be between 0.0 and 1.0.")
    if not (0.0 <= temperature <= 2.0):
        raise ValueError("Temperature must be between 0.0 and 2.0.")

    try:
        # 2. Load and preprocess the prompt template
        template = load_prompt_template("merge_tests_LLM")
        if not template:
            raise ValueError("Failed to load 'merge_tests' prompt template.")
        

        # 3. Prepare the input for the LLM
        input_json = {
            "existing_tests": existing_tests,
            "new_tests": new_tests,
            "language": language
        }

        # 4. Invoke the LLM
        if verbose:
            console.print("[blue]Invoking LLM to merge test cases...[/blue]")
        
        response = llm_invoke(
            prompt=template,
            input_json=input_json,
            strength=strength,
            temperature=temperature,
            time=time_budget,
            verbose=verbose
        )

        raw_result = response['result']
        total_cost = response['cost']
        model_name = response['model_name']

        if not raw_result or not raw_result.strip():
            raise ValueError("LLM returned an empty result during merge operation.")

        if verbose:
            console.print(f"[green]LLM invocation successful. Model: {model_name}, Cost: ${total_cost:.6f}[/green]")
            console.print("[blue]Post-processing the merged code...[/blue]")

        # 5. Post-process the result to extract clean code
        merged_code, post_cost, post_model = postprocess(
            raw_result,
            language=language,
            strength=EXTRACTION_STRENGTH,
            temperature=temperature,
            time=time_budget,
            verbose=verbose
        )
        total_cost += post_cost

        if verbose:
            console.print(f"[green]Post-processing complete. Additional cost: ${post_cost:.6f}[/green]")
            console.print(f"[bold green]Total cost for merge operation: ${total_cost:.6f}[/bold green]")

        return merged_code, total_cost, model_name

    except Exception as e:
        console.print(f"[bold red]Error in merge_with_existing_test:[/bold red] {e}")
        raise
