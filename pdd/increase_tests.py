from typing import Tuple, Optional
from rich.console import Console
from . import EXTRACTION_STRENGTH, DEFAULT_TIME
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke
from .postprocess import postprocess

def increase_tests(
    existing_unit_tests: str, 
    coverage_report: str, 
    code: str, 
    prompt_that_generated_code: str,
    language: str = "python",
    strength: float = 0.5,
    temperature: float = 0.0,
    time: Optional[float] = DEFAULT_TIME,
    verbose: bool = False
) -> Tuple[str, float, str]:
    """
    Generate additional unit tests to increase code coverage.

    Args:
        existing_unit_tests (str): Current unit tests for the code
        coverage_report (str): Coverage report for the code
        code (str): Code under test
        prompt_that_generated_code (str): Original prompt used to generate the code
        language (str, optional): Programming language. Defaults to "python".
        strength (float, optional): LLM model strength. Defaults to 0.5.
        temperature (float, optional): LLM model temperature. Defaults to 0.0.
        time (Optional[float]): Time allocation for the LLM. Defaults to DEFAULT_TIME.
        verbose (bool, optional): Verbose output flag. Defaults to False.

    Returns:
        Tuple containing:
        - Increased test function (str)
        - Total cost of generation (float)
        - Model name used (str)
    """
    console = Console()

    # Validate inputs
    if not all([existing_unit_tests, coverage_report, code, prompt_that_generated_code]):
        raise ValueError("All input parameters must be non-empty strings")

    # Validate strength and temperature
    if not (0 <= strength <= 1):
        raise ValueError("Strength must be between 0 and 1")
    if not (0 <= temperature <= 1):
        raise ValueError("Temperature must be between 0 and 1")

    try:
        # Step 1: Load prompt template
        prompt_name = "increase_tests_LLM"
        prompt_template = load_prompt_template(prompt_name)
        
        # Check if prompt template was loaded successfully
        if prompt_template is None:
            raise TypeError(f"Prompt template '{prompt_name}' not found or could not be loaded")
            
        if verbose:
            console.print(f"[blue]Loaded Prompt Template:[/blue]\n{prompt_template}")

        # Step 2: Prepare input for LLM invoke
        input_json = {
            "existing_unit_tests": existing_unit_tests,
            "coverage_report": coverage_report,
            "code": code,
            "prompt_that_generated_code": prompt_that_generated_code,
            "language": language
        }

        # Invoke LLM with the prompt
        llm_response = llm_invoke(
            prompt=prompt_template,
            input_json=input_json,
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose
        )
        
        # Debug: Check LLM response
        console.print(f"[blue]DEBUG increase_tests: LLM response type: {type(llm_response)}[/blue]")
        console.print(f"[blue]DEBUG increase_tests: LLM response keys: {llm_response.keys() if isinstance(llm_response, dict) else 'Not a dict'}[/blue]")
        console.print(f"[blue]DEBUG increase_tests: LLM result type: {type(llm_response.get('result', 'No result key'))}[/blue]")
        console.print(f"[blue]DEBUG increase_tests: LLM result length: {len(llm_response['result']) if 'result' in llm_response and llm_response['result'] else 0}[/blue]")
        console.print(f"[blue]DEBUG increase_tests: LLM result preview: {repr(llm_response['result'][:300]) if 'result' in llm_response and llm_response['result'] else 'Empty or no result'}[/blue]")

        increase_test_function, total_cost, model_name = postprocess(
            llm_response['result'], 
            language, 
            EXTRACTION_STRENGTH,  # Fixed strength for extraction
            temperature,
            verbose
        )

        if verbose:
            console.print(f"[green]Generated Test Function:[/green]\n{increase_test_function}")
            console.print(f"[blue]Total Cost: ${total_cost:.6f}[/blue]")
            console.print(f"[blue]Model Used: {model_name}[/blue]")

        return increase_test_function, total_cost, model_name

    except Exception as e:
        console.print(f"[red]Error in increase_tests: {str(e)}[/red]")
        raise