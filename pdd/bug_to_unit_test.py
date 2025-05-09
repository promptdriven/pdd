from typing import Tuple, Optional
from rich import print
from rich.markdown import Markdown
from rich.console import Console
from . import EXTRACTION_STRENGTH, DEFAULT_STRENGTH
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke
from .unfinished_prompt import unfinished_prompt
from .continue_generation import continue_generation
from .postprocess import postprocess
from .preprocess import preprocess

console = Console()

def bug_to_unit_test(
    current_output: str,
    desired_output: str,
    prompt_used_to_generate_the_code: str,
    code_under_test: str,
    program_used_to_run_code_under_test: str,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    language: str = "python"
) -> Tuple[str, float, str]:
    """
    Generate a unit test from a code file with bug information.

    Args:
        current_output (str): Current output of the code
        desired_output (str): Desired output of the code
        prompt_used_to_generate_the_code (str): Original prompt used to generate the code
        code_under_test (str): Code to be tested
        program_used_to_run_code_under_test (str): Program used to run the code
        strength (float, optional): Strength of the LLM model. Must be between 0 and 1. Defaults to DEFAULT_STRENGTH.
        temperature (float, optional): Temperature of the LLM model. Defaults to 0.0.
        language (str, optional): Programming language. Defaults to "python".

    Returns:
        Tuple[str, float, str]: Generated unit test, total cost, and model name

    Raises:
        ValueError: If strength is not between 0 and 1
    """
    # Validate strength parameter
    if not 0 <= strength <= 1:
        raise ValueError("Strength parameter must be between 0 and 1")
        
    # Ensure language parameter is not None or empty
    if not language or not isinstance(language, str):
        language = "python"  # Default fallback
        console.print("[yellow]Warning: Invalid language parameter, defaulting to 'python'[/yellow]")

    total_cost = 0.0
    final_model_name = ""

    try:
        # Step 1: Load the prompt template
        prompt_template = load_prompt_template("bug_to_unit_test_LLM")
        if not prompt_template:
            raise ValueError("Failed to load prompt template")

        # Step 2: Prepare input and run through LLM
        preprocessed_prompt = preprocess(prompt_used_to_generate_the_code)
        
        input_json = {
            "prompt_that_generated_code": preprocessed_prompt,
            "current_output": current_output,
            "desired_output": desired_output,
            "code_under_test": code_under_test,
            "program_used_to_run_code_under_test": program_used_to_run_code_under_test,
            "language": language if language and isinstance(language, str) else "python"
        }

        console.print("[bold blue]Generating unit test...[/bold blue]")
        response = llm_invoke(
            prompt=prompt_template,
            input_json=input_json,
            strength=strength,
            temperature=temperature,
            verbose=True
        )

        total_cost += response['cost']
        final_model_name = response['model_name']

        # Step 3: Print markdown formatting
        console.print(Markdown(response['result']))

        # Step 4: Check if generation is complete
        last_600_chars = response['result'][-600:] if len(response['result']) > 600 else response['result']
        
        reasoning, is_finished, unfinished_cost, unfinished_model = unfinished_prompt(
            prompt_text=last_600_chars,
            strength=0.75,
            temperature=temperature,
            verbose=False
        )
        
        total_cost += unfinished_cost

        if not is_finished:
            console.print("[yellow]Generation incomplete. Continuing...[/yellow]")
            continued_output, continued_cost, continued_model = continue_generation(
                formatted_input_prompt=prompt_template,
                llm_output=response['result'],
                strength=strength,
                temperature=temperature,
                verbose=True
            )
            total_cost += continued_cost
            final_model_name = continued_model
            result = continued_output
        else:
            result = response['result']

        # Post-process the result
        # Double-check language is valid before passing to postprocess
        if not language or not isinstance(language, str):
            language = "python"  # Ensure language is valid
            console.print("[yellow]Warning: Language value became invalid during processing, defaulting to 'python'[/yellow]")
            
        final_code, postprocess_cost, postprocess_model = postprocess(
            result,
            language,
            strength=EXTRACTION_STRENGTH,
            temperature=temperature,
            verbose=True
        )
        total_cost += postprocess_cost

        # Step 5: Print total cost
        console.print(f"[bold green]Total Cost: ${total_cost:.6f}[/bold green]")

        return final_code, total_cost, final_model_name

    except Exception as e:
        console.print(f"[bold red]Error: {str(e)}[/bold red]")
        return "", 0.0, ""

def main():
    """Example usage of the bug_to_unit_test function"""
    try:
        current_output = "3"
        desired_output = "5"
        prompt = "create a function that adds two numbers in python"
        code = """
def add_numbers(a, b):
    return a + 1
        """
        program = "python"

        unit_test, cost, model = bug_to_unit_test(
            current_output=current_output,
            desired_output=desired_output,
            prompt_used_to_generate_the_code=prompt,
            code_under_test=code,
            program_used_to_run_code_under_test=program
        )

        if unit_test:
            console.print("[bold green]Generated Unit Test:[/bold green]")
            console.print(unit_test)
            console.print(f"[bold blue]Total Cost: ${cost:.6f}[/bold blue]")
            console.print(f"[bold blue]Model Used: {model}[/bold blue]")

    except Exception as e:
        console.print(f"[bold red]Error in main: {str(e)}[/bold red]")

if __name__ == "__main__":
    main()