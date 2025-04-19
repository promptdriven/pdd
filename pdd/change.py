from typing import Tuple
from rich.console import Console
from rich.markdown import Markdown
from rich.panel import Panel
from pydantic import BaseModel, Field
from .preprocess import preprocess
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke
from . import EXTRACTION_STRENGTH

console = Console()

class ExtractedPrompt(BaseModel):
    modified_prompt: str = Field(description="The extracted modified prompt")

def change(
    input_prompt: str,
    input_code: str,
    change_prompt: str,
    strength: float,
    temperature: float,
    verbose: bool = False
) -> Tuple[str, float, str]:
    """
    Change a prompt according to specified modifications.

    Args:
        input_prompt (str): The original prompt to be modified
        input_code (str): The code generated from the input prompt
        change_prompt (str): Instructions for modifying the input prompt
        strength (float): The strength parameter for the LLM model (0-1)
        temperature (float): The temperature parameter for the LLM model
        verbose (bool): Whether to print detailed information

    Returns:
        Tuple[str, float, str]: (modified prompt, total cost, model name)
    """
    try:
        # Step 1: Load prompt templates
        change_llm_prompt = load_prompt_template("change_LLM")
        extract_prompt = load_prompt_template("extract_prompt_change_LLM")

        if not all([change_llm_prompt, extract_prompt]):
            raise ValueError("Failed to load prompt templates")

        # Step 2: Preprocess the change_LLM prompt
        processed_change_llm = preprocess(change_llm_prompt, recursive=False, double_curly_brackets=False)
        processed_change_prompt = preprocess(change_prompt, recursive=False, double_curly_brackets=False)

        # Input validation
        if not all([input_prompt, input_code, change_prompt]):
            raise ValueError("Missing required input parameters")
        if not (0 <= strength <= 1):
            raise ValueError("Strength must be between 0 and 1")

        total_cost = 0.0
        final_model_name = ""

        # Step 3: Run change prompt through model
        if verbose:
            console.print(Panel("Running change prompt through LLM...", style="blue"))

        change_response = llm_invoke(
            prompt=processed_change_llm,
            input_json={
                "input_prompt": input_prompt,
                "input_code": input_code,
                "change_prompt": processed_change_prompt
            },
            strength=strength,
            temperature=temperature,
            verbose=verbose
        )

        total_cost += change_response["cost"]
        final_model_name = change_response["model_name"]

        # Step 4: Print markdown formatting if verbose
        if verbose:
            console.print(Panel("Change prompt result:", style="green"))
            console.print(Markdown(change_response["result"]))

        # Step 5: Run extract prompt
        if verbose:
            console.print(Panel("Extracting modified prompt...", style="blue"))

        extract_response = llm_invoke(
            prompt=extract_prompt,
            input_json={"llm_output": change_response["result"]},
            strength=EXTRACTION_STRENGTH,  # Fixed strength for extraction
            temperature=temperature,
            verbose=verbose,
            output_pydantic=ExtractedPrompt
        )

        total_cost += extract_response["cost"]

        # Ensure we have a valid result
        if not isinstance(extract_response["result"], ExtractedPrompt):
            raise ValueError("Failed to extract modified prompt")

        modified_prompt = extract_response["result"].modified_prompt

        # Step 6: Print extracted prompt if verbose
        if verbose:
            console.print(Panel("Extracted modified prompt:", style="green"))
            console.print(Markdown(modified_prompt))

        # Step 7: Return results
        return modified_prompt, total_cost, final_model_name

    except Exception as e:
        console.print(f"[red]Error in change function: {str(e)}[/red]")
        raise

def main():
    """Example usage of the change function"""
    try:
        # Example inputs
        input_prompt = "Write a function that adds two numbers"
        input_code = "def add(a, b):\n    return a + b"
        change_prompt = "Make the function handle negative numbers explicitly"
        
        modified_prompt, cost, model = change(
            input_prompt=input_prompt,
            input_code=input_code,
            change_prompt=change_prompt,
            strength=0.7,
            temperature=0.7,
            verbose=True
        )

        console.print("\n[bold green]Results:[/bold green]")
        console.print(f"Modified Prompt: {modified_prompt}")
        console.print(f"Total Cost: ${cost:.6f}")
        console.print(f"Model Used: {model}")

    except Exception as e:
        console.print(f"[red]Error in main: {str(e)}[/red]")

if __name__ == "__main__":
    main()