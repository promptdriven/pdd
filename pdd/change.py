"""
This module provides functionality to modify a prompt according to specified changes.
It takes an input prompt, input code, and change instructions to generate a modified prompt.
"""
from typing import Tuple
from rich.console import Console
from rich.markdown import Markdown
from rich.panel import Panel
from pydantic import BaseModel, Field
from .preprocess import preprocess
from .load_prompt_template import load_prompt_template
from .llm_invoke import llm_invoke
from . import EXTRACTION_STRENGTH, DEFAULT_STRENGTH, DEFAULT_TIME

console = Console()

# Delimiters for modified prompt extraction
MODIFIED_PROMPT_START = "<<<MODIFIED_PROMPT>>>"
MODIFIED_PROMPT_END = "<<<END_MODIFIED_PROMPT>>>"


def extract_between_delimiters(text: str) -> str | None:
    """
    Extract content between MODIFIED_PROMPT delimiters if present.
    Returns None if delimiters are not found.
    """
    start_idx = text.find(MODIFIED_PROMPT_START)
    end_idx = text.find(MODIFIED_PROMPT_END)

    if start_idx != -1 and end_idx != -1 and start_idx < end_idx:
        # Extract content between delimiters
        content_start = start_idx + len(MODIFIED_PROMPT_START)
        extracted = text[content_start:end_idx].strip()
        return extracted
    return None


class ExtractedPrompt(BaseModel):
    """Pydantic model for extracting the modified prompt from LLM output."""
    modified_prompt: str = Field(description="The extracted modified prompt")

def change(  # pylint: disable=too-many-arguments, too-many-locals
    input_prompt: str,
    input_code: str,
    change_prompt: str,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time: float = DEFAULT_TIME,
    budget: float = 5.0,  # pylint: disable=unused-argument
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
        time (float): The time budget for LLM calls.
        budget (float): The budget for the operation (not used, but kept for API compatibility).
        verbose (bool): Whether to print out detailed information.

    Returns:
        Tuple[str, float, str]: (modified prompt, total cost, model name)
    """
    try:
        # Step 1: Load prompt templates
        change_llm_prompt_template = load_prompt_template("change_LLM")
        extract_prompt_template = load_prompt_template("extract_prompt_change_LLM")

        if not all([change_llm_prompt_template, extract_prompt_template]):
            raise ValueError("Failed to load prompt templates")

        # Step 2: Preprocess the change_LLM prompt
        processed_change_llm_template = preprocess(change_llm_prompt_template,
                                                  recursive=False, double_curly_brackets=False)
        processed_change_prompt_content = preprocess(change_prompt,
                                                    recursive=False, double_curly_brackets=False)

        # Input validation
        if not all([input_prompt, input_code, processed_change_prompt_content]):
            raise ValueError("Missing required input parameters after preprocessing")
        if not 0 <= strength <= 1:
            raise ValueError("Strength must be between 0 and 1")

        total_cost = 0.0
        final_model_name = ""

        # Step 3: Run change prompt through model
        if verbose:
            console.print(Panel("Running change prompt through LLM...", style="blue"))

        change_response = llm_invoke(
            prompt=processed_change_llm_template,
            input_json={
                "input_prompt": input_prompt,
                "input_code": input_code,
                "change_prompt": processed_change_prompt_content
            },
            strength=strength,
            temperature=temperature,
            time=time,
            verbose=verbose
        )

        total_cost += change_response["cost"]
        final_model_name = change_response["model_name"]

        # Step 4: Print markdown formatting if verbose
        if verbose:
            console.print(Panel("Change prompt result:", style="green"))
            console.print(Markdown(change_response["result"]))

        # Step 5: Try programmatic extraction first (faster, cheaper, more reliable)
        modified_prompt = extract_between_delimiters(change_response["result"])

        if modified_prompt:
            if verbose:
                console.print(Panel(
                    "Extracted modified prompt using delimiters (no LLM needed)",
                    style="green"
                ))
        else:
            # Fall back to LLM extraction if no delimiters found
            if verbose:
                console.print(Panel(
                    "No delimiters found, falling back to LLM extraction...",
                    style="blue"
                ))

            extract_response = llm_invoke(
                prompt=extract_prompt_template,
                input_json={"llm_output": change_response["result"]},
                strength=EXTRACTION_STRENGTH,
                temperature=temperature,
                time=time,
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

    except Exception as error:
        # Conditionally print error if verbose
        if verbose:
            console.print(f"[red]Error in change function: {str(error)}[/red]")
        raise

def main():
    """Example usage of the change function"""
    try:
        # Example inputs
        input_prompt_content = "Write a function that adds two numbers"
        input_code_content = "def add(a, b):\n    return a + b"
        change_prompt_content = "Make the function handle negative numbers explicitly"

        modified_prompt, cost, model = change(
            input_prompt=input_prompt_content,
            input_code=input_code_content,
            change_prompt=change_prompt_content,
            strength=0.7,
            temperature=0.7,
            time=DEFAULT_TIME,
            budget=10.0,
            verbose=True
        )

        console.print("\n[bold green]Results:[/bold green]")
        console.print(f"Modified Prompt: {modified_prompt}")
        console.print(f"Total Cost: ${cost:.6f}")
        console.print(f"Model Used: {model}")

    except Exception as error:  # pylint: disable=broad-except
        console.print(f"[red]Error in main: {str(error)}[/red]")

if __name__ == "__main__":
    main()
